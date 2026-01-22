package lens

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const sendLensPointStateMessageFunc = "sendLensPointStateMessage"

const testGoMod = `module testmod

go 1.21
`

func countFunctionCalls(t *testing.T, src []byte, funcName string) int {
	t.Helper()

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, 0)
	require.NoError(t, err)

	var count int
	ast.Inspect(file, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == funcName {
			count++
		}
		return true
	})
	return count
}

func TestDetectPackageName(t *testing.T) {
	t.Parallel()

	t.Run("single_package", func(t *testing.T) {
		dir := t.TempDir()
		require.NoError(t, os.WriteFile(filepath.Join(dir, "f.go"), []byte("package foo\n"), 0o644))
		name, err := detectPackageName(dir)
		require.NoError(t, err)
		assert.Equal(t, "foo", name)
	})

	t.Run("mixed_packages", func(t *testing.T) {
		dir := t.TempDir()
		require.NoError(t, os.WriteFile(filepath.Join(dir, "a.go"), []byte("package a\n"), 0o644))
		require.NoError(t, os.WriteFile(filepath.Join(dir, "b.go"), []byte("package b\n"), 0o644))
		_, err := detectPackageName(dir)
		assert.Error(t, err)
	})

	t.Run("tests_only", func(t *testing.T) {
		dir := t.TempDir()
		require.NoError(t, os.WriteFile(filepath.Join(dir, "a_test.go"), []byte("package foo\n"), 0o644))
		_, err := detectPackageName(dir)
		assert.Error(t, err)
	})
}

func TestUpdateConstLiterals(t *testing.T) {
	t.Parallel()

	src := `package p
const (
    a = 1
    b, c = 2, 3
    d
)`
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "", src, 0)
	require.NoError(t, err)

	updateConstLiterals(f, map[string]string{"a": "10", "c": "30", "d": "40"})

	// check a
	decl := f.Decls[0].(*ast.GenDecl)
	specA := decl.Specs[0].(*ast.ValueSpec)
	assert.Equal(t, "10", specA.Values[0].(*ast.BasicLit).Value)

	// check b,c
	specBC := decl.Specs[1].(*ast.ValueSpec)
	assert.Equal(t, "2", specBC.Values[0].(*ast.BasicLit).Value)
	assert.Equal(t, "30", specBC.Values[1].(*ast.BasicLit).Value)

	// check d (no value originally)
	specD := decl.Specs[2].(*ast.ValueSpec)
	require.Len(t, specD.Values, 1)
	assert.Equal(t, "40", specD.Values[0].(*ast.BasicLit).Value)
}

func TestIsRecursiveCall(t *testing.T) {
	t.Parallel()

	identCall := &ast.CallExpr{Fun: ast.NewIdent("Foo")}
	assert.True(t, isRecursiveCall(identCall, "Foo"))
	assert.False(t, isRecursiveCall(identCall, "Bar"))

	selCall := &ast.CallExpr{Fun: &ast.SelectorExpr{X: ast.NewIdent("r"), Sel: ast.NewIdent("Foo")}}
	assert.True(t, isRecursiveCall(selCall, "Foo"))
	assert.False(t, isRecursiveCall(selCall, "Other"))

	assert.False(t, isRecursiveCall(ast.NewIdent("Foo"), "Foo"))
}

func TestCloneExprNoPos(t *testing.T) {
	t.Parallel()

	t.Run("expr", func(t *testing.T) {
		var buf bytes.Buffer
		expr, err := parser.ParseExpr("a + b*c")
		require.NoError(t, err)

		clone, err := cloneExprNoPos(&buf, expr)
		require.NoError(t, err)

		cb := clone.(*ast.BinaryExpr)
		cb.Op = token.SUB

		ob := expr.(*ast.BinaryExpr)
		assert.Equal(t, token.ADD, ob.Op)
		assert.NotSame(t, expr, clone)
		assert.NotSame(t, ob.X, cb.X)
	})

	t.Run("composite", func(t *testing.T) {
		var buf bytes.Buffer
		expr, err := parser.ParseExpr("&My{X:1, Y:z}")
		require.NoError(t, err)

		clone, err := cloneExprNoPos(&buf, expr)
		require.NoError(t, err)
		assert.NotSame(t, expr, clone)
	})

	t.Run("call", func(t *testing.T) {
		var buf bytes.Buffer
		expr, err := parser.ParseExpr("pkg.F(x.Y, []int{1}, map[string]int{\"a\":1})")
		require.NoError(t, err)

		clone, err := cloneExprNoPos(&buf, expr)
		require.NoError(t, err)
		assert.NotSame(t, expr, clone)
	})
}

func TestInsertFuncLines(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name                    string
		src                     string
		triggerOnSubstring      string
		triggerAllCodeLines     bool
		insertText              string
		keepGoingAfterInsertion bool
		expected                string
	}{
		{
			name: "basic",
			src: `package main

func Foo() {
    a := 1
    _ = a
}
`,
			triggerOnSubstring:      "a :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    // inserted
    a := 1
    _ = a
}
`,
		},
		{
			name: "comments",
			src: `package main

func Foo() {
    // comment
    a := 1
}
`,
			triggerOnSubstring:      "a :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    // comment
    // inserted
    a := 1
}
`,
		},
		{
			name: "trailing comment",
			src: `package main

func Foo() {
    a := 1 // trailing
}
`,
			triggerOnSubstring:      "a :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    // inserted
    a := 1 // trailing
}
`,
		},
		{
			name: "multi-line string",
			src: `package main

func Foo() {
    s := ` + "`hello\nworld`" + `
    a := 2
}
`,
			triggerOnSubstring:      "a :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    s := ` + "`hello\nworld`" + `
    // inserted
    a := 2
}
`,
		},
		{
			name: "blank lines",
			src: `package main

func Foo() {
    
    a := 3

}
`,
			triggerOnSubstring:      "a :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    
    // inserted
    a := 3

}
`,
		},
		{
			name: "stop early",
			src: `package main

func Foo() {
    a := 1
    b := 2
    c := 3
}
`,
			triggerOnSubstring:      ":=",
			insertText:              "// X",
			keepGoingAfterInsertion: false,
			expected: `package main

func Foo() {
    // X
    a := 1
    b := 2
    c := 3
}
`,
		},
		{
			name: "all code",
			src: `package main

func Foo() {
    x := 1
    y := 2
}
`,
			triggerAllCodeLines:     true,
			insertText:              "// everywhere",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    // everywhere
    x := 1
    // everywhere
    y := 2
}
`,
		},
		{
			name: "struct",
			src: `package main

func Foo() {
    person := Person{
        Name: "Alice",
        Age:  30,
    }
    foo(person)
}
`,
			triggerOnSubstring:      "person :=",
			insertText:              "// inserted",
			keepGoingAfterInsertion: true,
			expected: `package main

func Foo() {
    // inserted
    person := Person{
        Name: "Alice",
        Age:  30,
    }
    foo(person)
}
`,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			file := filepath.Join(dir, "main.go")
			require.NoError(t, os.WriteFile(file, []byte(tc.src), 0644))

			mod := &ASTModifier{}
			err := mod.InsertFuncLines(&Function{
				FilePath:      file,
				PackageName:   mainPkg,
				FunctionIdent: "main:Foo",
				FunctionName:  "Foo",
			}, func(i int, line string) (string, bool) {
				if tc.triggerAllCodeLines {
					return tc.insertText, true
				} else if tc.triggerOnSubstring != "" && strings.Contains(line, tc.triggerOnSubstring) {
					return tc.insertText, tc.keepGoingAfterInsertion
				}
				return "", true
			})
			require.NoError(t, err)
			require.NoError(t, mod.CommitFile(file))

			data, err := os.ReadFile(file)
			require.NoError(t, err)
			assert.Equal(t, tc.expected, string(data))

			_, err = os.Stat(file + ".bkp")
			require.NoError(t, err)
		})
	}
}

func TestVisibleDeclsBefore(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name string
		src  string
		want []string
	}{
		{
			name: "params and results",
			src: `package foo
func Foo(a, b int) (r int) {
    r = a + b
    return r
}`,
			want: []string{"a", "b", "r"},
		},
		{
			name: "var and short assign",
			src: `package foo
func Foo() int {
    var x int
    y := 2
    return x + y
}`,
			want: []string{"x", "y"},
		},
		{
			name: "range loop",
			src: `package foo
func Foo() int {
    xs := []int{1,2}
    for i, v := range xs {
        _ = i
        return v
    }
    return 0
}`,
			want: []string{"xs", "i", "v"},
		},
		{
			name: "after retPos not visible",
			src: `package foo
func Foo() int {
    x := 1
    return x
    y := 2
    _ = y
}`,
			want: []string{"x"},
		},
		{
			name: "scoped block",
			src: `package foo
func Foo(cond bool) int {
    if cond {
        z := 1
        _ = z
    }
    return 0
}`,
			want: []string{"cond"},
		},
		{
			name: "reuse name",
			src: `package foo
func Foo(a int) int {
    a := 2
    return a
}`,
			want: []string{"a"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			file, err := parser.ParseFile(fset, "foo.go", tc.src, 0)
			require.NoError(t, err)

			var fn *ast.FuncDecl
			var ret *ast.ReturnStmt
			ast.Inspect(file, func(n ast.Node) bool {
				switch x := n.(type) {
				case *ast.FuncDecl:
					fn = x
				case *ast.ReturnStmt:
					if ret == nil {
						ret = x
					}
				}
				return true
			})
			require.NotNil(t, fn)
			require.NotNil(t, ret)

			decls := visibleDeclsBefore(fn, ret.Pos())
			names := make([]string, len(decls))
			for i, d := range decls {
				names[i] = d.ident.Name
			}

			assert.ElementsMatch(t, tc.want, names)
		})
	}
}

func TestBuildReturnInstrumentationNamedResult(t *testing.T) {
	t.Parallel()

	src := `package foo
func Bar() (x int) {
       x = 5
       return
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Bar"}, decls,
		[]ast.Expr{ast.NewIdent("int")}, nil, []string{"x"})
	require.NoError(t, err)

	rs, ok := blk.List[len(blk.List)-1].(*ast.ReturnStmt)
	require.True(t, ok)
	require.Len(t, rs.Results, 1)
	id, ok := rs.Results[0].(*ast.Ident)
	require.True(t, ok)
	assert.Equal(t, "x", id.Name)

	ast.Inspect(blk, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			assert.False(t, strings.HasPrefix(id.Name, syntheticFieldNamePrefixReturn))
		}
		return true
	})
}

func TestBuildReturnInstrumentationBasicLit(t *testing.T) {
	t.Parallel()

	src := `package foo
func Foo() int {
       return 42
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Foo"}, decls,
		[]ast.Expr{ast.NewIdent("int")}, nil, []string{""})
	require.NoError(t, err)

	require.Len(t, blk.List, 3)
	_, ok := blk.List[0].(*ast.AssignStmt)
	assert.False(t, ok)

	ast.Inspect(blk, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			assert.False(t, strings.HasPrefix(id.Name, syntheticFieldNamePrefixTemp))
		}
		return true
	})
}

func TestBuildReturnInstrumentationBasicLitInterface(t *testing.T) {
	t.Parallel()

	src := `package foo
func Foo() interface{} {
       return 42
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	iface, _ := parser.ParseExpr("interface{}")
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Foo"}, decls,
		[]ast.Expr{iface}, nil, []string{""})
	require.NoError(t, err)

	require.Len(t, blk.List, 4)
	_, ok := blk.List[0].(*ast.DeclStmt)
	assert.True(t, ok)

	var foundTmp bool
	ast.Inspect(blk, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			if strings.HasPrefix(id.Name, syntheticFieldNamePrefixTemp) {
				foundTmp = true
			}
		}
		return true
	})
	assert.True(t, foundTmp)
}

func TestBuildReturnInstrumentationInterfaceConv(t *testing.T) {
	t.Parallel()

	src := `package foo
func Foo(x int) interface{} {
       return interface{}(x)
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	iface, _ := parser.ParseExpr("interface{}")
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Foo"}, decls,
		[]ast.Expr{iface}, nil, []string{""})
	require.NoError(t, err)

	var haveConv bool
	ast.Inspect(blk, func(n ast.Node) bool {
		if _, ok := n.(*ast.TypeAssertExpr); ok {
			haveConv = true
		}
		return true
	})
	assert.False(t, haveConv)
}

func TestBuildReturnInstrumentationMultiNamedResult(t *testing.T) {
	t.Parallel()

	src := `package foo
func Baz() (x, y int) {
       x, y = 1, 2
       return
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Baz"}, decls,
		[]ast.Expr{ast.NewIdent("int"), ast.NewIdent("int")}, nil, []string{"x", "y"})
	require.NoError(t, err)

	rs, ok := blk.List[len(blk.List)-1].(*ast.ReturnStmt)
	require.True(t, ok)
	require.Len(t, rs.Results, 2)
	id1, ok := rs.Results[0].(*ast.Ident)
	require.True(t, ok)
	assert.Equal(t, "x", id1.Name)
	id2, ok := rs.Results[1].(*ast.Ident)
	require.True(t, ok)
	assert.Equal(t, "y", id2.Name)

	ast.Inspect(blk, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			assert.False(t, strings.HasPrefix(id.Name, syntheticFieldNamePrefixReturn))
		}
		return true
	})
}

func TestBuildReturnInstrumentationMixedResult(t *testing.T) {
	t.Parallel()

	src := `package foo
func Qux() (int, y int) {
       y = 42
       return
}`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)
	var buf bytes.Buffer

	fn := file.Decls[0].(*ast.FuncDecl)
	var ret *ast.ReturnStmt
	ast.Inspect(fn, func(n ast.Node) bool {
		if r, ok := n.(*ast.ReturnStmt); ok {
			ret = r
			return false
		}
		return true
	})
	require.NotNil(t, ret)

	decls := visibleDeclsBefore(fn, ret.Pos())
	blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Qux"}, decls,
		[]ast.Expr{ast.NewIdent("int"), ast.NewIdent("int")}, nil, []string{"", "y"})
	require.NoError(t, err)

	rs, ok := blk.List[len(blk.List)-1].(*ast.ReturnStmt)
	require.True(t, ok)
	require.Empty(t, rs.Results)

	ast.Inspect(blk, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			assert.False(t, strings.HasPrefix(id.Name, syntheticFieldNamePrefixReturn))
		}
		return true
	})
}

func TestBuildReturnInstrumentationRecursive(t *testing.T) {
	t.Parallel()

	iface, _ := parser.ParseExpr("interface{}")
	testCases := []struct {
		name       string
		src        string
		resultType ast.Expr
		expectTmp  bool
	}{
		{
			name: "concrete",
			src: `package foo
func Foo(n int) int {
    if n > 0 {
        return Foo(n-1)
    }
    return 1
}`,
			resultType: ast.NewIdent("int"),
		},
		{
			name: "interface",
			src: `package foo
func Foo(n int) interface{} {
    if n > 0 {
        return Foo(n-1)
    }
    return n
}`,
			resultType: iface,
			expectTmp:  true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			file, err := parser.ParseFile(fset, "foo.go", tc.src, 0)
			require.NoError(t, err)
			var buf bytes.Buffer

			fn := file.Decls[0].(*ast.FuncDecl)
			var rets []*ast.ReturnStmt
			ast.Inspect(fn, func(n ast.Node) bool {
				if r, ok := n.(*ast.ReturnStmt); ok {
					rets = append(rets, r)
				}
				return true
			})
			require.Len(t, rets, 2)

			for i, ret := range rets {
				decls := visibleDeclsBefore(fn, ret.Pos())
				blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Foo"}, decls,
					[]ast.Expr{tc.resultType}, nil, []string{""})
				require.NoError(t, err)

				var haveRec, haveTmp bool
				ast.Inspect(blk, func(n ast.Node) bool {
					if id, ok := n.(*ast.Ident); ok {
						if strings.HasPrefix(id.Name, syntheticFieldNamePrefixRecursive) {
							haveRec = true
						}
						if strings.HasPrefix(id.Name, syntheticFieldNamePrefixTemp) {
							haveTmp = true
						}
					}
					return true
				})

				if i == 0 {
					assert.True(t, haveRec)
				} else {
					assert.False(t, haveRec)
				}
				if tc.expectTmp {
					assert.True(t, haveTmp)
				} else if i == 1 {
					assert.False(t, haveTmp)
				}
			}
		})
	}
}

func TestReturnNilToInterface(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name         string
		src          string
		resultType   string
		expectTmpVar bool // Should we expect a temporary variable?
	}{
		{
			name: "nil_to_error",
			src: `package foo
func GetError() error {
	return nil
}`,
			resultType:   "error",
			expectTmpVar: false, // error is a named type, doesn't trigger needTmp
		},
		{
			name: "nil_to_empty_interface",
			src: `package foo
func GetAny() interface{} {
	return nil
}`,
			resultType:   "interface{}",
			expectTmpVar: true,
		},
		{
			name: "nil_to_pointer",
			src: `package foo
func GetPtr() *int {
	return nil
}`,
			resultType:   "*int",
			expectTmpVar: false, // pointers don't need temp
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			file, err := parser.ParseFile(fset, "test.go", tc.src, 0)
			require.NoError(t, err)
			var buf bytes.Buffer

			fn := file.Decls[0].(*ast.FuncDecl)
			var ret *ast.ReturnStmt
			ast.Inspect(fn, func(n ast.Node) bool {
				if r, ok := n.(*ast.ReturnStmt); ok {
					ret = r
					return false
				}
				return true
			})
			require.NotNil(t, ret)

			resultType, err := parser.ParseExpr(tc.resultType)
			require.NoError(t, err)

			decls := visibleDeclsBefore(fn, ret.Pos())
			blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Test"}, decls,
				[]ast.Expr{resultType}, nil, []string{""})
			require.NoError(t, err)

			// Format the block to ensure it is a valid Go code
			var genBuf bytes.Buffer
			err = format.Node(&genBuf, token.NewFileSet(), blk)
			require.NoError(t, err)

			// Check we don't generate invalid "tmpX := nil"
			generated := genBuf.String()
			assert.NotContains(t, generated, "lenSyntheticTmp0 := nil")

			// Check that the generated code handles nil correctly
			// Even if not using temp, nil should be handled properly
			if ret.Results[0].(*ast.Ident).Name == "nil" {
				// nil returns should not cause invalid syntax
				assert.NotContains(t, generated, ":= nil")
			}
		})
	}
}

// TestMakeReturnTempNilHandling directly tests makeReturnTemp with nil
func TestMakeReturnTempNilHandling(t *testing.T) {
	t.Parallel()

	// Test that nil is handled correctly
	nilIdent := ast.NewIdent("nil")
	errorType := ast.NewIdent("error")

	retId, stmts, snap := makeReturnTemp("lenSyntheticRet", 0, nilIdent, errorType)

	assert.NotNil(t, retId)
	assert.Equal(t, "lenSyntheticRet0", retId.Name)
	assert.NotNil(t, snap)

	// Should only have one statement (var declaration)
	assert.Len(t, stmts, 1)

	// Format and check it's valid
	var buf bytes.Buffer
	err := format.Node(&buf, token.NewFileSet(), stmts[0])
	require.NoError(t, err)

	// Should be "var lenSyntheticRet0 error = nil"
	generated := buf.String()
	assert.Contains(t, generated, "var lenSyntheticRet0 error = nil")
	assert.NotContains(t, generated, ":= nil")
}

func TestBuildReturnInstrumentationBareReturnBlankIdentifier(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name             string
		src              string
		funcResultTypes  []string
		funcResultNames  []string
		expectBareReturn bool // Should the generated return be bare (no values)?
		expectedSnaps    []string
	}{
		{
			name: "named_and_blank",
			src: `package foo
func GetTokens() (out []int, _ error) {
	return
}`,
			funcResultTypes:  []string{"[]int", "error"},
			funcResultNames:  []string{"out", "_"},
			expectBareReturn: true,
			expectedSnaps:    []string{"out"}, // Only capture 'out', not '_'
		},
		{
			name: "all_blank",
			src: `package foo
func GetBlanks() (_ int, _ error) {
	return
}`,
			funcResultTypes:  []string{"int", "error"},
			funcResultNames:  []string{"_", "_"},
			expectBareReturn: true,
			expectedSnaps:    []string{}, // No snapshots for blank identifiers
		},
		{
			name: "all_named_no_blank",
			src: `package foo
func GetPair() (x int, err error) {
	return
}`,
			funcResultTypes:  []string{"int", "error"},
			funcResultNames:  []string{"x", "err"},
			expectBareReturn: false, // Should return explicit values
			expectedSnaps:    []string{"x", "err"},
		},
		{
			name: "single_blank",
			src: `package foo
func GetBlank() (_ int) {
	return
}`,
			funcResultTypes:  []string{"int"},
			funcResultNames:  []string{"_"},
			expectBareReturn: true,
			expectedSnaps:    []string{},
		},
		{
			name: "mixed_blank_named",
			src: `package foo
func GetMixed() (_ int, result string, _ error) {
	return
}`,
			funcResultTypes:  []string{"int", "string", "error"},
			funcResultNames:  []string{"_", "result", "_"},
			expectBareReturn: true,
			expectedSnaps:    []string{"result"}, // Only capture 'result'
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			file, err := parser.ParseFile(fset, "test.go", tc.src, 0)
			require.NoError(t, err)
			var buf bytes.Buffer

			fn := file.Decls[0].(*ast.FuncDecl)
			var ret *ast.ReturnStmt
			ast.Inspect(fn, func(n ast.Node) bool {
				if r, ok := n.(*ast.ReturnStmt); ok {
					ret = r
					return false
				}
				return true
			})
			require.NotNil(t, ret)
			require.Empty(t, ret.Results)

			// Build funcResultTypes from strings
			funcResultTypes := make([]ast.Expr, len(tc.funcResultTypes))
			for i, typeStr := range tc.funcResultTypes {
				typ, err := parser.ParseExpr(typeStr)
				require.NoError(t, err)
				funcResultTypes[i] = typ
			}

			decls := visibleDeclsBefore(fn, ret.Pos())
			blk, err := buildReturnInstrumentation(&buf, ret, 1, &Function{FunctionName: "Test"}, decls,
				funcResultTypes, nil, tc.funcResultNames)
			require.NoError(t, err)

			var genBuf bytes.Buffer
			err = format.Node(&genBuf, token.NewFileSet(), blk)
			require.NoError(t, err)

			generated := genBuf.String()

			// Should never try to use '_' as a value
			assert.NotContains(t, generated, "= _")
			assert.NotContains(t, generated, ": _")
			assert.NotRegexp(t, `\b_\s*\}`, generated)

			// Check the return statement
			rs, ok := blk.List[len(blk.List)-1].(*ast.ReturnStmt)
			require.True(t, ok)

			if tc.expectBareReturn {
				assert.Empty(t, rs.Results)
			} else {
				assert.NotEmpty(t, rs.Results)
			}

			// Verify expected snapshots are present
			for _, snapName := range tc.expectedSnaps {
				assert.Contains(t, generated, snapName)
			}
		})
	}
}

func TestImplicitReturnInstrumentation(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name           string
		src            string
		expectReturn   bool
		returnVarNames []string
	}{
		{
			name: "named_returns_no_explicit_return",
			src: `package foo
func GetValue() (result int) {
	result = 42
}`,
			expectReturn:   true,
			returnVarNames: []string{"result"},
		},
		{
			name: "multiple_named_returns",
			src: `package foo
func GetPair() (x, y int) {
	x, y = 1, 2
}`,
			expectReturn:   true,
			returnVarNames: []string{"x", "y"},
		},
		{
			name: "void_function",
			src: `package foo
func DoNothing() {
	x := 1
	_ = x
}`,
			expectReturn:   false,
			returnVarNames: nil,
		},
		{
			name: "unnamed_returns_no_explicit_return",
			src: `package foo
func GetValue() (int, error) {
}`,
			expectReturn:   true,
			returnVarNames: []string{"", ""},
		},
		{
			name: "single_unnamed_return_no_explicit",
			src: `package foo
func GetString() string {
}`,
			expectReturn:   true,
			returnVarNames: []string{""},
		},
		{
			name: "mixed_named_unnamed_no_explicit",
			src: `package foo
func GetMixed() (_ int, err error) {
	err = nil
}`,
			expectReturn:   true,
			returnVarNames: []string{"_", "err"},
		},
		{
			name: "all_blank_identifiers",
			src: `package foo
func GetBlanks() (_ int, _ error) {
}`,
			expectReturn:   true,
			returnVarNames: []string{"_", "_"},
		},
		{
			name: "mixed_blank_named_unnamed",
			src: `package foo
func GetComplex() (_ int, result string, err error) {
}`,
			expectReturn:   true,
			returnVarNames: []string{"_", "result", "err"},
		},
		{
			name: "single_blank_identifier",
			src: `package foo
func GetBlank() (_ int) {
}`,
			expectReturn:   true,
			returnVarNames: []string{"_"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			file, err := parser.ParseFile(fset, "test.go", tc.src, 0)
			require.NoError(t, err)

			fn := file.Decls[0].(*ast.FuncDecl)

			// Simulate the logic from InjectFuncPointReturnStates
			var funcResultNames []string
			if fn.Type.Results != nil {
				for _, field := range fn.Type.Results.List {
					if len(field.Names) == 0 {
						funcResultNames = append(funcResultNames, "")
					} else {
						for _, id := range field.Names {
							funcResultNames = append(funcResultNames, id.Name)
						}
					}
				}
			}

			assert.Equal(t, tc.returnVarNames, funcResultNames)

			// Check if we should add a return statement
			// Add return if there are return values (named or unnamed)
			hasReturnValues := len(funcResultNames) > 0
			assert.Equal(t, tc.expectReturn, hasReturnValues)

			if hasReturnValues {
				// Build the return statement that would be added - matching InjectFuncPointReturnStates logic
				allNamed := len(funcResultNames) > 0 && !slices.Contains(funcResultNames, "")

				// Check if ALL returns are blank identifiers
				allBlank := true
				for _, name := range funcResultNames {
					if name != "" && name != "_" {
						allBlank = false
						break
					}
				}

				var buf bytes.Buffer

				if allBlank {
					// All blank: naked return
					retStmt := &ast.ReturnStmt{}
					err := format.Node(&buf, token.NewFileSet(), retStmt)
					require.NoError(t, err)
					assert.Equal(t, "return", buf.String())
				} else if allNamed {
					// All named (but not all blank): return named variables
					returnExprs := make([]ast.Expr, len(funcResultNames))
					for i, name := range funcResultNames {
						if name != "" && name != "_" {
							returnExprs[i] = ast.NewIdent(name)
						} else {
							// Get the type for blank identifier
							funcResultTypes := make([]ast.Expr, 0)
							if fn.Type.Results != nil {
								for _, field := range fn.Type.Results.List {
									if len(field.Names) == 0 {
										funcResultTypes = append(funcResultTypes, field.Type)
									} else {
										for range field.Names {
											funcResultTypes = append(funcResultTypes, field.Type)
										}
									}
								}
							}
							zeroVal, err := zeroValueForType(&buf, funcResultTypes[i])
							require.NoError(t, err)
							returnExprs[i] = zeroVal
						}
					}
					retStmt := &ast.ReturnStmt{Results: returnExprs}
					buf.Reset()
					err := format.Node(&buf, token.NewFileSet(), retStmt)
					require.NoError(t, err)

					generated := buf.String()
					// Should not contain "_" as a value
					assert.NotContains(t, generated, "return _")
				} else {
					// Has unnamed: generate zero values
					funcResultTypes := make([]ast.Expr, 0)
					if fn.Type.Results != nil {
						for _, field := range fn.Type.Results.List {
							if len(field.Names) == 0 {
								funcResultTypes = append(funcResultTypes, field.Type)
							} else {
								for range field.Names {
									funcResultTypes = append(funcResultTypes, field.Type)
								}
							}
						}
					}

					returnExprs := make([]ast.Expr, len(funcResultTypes))
					for i, typ := range funcResultTypes {
						if allNamed && funcResultNames[i] != "" && funcResultNames[i] != "_" {
							returnExprs[i] = ast.NewIdent(funcResultNames[i])
						} else if funcResultNames[i] != "" && funcResultNames[i] != "_" {
							returnExprs[i] = ast.NewIdent(funcResultNames[i])
						} else {
							zeroVal, err := zeroValueForType(&buf, typ)
							require.NoError(t, err)
							returnExprs[i] = zeroVal
						}
					}
					retStmt := &ast.ReturnStmt{Results: returnExprs}

					buf.Reset()
					err := format.Node(&buf, token.NewFileSet(), retStmt)
					require.NoError(t, err)
					assert.NotEmpty(t, buf.String())
					// Should not contain "_" as a value
					assert.NotContains(t, buf.String(), "return _")
				}
			}
		})
	}
}

func TestInjectFuncPointBeforeCall(t *testing.T) {
	t.Parallel()

	const (
		testPkgName     = "testpkg"
		fmtPackage      = "fmt"
		printfFuncName  = "Printf"
		sprintfFuncName = "Sprintf"
	)

	testCases := []struct {
		name           string
		src            string
		funcName       string
		predicate      func(*ast.CallExpr) (any, bool)
		expectedPoints int
		expectedCalls  map[string]int // pkg.Func -> count after injection
	}{
		{
			name: "single_call",
			src: `package testpkg
import "fmt"

func ProcessData(data string) {
	fmt.Printf("Data: %s\n", data)
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Printf": 1},
		},
		{
			name: "multiple_calls_same_function",
			src: `package testpkg
import "fmt"

func ProcessData(a, b string) {
	fmt.Printf("First: %s\n", a)
	fmt.Println("Middle")
	fmt.Printf("Second: %s\n", b)
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 2,
			expectedCalls:  map[string]int{"fmt.Printf": 2, "fmt.Println": 1},
		},
		{
			name: "call_in_nested_blocks",
			src: `package testpkg
import "fmt"

func ProcessData(data string) {
	if len(data) > 0 {
		fmt.Printf("Data: %s\n", data)
	}
	for i := 0; i < 10; i++ {
		fmt.Printf("Index: %d\n", i)
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 2,
			expectedCalls:  map[string]int{"fmt.Printf": 2},
		},
		{
			name: "no_matching_calls",
			src: `package testpkg
import "fmt"

func ProcessData(data string) {
	fmt.Println("No Printf here")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 0,
			expectedCalls:  map[string]int{"fmt.Println": 1},
		},
		{
			name: "call_in_switch",
			src: `package testpkg
import "fmt"

func ProcessData(op string) {
	switch op {
	case "print":
		fmt.Printf("Printing\n")
	case "log":
		fmt.Println("Logging")
	default:
		fmt.Printf("Unknown\n")
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 2,
			expectedCalls:  map[string]int{"fmt.Printf": 2, "fmt.Println": 1},
		},
		{
			name: "predicate_never_matches",
			src: `package testpkg
import "fmt"

func ProcessData(data string) {
	fmt.Printf("Data: %s\n", data)
	fmt.Println("Log message")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				return nil, false // Never match
			},
			expectedPoints: 0,
			expectedCalls:  map[string]int{"fmt.Printf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_var_declaration",
			src: `package testpkg
import "fmt"

func ProcessData() {
	var x = fmt.Sprintf("test")
	_ = x
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1},
		},
		{
			name: "call_in_if_init",
			src: `package testpkg
import "fmt"

func ProcessData() {
	if x := fmt.Sprintf("test"); len(x) > 0 {
		fmt.Println(x)
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_for_init",
			src: `package testpkg
import "fmt"

func ProcessData() {
	for i := fmt.Sprint(0); i == "0"; i = fmt.Sprint(1) {
		break
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == "Sprint"
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 2, // Init and Post
			expectedCalls:  map[string]int{"fmt.Sprint": 2},
		},
		{
			name: "call_in_switch_init",
			src: `package testpkg
import "fmt"

func ProcessData() {
	switch x := fmt.Sprintf("test"); x {
	case "test":
		fmt.Println("matched")
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_range_expr",
			src: `package testpkg
import "fmt"

func GetSlice() []string { return []string{"a", "b"} }

func ProcessData() {
	for _, v := range GetSlice() {
		fmt.Println(v)
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == "GetSlice"
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Println": 1},
		},
		{
			name: "multiple_calls_same_statement",
			src: `package testpkg
import "fmt"

func ProcessData() {
	x, y := fmt.Sprintf("a"), fmt.Sprintf("b")
	_, _ = x, y
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1, // One monitoring point before the entire statement
			expectedCalls:  map[string]int{"fmt.Sprintf": 2},
		},
		{
			name: "call_in_return",
			src: `package testpkg
import "fmt"

func ProcessData() string {
	return fmt.Sprintf("result")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1},
		},
		{
			name: "call_in_assignment",
			src: `package testpkg
import "fmt"

func ProcessData() {
	var x string
	x = fmt.Sprintf("test")
	_ = x
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1},
		},
		{
			name: "call_with_defer",
			src: `package testpkg
import "fmt"

func ProcessData() {
	defer fmt.Printf("cleanup\n")
	fmt.Println("work")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Printf": 1, "fmt.Println": 1},
		},
		{
			name: "call_with_go",
			src: `package testpkg
import "fmt"

func ProcessData() {
	go fmt.Printf("async\n")
	fmt.Println("sync")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Printf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_channel_send",
			src: `package testpkg
import "fmt"

func ProcessData(ch chan string) {
	ch <- fmt.Sprintf("message")
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1},
		},
		{
			name: "call_in_select",
			src: `package testpkg
import "fmt"

func ProcessData(ch chan string) {
	select {
	case ch <- fmt.Sprintf("send"):
	case msg := <-ch:
		fmt.Println(msg)
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_if_condition",
			src: `package testpkg
import "fmt"

func IsPositive(x int) bool { return x > 0 }

func ProcessData() {
	if IsPositive(fmt.Sprintf("test") == "test") {
		fmt.Println("positive")
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == "IsPositive"
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1, "fmt.Println": 1},
		},
		{
			name: "call_in_for_condition",
			src: `package testpkg
import "fmt"

func ShouldContinue() bool { return false }

func ProcessData() {
	for ; ShouldContinue(); {
		fmt.Println("loop")
		break
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == "ShouldContinue"
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Println": 1},
		},
		{
			name: "call_in_switch_tag",
			src: `package testpkg
import "fmt"

func ProcessData() {
	switch fmt.Sprintf("test") {
	case "test":
		fmt.Println("matched")
	default:
		fmt.Println("default")
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return struct{}{}, x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 1, "fmt.Println": 2},
		},
		{
			name: "call_in_type_switch_assign",
			src: `package testpkg
import "fmt"

func GetInterface() interface{} { return "test" }

func ProcessData() {
	switch v := GetInterface().(type) {
	case string:
		fmt.Println(v)
	default:
		fmt.Println("unknown")
	}
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == "GetInterface"
				}
				return struct{}{}, false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Println": 2},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			filePath := filepath.Join(dir, "test.go")
			require.NoError(t, os.WriteFile(filePath, []byte(tc.src), 0o644))
			modifier := &ASTModifier{}
			fn := Function{
				FunctionIdent: testPkgName + ":" + tc.funcName,
				FunctionName:  tc.funcName,
				PackageName:   testPkgName,
				FilePath:      filePath,
			}

			pointMap, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Len(t, pointMap, tc.expectedPoints)

			// Verify point IDs are sequential
			pointIDs := make([]uint32, 0, len(pointMap))
			for id := range pointMap {
				pointIDs = append(pointIDs, id)
			}
			slices.Sort(pointIDs)
			for i, id := range pointIDs {
				assert.Equal(t, uint32(i+1), id) // point IDs start at 1
			}

			require.NoError(t, modifier.CommitFile(filePath))

			// Read and parse modified file
			modifiedSrc, err := os.ReadFile(filePath)
			require.NoError(t, err)
			modifiedStr := string(modifiedSrc)

			fset := token.NewFileSet()
			modFile, err := parser.ParseFile(fset, filePath, nil, 0)
			require.NoError(t, err)

			// Verify monitoring calls are present (no longer check for marker since it's removed)
			if tc.expectedPoints > 0 {
				assert.Contains(t, modifiedStr, sendLensPointStateMessageFunc)
			}

			// Find function and count calls
			var funcDecl *ast.FuncDecl
			for _, decl := range modFile.Decls {
				if fd, ok := decl.(*ast.FuncDecl); ok && fd.Name.Name == tc.funcName {
					funcDecl = fd
					break
				}
			}
			require.NotNil(t, funcDecl)

			// Count monitoring and target calls
			var monitoringCount int
			callCounts := make(map[string]int)
			ast.Inspect(funcDecl, func(n ast.Node) bool {
				if call, ok := n.(*ast.CallExpr); ok {
					if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == sendLensPointStateMessageFunc {
						monitoringCount++
					}
					if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
						if x, ok := sel.X.(*ast.Ident); ok {
							callCounts[x.Name+"."+sel.Sel.Name]++
						}
					}
				}
				return true
			})

			assert.Equal(t, tc.expectedPoints, monitoringCount)

			// Verify original calls are preserved
			for fnName, expectedCount := range tc.expectedCalls {
				assert.Equal(t, expectedCount, callCounts[fnName])
			}

			// Verify idempotency - calling again with same predicate should not re-instrument
			pointMap2, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Empty(t, pointMap2)
		})
	}

	t.Run("type_reservation", func(t *testing.T) {
		tests := []struct {
			name           string
			source         string
			expectedInCode string
		}{
			{
				name: "selector_expr_syscall_constant",
				source: `package test
import "syscall"
func foo() {
	bar(syscall.SYS_IOCTL)
}
func bar(x uintptr) {}`,
				expectedInCode: "syscall.SYS_IOCTL",
			},
			{
				name: "selector_expr_field_access",
				source: `package test
type Config struct { Value int }
func foo(c Config) {
	bar(c.Value)
}
func bar(x int) {}`,
				expectedInCode: "c.Value",
			},
			{
				name: "basic_lit_untyped_constant",
				source: `package test
func foo() {
	bar(42)
}
func bar(x int64) {}`,
				expectedInCode: "42",
			},
			{
				name: "basic_lit_string",
				source: `package test
func foo() {
	bar("hello")
}
func bar(s string) {}`,
				expectedInCode: `"hello"`,
			},
		}

		for _, tt := range tests {
			t.Run(tt.name, func(t *testing.T) {
				dir := t.TempDir()
				filePath := filepath.Join(dir, "test.go")
				err := os.WriteFile(filePath, []byte(tt.source), 0o644)
				require.NoError(t, err)

				modifier := &ASTModifier{}
				fn := Function{
					FunctionIdent: "test:bar",
					FunctionName:  "bar",
					PackageName:   "test",
					FilePath:      filePath,
				}

				_, err = modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
					if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == "bar" {
						return "test", true
					}
					return nil, false
				})
				require.NoError(t, err)

				err = modifier.CommitFile(filePath)
				require.NoError(t, err)

				modifiedSrc, err := os.ReadFile(filePath)
				require.NoError(t, err)

				assert.Contains(t, string(modifiedSrc), tt.expectedInCode)
			})
		}
	})
}

func TestInjectFuncPointBeforeCallMultipleSinks(t *testing.T) {
	t.Parallel()

	// Test that we can call InjectFuncPointBeforeCall multiple times with different predicates
	// to instrument different security sinks in the same function
	src := `package testpkg
import (
	"fmt"
	"os"
	"os/exec"
)

func ProcessData(path, cmd string) {
	// Security sink 1: file system access
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()

	// Security sink 2: command execution
	output, err := exec.Command("sh", "-c", cmd).Output()
	if err != nil {
		return
	}

	// Regular output (not a security sink)
	fmt.Println(string(output))
}
`
	dir := t.TempDir()
	filePath := filepath.Join(dir, "test.go")
	require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

	modifier := &ASTModifier{}
	fn := Function{
		FunctionIdent: "testpkg:ProcessData",
		FunctionName:  "ProcessData",
		PackageName:   "testpkg",
		FilePath:      filePath,
	}

	// First call: instrument os.Open (filesystem access sink)
	pointMap1, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				if x.Name == "os" && sel.Sel.Name == "Open" {
					return "filesystem:open", true
				}
			}
		}
		return nil, false
	})
	require.NoError(t, err)
	require.Len(t, pointMap1, 1)

	var fsOpenPointID uint32
	for id := range pointMap1 {
		fsOpenPointID = id
	}

	// Commit the first set of changes
	require.NoError(t, modifier.CommitFile(filePath))

	// Second call: instrument exec.Command (command execution sink)
	pointMap2, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				if x.Name == "exec" && sel.Sel.Name == "Command" {
					return "exec:command", true
				}
			}
		}
		return nil, false
	})
	require.NoError(t, err)
	require.Len(t, pointMap2, 1)

	var execCmdPointID uint32
	for id := range pointMap2 {
		execCmdPointID = id
	}

	// Point IDs should be different
	require.NotEqual(t, fsOpenPointID, execCmdPointID)

	// Commit the second set of changes
	require.NoError(t, modifier.CommitFile(filePath))

	// Read and verify the modified file
	modifiedSrc, err := os.ReadFile(filePath)
	require.NoError(t, err)
	modifiedStr := string(modifiedSrc)

	// Verify both instrumentation points are present
	assert.Contains(t, modifiedStr, sendLensPointStateMessageFunc)

	// Parse and count monitoring calls
	fset := token.NewFileSet()
	modFile, err := parser.ParseFile(fset, filePath, nil, 0)
	require.NoError(t, err)

	var funcDecl *ast.FuncDecl
	for _, decl := range modFile.Decls {
		if fd, ok := decl.(*ast.FuncDecl); ok && fd.Name.Name == "ProcessData" {
			funcDecl = fd
			break
		}
	}
	require.NotNil(t, funcDecl)

	// Count monitoring calls and verify both are present
	monitoringCalls := 0
	foundPointIDs := make(map[uint32]bool)
	ast.Inspect(funcDecl, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == sendLensPointStateMessageFunc {
				monitoringCalls++
				// Extract point ID from first argument
				if len(call.Args) > 0 {
					if lit, ok := call.Args[0].(*ast.BasicLit); ok {
						if id, err := strconv.ParseUint(lit.Value, 10, 32); err == nil {
							foundPointIDs[uint32(id)] = true
						}
					}
				}
			}
		}
		return true
	})

	assert.Equal(t, 2, monitoringCalls)
	assert.True(t, foundPointIDs[fsOpenPointID])
	assert.True(t, foundPointIDs[execCmdPointID])

	// Verify original calls are preserved
	assert.Contains(t, modifiedStr, "os.Open")
	assert.Contains(t, modifiedStr, "exec.Command")
	assert.Contains(t, modifiedStr, "fmt.Println")

	// Third call: try to re-instrument os.Open - should be idempotent
	pointMap3, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				if x.Name == "os" && sel.Sel.Name == "Open" {
					return "filesystem:open", true
				}
			}
		}
		return nil, false
	})
	require.NoError(t, err)
	assert.Empty(t, pointMap3)
}

func TestBuildCallInstrumentationWithArgs(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name          string
		callExpr      string
		expectedArgs  []string // Expected argument names after transformation
		expectedCount int
	}{
		{
			name:          "zero arguments",
			callExpr:      "foo()",
			expectedArgs:  []string{},
			expectedCount: 0,
		},
		{
			name:          "single argument",
			callExpr:      "foo(x)",
			expectedArgs:  []string{"arg0"},
			expectedCount: 1,
		},
		{
			name:          "multiple arguments",
			callExpr:      "foo(a, b, c)",
			expectedArgs:  []string{"arg0", "arg1", "arg2"},
			expectedCount: 3,
		},
		{
			name:          "complex expressions",
			callExpr:      "foo(x+y, bar(), \"literal\")",
			expectedArgs:  []string{"arg0", "arg1", "arg2"},
			expectedCount: 3,
		},
		{
			name:          "variadic call with ellipsis",
			callExpr:      "append(slice, elements...)",
			expectedArgs:  []string{"arg0", "arg1"},
			expectedCount: 2,
		},
		{
			name:          "variadic with explicit args",
			callExpr:      "fmt.Printf(\"%s %d\", str, num)",
			expectedArgs:  []string{"arg0", "arg1", "arg2"},
			expectedCount: 3,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Parse the call expression
			call, err := parser.ParseExpr(tc.callExpr)
			require.NoError(t, err)
			callExpr, ok := call.(*ast.CallExpr)
			require.True(t, ok)

			// Build a file node with fmt import for proper package detection
			const fileSrc = `package test
import "fmt"
`
			fset := token.NewFileSet()
			fileNode, err := parser.ParseFile(fset, "", fileSrc, 0)
			require.NoError(t, err)

			// Build package names map from file node
			filePackageNames := make(map[string]bool)
			for _, imp := range fileNode.Imports {
				if imp.Name != nil {
					filePackageNames[imp.Name.Name] = true
				} else {
					path := strings.Trim(imp.Path.Value, `"`)
					if idx := strings.LastIndex(path, "/"); idx != -1 {
						filePackageNames[path[idx+1:]] = true
					} else {
						filePackageNames[path] = true
					}
				}
			}

			// Build instrumentation
			var buf bytes.Buffer
			stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, filePackageNames)
			require.NoError(t, err)
			require.NotEmpty(t, stmts)

			// Extract the monitoring call (always the last statement returned)
			monitorStmt := stmts[len(stmts)-1]
			exprStmt, ok := monitorStmt.(*ast.ExprStmt)
			require.True(t, ok)
			monitorCall, ok := exprStmt.X.(*ast.CallExpr)
			require.True(t, ok)

			// Verify the function being called is SendLensPointStateMessage
			funIdent, ok := monitorCall.Fun.(*ast.Ident)
			require.True(t, ok)
			assert.Equal(t, sendLensPointStateMessageFunc, funIdent.Name)

			// Verify point ID (first argument)
			require.NotEmpty(t, monitorCall.Args)
			pointIDLit, ok := monitorCall.Args[0].(*ast.BasicLit)
			require.True(t, ok)
			assert.Equal(t, "42", pointIDLit.Value)

			// Verify number of snapshots matches expected
			snapshotCount := len(monitorCall.Args) - 1 // Subtract point ID
			assert.Equal(t, tc.expectedCount, snapshotCount)

			// Verify each snapshot has correct naming
			for i, expectedName := range tc.expectedArgs {
				snapshot, ok := monitorCall.Args[i+1].(*ast.CompositeLit)
				require.True(t, ok)

				// Find the Name field
				var nameValue string
				for _, elt := range snapshot.Elts {
					kv, ok := elt.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					keyIdent, ok := kv.Key.(*ast.Ident)
					if !ok || keyIdent.Name != fieldKeyName {
						continue
					}
					namelit, ok := kv.Value.(*ast.BasicLit)
					require.True(t, ok)
					nameValue, err = strconv.Unquote(namelit.Value)
					require.NoError(t, err)
					break
				}
				assert.Equal(t, expectedName, nameValue, "Snapshot %d name mismatch", i)
			}
		})
	}

	t.Run("ellipsis", func(t *testing.T) {
		src := "append(slice, elements...)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 1, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// Format the statements to verify they're valid Go code
		buf.Reset()
		formatNode := stmts[0]
		if len(stmts) > 1 {
			formatNode = &ast.BlockStmt{List: stmts}
		}
		err = format.Node(&buf, token.NewFileSet(), formatNode)
		require.NoError(t, err)

		generated := buf.String()
		// Should have arg0 and arg1
		assert.Contains(t, generated, "arg0")
		assert.Contains(t, generated, "arg1")
		// Should reference the underlying element expression, not the ellipsis itself
		assert.Contains(t, generated, "elements")
	})

	// Test for untyped constant expressions - these should NOT be extracted to synthetic variables
	// because doing so changes their type from "untyped int" to "int", breaking calls to functions
	// expecting int64 (like File.Truncate).
	t.Run("binary_expr_constant", func(t *testing.T) {
		// This simulates: f.Truncate(1440 * 1024)
		// The argument 1440 * 1024 is an untyped constant expression that must remain inline
		src := "target(1440 * 1024)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument should NOT be replaced with a synthetic variable
		// It should still be the original BinaryExpr
		assert.IsType(t, &ast.BinaryExpr{}, callExpr.Args[0])

		// Verify the snapshot still captures the value
		monitorStmt := stmts[len(stmts)-1]
		exprStmt, ok := monitorStmt.(*ast.ExprStmt)
		require.True(t, ok)
		monitorCall, ok := exprStmt.X.(*ast.CallExpr)
		require.True(t, ok)

		// Should have point ID + 1 snapshot
		assert.Len(t, monitorCall.Args, 2)
	})

	t.Run("unary_expr_constant", func(t *testing.T) {
		// Test: target(-42) - unary expression with constant operand
		src := "target(-42)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument should NOT be replaced with a synthetic variable
		assert.IsType(t, &ast.UnaryExpr{}, callExpr.Args[0])
	})

	t.Run("paren_expr_constant", func(t *testing.T) {
		// Test: target((5 + 3)) - parenthesized constant expression
		src := "target((5 + 3))"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument should NOT be replaced with a synthetic variable
		assert.IsType(t, &ast.ParenExpr{}, callExpr.Args[0])
	})

	t.Run("shift_expr_constant", func(t *testing.T) {
		// Test: target(1 << 20) - shift expression with constant operands
		// This is a common pattern (e.g., 1 << 20 for 1MB) that must preserve untyped semantics
		src := "target(1 << 20)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument should NOT be replaced with a synthetic variable
		assert.IsType(t, &ast.BinaryExpr{}, callExpr.Args[0])
	})

	t.Run("nested_constant_expr", func(t *testing.T) {
		// Test: target(-(1 + 2) * 3) - nested constant expression
		src := "target(-(1 + 2) * 3)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument should NOT be replaced with a synthetic variable
		assert.IsType(t, &ast.BinaryExpr{}, callExpr.Args[0])
	})

	t.Run("mixed_constant_and_variable", func(t *testing.T) {
		// Test: target(x + 1) - NOT a constant expression (contains variable)
		src := "target(x + 1)"
		call, err := parser.ParseExpr(src)
		require.NoError(t, err)
		callExpr, ok := call.(*ast.CallExpr)
		require.True(t, ok)

		var buf bytes.Buffer
		stmts, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr, nil)
		require.NoError(t, err)
		require.NotEmpty(t, stmts)

		// The call argument SHOULD be replaced with a synthetic variable
		// because it contains a variable reference
		assert.IsType(t, &ast.Ident{}, callExpr.Args[0])
	})
}

func TestMakeSnapshotLitWithArgPrefix(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name         string
		inputName    string
		expectedName string
	}{
		{
			name:         "arg prefix transformation",
			inputName:    "lenSyntheticArg0",
			expectedName: "arg0",
		},
		{
			name:         "arg prefix with higher index",
			inputName:    "lenSyntheticArg42",
			expectedName: "arg42",
		},
		{
			name:         "ret prefix unchanged",
			inputName:    "lenSyntheticRet0",
			expectedName: "ret0",
		},
		{
			name:         "rec prefix unchanged",
			inputName:    "lenSyntheticRec0",
			expectedName: "rec0",
		},
		{
			name:         "no prefix",
			inputName:    "regularName",
			expectedName: "regularName",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			snapshot := makeSnapshotLit(tc.inputName, ast.NewIdent("value"))

			// Extract the Name field value
			composite, ok := snapshot.(*ast.CompositeLit)
			require.True(t, ok)

			var nameValue string
			for _, elt := range composite.Elts {
				kv, ok := elt.(*ast.KeyValueExpr)
				if !ok {
					continue
				}
				keyIdent, ok := kv.Key.(*ast.Ident)
				if !ok || keyIdent.Name != fieldKeyName {
					continue
				}
				namelit, ok := kv.Value.(*ast.BasicLit)
				require.True(t, ok)
				var err error
				nameValue, err = strconv.Unquote(namelit.Value)
				require.NoError(t, err)
				break
			}

			assert.Equal(t, tc.expectedName, nameValue)
		})
	}
}

func TestInjectFuncPointBeforeCallArgCapture(t *testing.T) {
	t.Parallel()

	const monitorFuncName = sendLensPointStateMessageFunc
	// Integration test: verify that InjectFuncPointBeforeCall uses the arg naming convention
	src := `package testpkg
import "fmt"

func ProcessData(x, y int) {
	fmt.Printf("%d %d\n", x, y)
}
`
	dir := t.TempDir()
	filePath := filepath.Join(dir, "test.go")
	require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

	modifier := &ASTModifier{}
	fn := Function{
		FunctionIdent: "testpkg:ProcessData",
		FunctionName:  "ProcessData",
		PackageName:   "testpkg",
		FilePath:      filePath,
	}

	// Inject monitoring before fmt.Printf calls
	pointMap, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				return struct{}{}, x.Name == "fmt" && sel.Sel.Name == "Printf"
			}
		}
		return struct{}{}, false
	})
	require.NoError(t, err)
	require.Len(t, pointMap, 1)

	require.NoError(t, modifier.CommitFile(filePath))

	modifiedSrc, err := os.ReadFile(filePath)
	require.NoError(t, err)
	modifiedStr := string(modifiedSrc)

	// Verify the monitoring call was inserted
	assert.Contains(t, modifiedStr, monitorFuncName)

	// Parse the modified file to verify argument naming
	fset := token.NewFileSet()
	modFile, err := parser.ParseFile(fset, filePath, nil, 0)
	require.NoError(t, err)

	// Find the monitoring call
	var foundMonitoringCall bool
	ast.Inspect(modFile, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == monitorFuncName {
				foundMonitoringCall = true

				// Verify arguments (should have point ID + 3 snapshots for fmt.Printf args)
				// Point ID + arg0 (format string) + arg1 (x) + arg2 (y)
				// fmt is not captured because it's an imported package
				assert.NotEmpty(t, call.Args)

				// Check that snapshots are only arguments
				buf := bytes.Buffer{}
				for i := 1; i < len(call.Args); i++ {
					buf.Reset()
					err := format.Node(&buf, token.NewFileSet(), call.Args[i])
					require.NoError(t, err)
					snapshot := buf.String()
					assert.Contains(t, snapshot, fmt.Sprintf("arg%d", i-1))
				}
				return false
			}
		}
		return true
	})

	assert.True(t, foundMonitoringCall)

	t.Run("arg_side_effect_single_eval", func(t *testing.T) {
		t.Parallel()

		src := `package testpkg

var counter int

func first(x int) int { return x }

func next() int {
	counter++
	return counter
}

func ProcessData() int {
	return first(next())
}
`

		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

		modifier := &ASTModifier{}
		fn := Function{
			FunctionIdent: "testpkg:ProcessData",
			FunctionName:  "ProcessData",
			PackageName:   "testpkg",
			FilePath:      filePath,
		}

		_, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "first"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)
		require.NoError(t, modifier.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)
		assert.Equal(t, 1, countFunctionCalls(t, modifiedSrc, "next"))
		code := string(modifiedSrc)
		assert.Contains(t, code, "lenSyntheticArg1_0 := next()")
		assert.Contains(t, code, "first(lenSyntheticArg1_0)")
	})

	t.Run("for_post_side_effect_single_eval", func(t *testing.T) {
		t.Parallel()

		src := `package testpkg

var counter int

func helper(int) {}

func next() int {
	counter++
	return counter
}

func Process() {
	for i := 0; i < 2; helper(next()) {
		i++
	}
}
`

		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

		modifier := &ASTModifier{}
		fn := Function{
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
			PackageName:   "testpkg",
			FilePath:      filePath,
		}

		_, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "helper"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)
		require.NoError(t, modifier.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)
		assert.Equal(t, 1, countFunctionCalls(t, modifiedSrc, "next"))
		code := string(modifiedSrc)
		assert.Contains(t, code, "for i := 0; i < 2; func() {")
		assert.Contains(t, code, "helper(lenSyntheticArg1_0)")
	})

	t.Run("multiple_args_side_effects", func(t *testing.T) {
		t.Parallel()

		src := `package testpkg

var counter int

func addThree(a, b, c int) int { return a + b + c }

func next() int {
	counter++
	return counter
}

func ProcessData() int {
	return addThree(next(), next(), next())
}
`

		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

		modifier := &ASTModifier{}
		fn := Function{
			FunctionIdent: "testpkg:ProcessData",
			FunctionName:  "ProcessData",
			PackageName:   "testpkg",
			FilePath:      filePath,
		}

		_, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "addThree"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)
		require.NoError(t, modifier.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)
		// Each next() should only be called once and stored in separate temp variables
		assert.Equal(t, 3, countFunctionCalls(t, modifiedSrc, "next"))
		code := string(modifiedSrc)
		assert.Contains(t, code, "lenSyntheticArg1_0 := next()")
		assert.Contains(t, code, "lenSyntheticArg1_1 := next()")
		assert.Contains(t, code, "lenSyntheticArg1_2 := next()")
		assert.Contains(t, code, "addThree(lenSyntheticArg1_0, lenSyntheticArg1_1, lenSyntheticArg1_2)")
	})

	t.Run("variadic_side_effects", func(t *testing.T) {
		t.Parallel()

		src := `package testpkg
import "fmt"

var counter int

func getFormat() string {
	counter++
	return "format"
}

func getArg() int {
	counter++
	return counter
}

func ProcessData() {
	fmt.Printf(getFormat(), getArg(), getArg())
}
`

		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

		modifier := &ASTModifier{}
		fn := Function{
			FunctionIdent: "testpkg:ProcessData",
			FunctionName:  "ProcessData",
			PackageName:   "testpkg",
			FilePath:      filePath,
		}

		_, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
			if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
				if x, ok := sel.X.(*ast.Ident); ok {
					return struct{}{}, x.Name == "fmt" && sel.Sel.Name == "Printf"
				}
			}
			return struct{}{}, false
		})
		require.NoError(t, err)
		require.NoError(t, modifier.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)
		// Each function should only be called once
		assert.Equal(t, 1, countFunctionCalls(t, modifiedSrc, "getFormat"))
		assert.Equal(t, 2, countFunctionCalls(t, modifiedSrc, "getArg"))
		code := string(modifiedSrc)
		assert.Contains(t, code, "lenSyntheticArg1_0 := getFormat()")
		assert.Contains(t, code, "lenSyntheticArg1_1 := getArg()")
		assert.Contains(t, code, "lenSyntheticArg1_2 := getArg()")
		assert.Contains(t, code, "fmt.Printf(lenSyntheticArg1_0, lenSyntheticArg1_1, lenSyntheticArg1_2)")
	})

	t.Run("method_chaining_side_effects", func(t *testing.T) {
		t.Parallel()

		src := `package testpkg

var counter int

type Builder struct {
	value int
}

func (b *Builder) Add(n int) *Builder {
	b.value += n
	return b
}

func (b *Builder) Build() int {
	return b.value
}

func getBuilder() *Builder {
	counter++
	return &Builder{}
}

func getValue() int {
	counter++
	return counter
}

func ProcessData() int {
	return getBuilder().Add(getValue()).Build()
}
`

		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0o644))

		modifier := &ASTModifier{}
		fn := Function{
			FunctionIdent: "testpkg:ProcessData",
			FunctionName:  "ProcessData",
			PackageName:   "testpkg",
			FilePath:      filePath,
		}

		_, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
			if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
				return struct{}{}, sel.Sel.Name == "Add"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)
		require.NoError(t, modifier.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)
		// Each function should only be called once
		assert.Equal(t, 1, countFunctionCalls(t, modifiedSrc, "getBuilder"))
		assert.Equal(t, 1, countFunctionCalls(t, modifiedSrc, "getValue"))
		code := string(modifiedSrc)
		// Receiver (getBuilder()) should be evaluated once
		assert.Contains(t, code, "lenSyntheticRecv1 := getBuilder()")
		// Argument (getValue()) should be evaluated once
		assert.Contains(t, code, "lenSyntheticArg1_0 := getValue()")
		assert.Contains(t, code, "lenSyntheticRecv1.Add(lenSyntheticArg1_0)")
	})
}

func TestInjectFuncPointBeforeCallReceiverCapture(t *testing.T) {
	t.Parallel()

	const testMethodDoWork = "DoWork"

	testCases := []struct {
		name             string
		src              string
		funcName         string
		predicate        func(*ast.CallExpr) (any, bool)
		expectedReceiver string // Expected receiver name in snapshots
		expectSynthetic  bool   // Whether to expect synthetic receiver
		verify           func(*testing.T, []byte)
	}{
		{
			name: "simple_receiver",
			src: `package testpkg

type MyStruct struct {
	Value int
}

func (m *MyStruct) DoWork() {}

func ProcessData() {
	obj := &MyStruct{Value: 42}
	obj.DoWork()
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					return struct{}{}, sel.Sel.Name == testMethodDoWork
				}
				return struct{}{}, false
			},
			expectedReceiver: "obj",
			expectSynthetic:  false,
		},
		{
			name: "complex_receiver",
			src: `package testpkg

type MyStruct struct {
	Value int
}

func (m *MyStruct) DoWork() {}

func ProcessData() {
	(&MyStruct{Value: 42}).DoWork()
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					return struct{}{}, sel.Sel.Name == testMethodDoWork
				}
				return struct{}{}, false
			},
			expectedReceiver: "recv",
			expectSynthetic:  true,
		},
		{
			name: "method_with_args",
			src: `package testpkg

type MyStruct struct {
	Value int
}

func (m *MyStruct) Process(x, y int) {}

func ProcessData() {
	obj := &MyStruct{Value: 10}
	obj.Process(1, 2)
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					return struct{}{}, sel.Sel.Name == "Process"
				}
				return struct{}{}, false
			},
			expectedReceiver: "obj",
			expectSynthetic:  false,
		},
		{
			name: "chained_receiver",
			src: `package testpkg

type Inner struct {
	Value int
}

func (i *Inner) DoWork() {}

type Outer struct {
	Inner *Inner
}

func ProcessData() {
	outer := &Outer{Inner: &Inner{Value: 5}}
	outer.Inner.DoWork()
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					return struct{}{}, sel.Sel.Name == testMethodDoWork
				}
				return struct{}{}, false
			},
			expectedReceiver: "recv",
			expectSynthetic:  true,
		},
		{
			name: "dot_import_package_function",
			src: `package testpkg
import . "strings"

func ProcessData() {
	// ToUpper is from dot-imported "strings" package
	// Should NOT be captured as receiver since it's a package function
	result := ToUpper("test")
	_ = result
}`,
			funcName: "ProcessData",
			predicate: func(call *ast.CallExpr) (any, bool) {
				// Match calls to ToUpper (from dot-imported strings package)
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == "ToUpper"
				}
				return struct{}{}, false
			},
			expectedReceiver: "", // No receiver should be captured for package functions
			expectSynthetic:  false,
		},
		{
			name: "receiver_side_effect_single_eval",
			src: `package testpkg

var counter int

type MyStruct struct{}

func makeStruct() *MyStruct {
	counter++
	return &MyStruct{}
}

func (m *MyStruct) DoWork() {}

func Process() {
	makeStruct().DoWork()
}
`,
			funcName: "Process",
			predicate: func(call *ast.CallExpr) (any, bool) {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					return struct{}{}, sel.Sel.Name == "DoWork"
				}
				return struct{}{}, false
			},
			expectedReceiver: "recv",
			expectSynthetic:  true,
			verify: func(t *testing.T, src []byte) {
				t.Helper()

				assert.Equal(t, 1, countFunctionCalls(t, src, "makeStruct"))
				code := string(src)
				assert.Contains(t, code, "lenSyntheticRecv1 := makeStruct()")
				assert.Contains(t, code, "lenSyntheticRecv1.DoWork()")
			},
		},
	}

	const monitorFuncName = sendLensPointStateMessageFunc
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			filePath := filepath.Join(dir, "test.go")
			require.NoError(t, os.WriteFile(filePath, []byte(tc.src), 0o644))

			modifier := &ASTModifier{}
			fn := Function{
				FunctionIdent: "testpkg:" + tc.funcName,
				FunctionName:  tc.funcName,
				PackageName:   "testpkg",
				FilePath:      filePath,
			}

			pointMap, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Len(t, pointMap, 1)

			require.NoError(t, modifier.CommitFile(filePath))

			// Read and parse modified file
			modifiedSrc, err := os.ReadFile(filePath)
			require.NoError(t, err)
			modifiedStr := string(modifiedSrc)

			// Verify monitoring call was inserted
			assert.Contains(t, modifiedStr, monitorFuncName)

			if tc.verify != nil {
				tc.verify(t, modifiedSrc)
			}

			// If synthetic receiver expected, verify assignment was created
			if tc.expectSynthetic {
				assert.Contains(t, modifiedStr, syntheticFieldNamePrefixReceiver+"1 := ")
			}

			fset := token.NewFileSet()
			modFile, err := parser.ParseFile(fset, filePath, nil, 0)
			require.NoError(t, err)

			// Find the monitoring call and verify receiver capture
			var foundMonitoringCall bool
			ast.Inspect(modFile, func(n ast.Node) bool {
				if call, ok := n.(*ast.CallExpr); ok {
					if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == monitorFuncName {
						foundMonitoringCall = true

						// First argument is always point ID
						require.GreaterOrEqual(t, len(call.Args), 1)

						if tc.expectedReceiver != "" {
							// When receiver is expected, verify it's captured
							require.GreaterOrEqual(t, len(call.Args), 2)

							// Format the receiver snapshot
							var buf bytes.Buffer
							err := format.Node(&buf, token.NewFileSet(), call.Args[1])
							require.NoError(t, err)
							receiverSnapshot := buf.String()

							// Verify receiver name appears in snapshot
							assert.Contains(t, receiverSnapshot, tc.expectedReceiver)
						} else {
							// When no receiver expected (dot import, package function),
							// verify the first snapshot (if any) is NOT a receiver but an argument
							var buf bytes.Buffer
							err := format.Node(&buf, token.NewFileSet(), call.Args[1])
							require.NoError(t, err)
							firstSnapshot := buf.String()

							// Should be arg0, not a receiver
							assert.Contains(t, firstSnapshot, "arg0")
						}

						return false
					}
				}
				return true
			})

			assert.True(t, foundMonitoringCall)
		})
	}
}

func TestBuildCallInstrumentationWithReceiver(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name             string
		callExpr         string
		expectedReceiver string // Empty if no receiver expected
		expectSynthetic  bool
	}{
		{
			name:             "simple_receiver",
			callExpr:         "obj.Method(x, y)",
			expectedReceiver: "obj",
			expectSynthetic:  false,
		},
		{
			name:             "package_function",
			callExpr:         "pkg.Function(x, y)",
			expectedReceiver: "",
			expectSynthetic:  false,
		},
		{
			name:             "no_receiver",
			callExpr:         "Function(x, y)",
			expectedReceiver: "",
			expectSynthetic:  false,
		},
		{
			name:             "complex_receiver",
			callExpr:         "getObj().Method(x)",
			expectedReceiver: "recv",
			expectSynthetic:  true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			call, err := parser.ParseExpr(tc.callExpr)
			require.NoError(t, err)
			callExpr, ok := call.(*ast.CallExpr)
			require.True(t, ok)

			var buf bytes.Buffer
			stmts, err := buildCallInstrumentationWithArgs(&buf, 99, callExpr, nil)
			require.NoError(t, err)
			require.NotEmpty(t, stmts)

			// All test cases have arguments, so expect assignments plus send statement
			blk := &ast.BlockStmt{List: stmts}
			require.GreaterOrEqual(t, len(blk.List), 1)

			// If synthetic receiver expected, verify the receiver assignment
			if tc.expectSynthetic {
				require.GreaterOrEqual(t, len(blk.List), 2)
				// First statement should be receiver assignment
				assign, ok := blk.List[0].(*ast.AssignStmt)
				require.True(t, ok)
				require.Len(t, assign.Lhs, 1)
				ident, ok := assign.Lhs[0].(*ast.Ident)
				require.True(t, ok)
				assert.Contains(t, ident.Name, syntheticFieldNamePrefixReceiver)
			}

			// Extract the monitoring call from the last statement
			exprStmt, ok := blk.List[len(blk.List)-1].(*ast.ExprStmt)
			require.True(t, ok)
			monitorCall, ok := exprStmt.X.(*ast.CallExpr)
			require.True(t, ok)

			// Verify function name
			funIdent, ok := monitorCall.Fun.(*ast.Ident)
			require.True(t, ok)
			assert.Equal(t, sendLensPointStateMessageFunc, funIdent.Name)

			// Count snapshots (excluding point ID)
			snapshotCount := len(monitorCall.Args) - 1

			if tc.expectedReceiver != "" {
				// Should have receiver + arguments
				require.GreaterOrEqual(t, snapshotCount, 1)

				// First snapshot should be receiver
				composite, ok := monitorCall.Args[1].(*ast.CompositeLit)
				require.True(t, ok)

				// Extract Name field
				var receiverName string
				for _, elt := range composite.Elts {
					kv, ok := elt.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					keyIdent, ok := kv.Key.(*ast.Ident)
					if !ok || keyIdent.Name != fieldKeyName {
						continue
					}
					namelit, ok := kv.Value.(*ast.BasicLit)
					require.True(t, ok)
					receiverName, err = strconv.Unquote(namelit.Value)
					require.NoError(t, err)
					break
				}

				assert.Equal(t, tc.expectedReceiver, receiverName)
			}
		})
	}
}

func TestMakeSnapshotLitWithReceiverPrefix(t *testing.T) {
	t.Parallel()

	snapshot := makeSnapshotLit("lenSyntheticRecv0", ast.NewIdent("value"))

	composite, ok := snapshot.(*ast.CompositeLit)
	require.True(t, ok)

	var nameValue string
	for _, elt := range composite.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		keyIdent, ok := kv.Key.(*ast.Ident)
		if !ok || keyIdent.Name != fieldKeyName {
			continue
		}
		namelit, ok := kv.Value.(*ast.BasicLit)
		require.True(t, ok)
		var err error
		nameValue, err = strconv.Unquote(namelit.Value)
		require.NoError(t, err)
		break
	}

	assert.Equal(t, "recv0", nameValue)
}

func TestZeroValueForType(t *testing.T) {
	tests := []struct {
		name     string
		typeExpr string
		expected string
	}{
		{"int", "int", "0"},
		{"int8", "int8", "0"},
		{"int16", "int16", "0"},
		{"int32", "int32", "0"},
		{"int64", "int64", "0"},
		{"uint", "uint", "0"},
		{"uint8", "uint8", "0"},
		{"uint16", "uint16", "0"},
		{"uint32", "uint32", "0"},
		{"uint64", "uint64", "0"},
		{"uintptr", "uintptr", "0"},
		{"float32", "float32", "0"},
		{"float64", "float64", "0"},
		{"complex64", "complex64", "0"},
		{"complex128", "complex128", "0"},
		{"byte", "byte", "0"},
		{"rune", "rune", "0"},
		{"bool", "bool", "false"},
		{"string", "string", `""`},
		{"error", "error", "nil"},
		{"pointer", "*int", "nil"},
		{"slice", "[]int", "nil"},
		{"map", "map[string]int", "nil"},
		{"channel", "chan int", "nil"},
		{"interface", "interface{}", "nil"},
		{"struct", "struct{}", "struct{}{}"},
		{"array", "[5]int", "[5]int{}"},
		{"generic_single", "Optional[int]", "*new(Optional[int])"},
		{"generic_multi", "Map[string, int]", "*new(Map[string, int])"},
		{"func_type", "func(int) string", "nil"},
		{"named_type", "MyType", "MyType{}"},
		{"selector_type", "pkg.Type", "pkg.Type{}"},
		{"pointer_to_struct", "*struct{}", "nil"},
		{"slice_of_pointers", "[]*int", "nil"},
		{"map_with_pointer_value", "map[string]*int", "nil"},
		{"chan_send", "chan<- int", "nil"},
		{"chan_recv", "<-chan int", "nil"},
		{"array_of_arrays", "[3][4]int", "[3][4]int{}"},
		{"slice_of_slices", "[][]string", "nil"},
		{"interface_with_methods", "interface{ String() string }", "nil"},
		{"func_with_multiple_returns", "func(int) (string, error)", "nil"},
		{"variadic_func", "func(...int) string", "nil"},
		{"blank_identifier", "_", "nil"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			fset := token.NewFileSet()
			expr, err := parser.ParseExpr(tt.typeExpr)
			require.NoError(t, err)

			var buf bytes.Buffer
			zeroVal, err := zeroValueForType(&buf, expr)
			require.NoError(t, err)

			var resultBuf bytes.Buffer
			err = printer.Fprint(&resultBuf, fset, zeroVal)
			require.NoError(t, err)
			assert.Equal(t, tt.expected, resultBuf.String())
		})
	}
}

func TestDeferGoInlineFunctionWrapping(t *testing.T) {
	tests := []struct {
		name          string
		source        string
		containsDefer bool
		containsGo    bool
	}{
		{
			name: "defer_with_instrumentation",
			source: `package test
func foo() {
	defer bar(1, 2)
}
func bar(a, b int) {}`,
			containsDefer: true,
		},
		{
			name: "go_with_instrumentation",
			source: `package test
func foo() {
	go bar(1, 2)
}
func bar(a, b int) {}`,
			containsGo: true,
		},
		{
			name: "defer_with_complex_args",
			source: `package test
func getVal() int { return 5 }
func foo() {
	defer bar(getVal())
}
func bar(a int) {}`,
			containsDefer: true,
		},
		{
			name: "go_with_complex_args",
			source: `package test
func getVal() int { return 5 }
func foo() {
	go bar(getVal())
}
func bar(a int) {}`,
			containsGo: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			dir := t.TempDir()
			filePath := filepath.Join(dir, "test.go")
			err := os.WriteFile(filePath, []byte(tt.source), 0o644)
			require.NoError(t, err)

			modifier := &ASTModifier{}
			fn := Function{
				FunctionIdent: "test:bar",
				FunctionName:  "bar",
				PackageName:   "test",
				FilePath:      filePath,
			}

			_, err = modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == "bar" {
					return "test", true
				}
				return nil, false
			})
			require.NoError(t, err)

			err = modifier.CommitFile(filePath)
			require.NoError(t, err)

			modifiedSrc, err := os.ReadFile(filePath)
			require.NoError(t, err)
			modifiedStr := string(modifiedSrc)

			if tt.containsDefer {
				assert.Contains(t, modifiedStr, "defer")
			}
			if tt.containsGo {
				assert.Contains(t, modifiedStr, "go")
			}
		})
	}
}

func TestFuncLitInstrumentation(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name           string
		src            string
		expectedPoints int
		description    string
		funcName       string // optional, defaults to "Outer"
		targetFunc     string // optional, defaults to "Target"
	}{
		{
			name: "callback_assignment",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	callback := func(x int) {
		Target(x)
	}
	_ = callback
}`,
			expectedPoints: 1,
			description:    "Target(x) inside FuncLit should be instrumented",
		},
		{
			name: "iife",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	func() {
		Target(1)
	}()
}`,
			expectedPoints: 1,
			description:    "Target() inside IIFE should be instrumented",
		},
		{
			name: "funclit_as_argument",
			src: `package testpkg

func Target(x int) {}
func Process(f func(int)) {}

func Outer() {
	Process(func(x int) {
		Target(x)
	})
}`,
			expectedPoints: 1,
			description:    "Target() inside FuncLit argument should be instrumented",
		},
		{
			name: "nested_funclit",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	outer := func() {
		inner := func() {
			Target(1)
		}
		_ = inner
	}
	_ = outer
}`,
			expectedPoints: 1,
			description:    "Target() in nested FuncLit should be instrumented",
		},
		{
			name: "defer_with_existing_funclit",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	defer func() {
		Target(1)
	}()
}`,
			expectedPoints: 1,
			description:    "Target() inside deferred FuncLit should be instrumented",
		},
		{
			name: "go_with_existing_funclit",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	go func() {
		Target(1)
	}()
}`,
			expectedPoints: 1,
			description:    "Target() inside goroutine FuncLit should be instrumented",
		},
		{
			name: "funclit_with_params_not_extracted",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	callback := func(va int, vb string) {
		Target(va)
	}
	_ = callback
}`,
			expectedPoints: 1,
			description:    "FuncLit params (va, vb) should NOT be extracted outside the FuncLit",
		},
		{
			name: "multiple_funclits",
			src: `package testpkg

func Target(x int) {}

func Outer() {
	f1 := func() { Target(1) }
	f2 := func() { Target(2) }
	_ = f1
	_ = f2
}`,
			expectedPoints: 2,
			description:    "Both FuncLits should have Target() instrumented",
		},
		{
			name: "defer_with_funclit_arg_containing_target",
			src: `package testpkg

func Target(x int) int { return x }

func Outer() {
	defer Target(func() int { return Target(1) }())
}`,
			expectedPoints: 2,
			description:    "Both outer Target and inner Target inside FuncLit arg should be instrumented",
		},
		{
			name: "go_with_funclit_arg_containing_target",
			src: `package testpkg

func Target(x int) int { return x }

func Outer() {
	go Target(func() int { return Target(1) }())
}`,
			expectedPoints: 2,
			description:    "Both outer Target and inner Target inside FuncLit arg should be instrumented",
		},
		{
			name: "struct_field_funclit_protobuf_pattern",
			src: `package testpkg

type pointer int
type coderFieldInfo struct {
	funcs coderFuncs
}
type coderFuncs struct {
	merge func(dst, src pointer, info *coderFieldInfo)
}

func Target(dst, src pointer, info *coderFieldInfo) {}

func Setup(first *coderFieldInfo) {
	first.funcs.merge = func(dst, src pointer, info *coderFieldInfo) {
		Target(dst, src, info)
	}
}`,
			expectedPoints: 1,
			description:    "Protobuf-like pattern: Target inside struct field FuncLit should be instrumented in correct scope",
			funcName:       "Setup",
		},
		{
			name: "k8s_marshal_pattern",
			src: `package testpkg

type MarshalOptions struct{}
type Encoder struct{}
type addressableValue struct{}
type fncs struct {
	marshal func(mo MarshalOptions, enc *Encoder, va addressableValue) error
}

func targetCall(va addressableValue) error { return nil }

func Setup() {
	var f fncs
	f.marshal = func(mo MarshalOptions, enc *Encoder, va addressableValue) error {
		return targetCall(va)
	}
	_ = f
}`,
			expectedPoints: 1,
			description:    "K8s-like pattern: targetCall inside marshal FuncLit should be instrumented in correct scope",
			funcName:       "Setup",
			targetFunc:     "targetCall",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			filePath := filepath.Join(dir, "test.go")
			require.NoError(t, os.WriteFile(filePath, []byte(tc.src), 0o644))

			// Use defaults if not specified
			funcName := tc.funcName
			if funcName == "" {
				funcName = "Outer"
			}
			targetFunc := tc.targetFunc
			if targetFunc == "" {
				targetFunc = "Target"
			}

			modifier := &ASTModifier{}
			fn := Function{
				FunctionIdent: "testpkg:" + funcName,
				FunctionName:  funcName,
				PackageName:   "testpkg",
				FilePath:      filePath,
			}

			// Only match target function calls
			pointMap, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) (any, bool) {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return struct{}{}, ident.Name == targetFunc
				}
				return struct{}{}, false
			})
			require.NoError(t, err, tc.description)
			assert.Len(t, pointMap, tc.expectedPoints, tc.description)

			require.NoError(t, modifier.CommitFile(filePath))

			modifiedSrc, err := os.ReadFile(filePath)
			require.NoError(t, err)
			modifiedStr := string(modifiedSrc)

			// Verify the monitoring call was inserted
			assert.Contains(t, modifiedStr, sendLensPointStateMessageFunc)

			// Verify the code compiles
			fset := token.NewFileSet()
			_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.AllErrors)
			require.NoError(t, err)

			// For the "funclit_with_params_not_extracted" test, verify that
			// the FuncLit params are NOT extracted outside the FuncLit
			if tc.name == "funclit_with_params_not_extracted" {
				// The instrumentation should be INSIDE the func literal, not before the assignment
				// Check that we don't have lenSyntheticArg with va/vb value before the callback assignment
				lines := strings.Split(modifiedStr, "\n")
				for i, line := range lines {
					if strings.Contains(line, "callback :=") {
						// The previous non-empty lines should NOT contain extraction of va or vb
						for j := i - 1; j >= 0 && j > i-5; j-- {
							if strings.TrimSpace(lines[j]) != "" {
								assert.NotContains(t, lines[j], "va")
								assert.NotContains(t, lines[j], "vb")
							}
						}
						break
					}
				}
			}
		})
	}
}

func TestZeroValue(t *testing.T) {
	t.Parallel()

	t.Run("package_conflict", func(t *testing.T) {
		src := `package test
import "math"

// math is a type that conflicts with the package name
type math int

func GetMath() (math, error) {
	_ = math.Pi // using the package
	if true {
		return 42, nil
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "GetMath" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:GetMath",
					FunctionName:  "GetMath",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		// Read modified file and compile-check
		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should compile without "math is not a type" error
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)

		// Should have added a return statement
		assert.Contains(t, outputStr, "return")
	})

	t.Run("blank_identifier", func(t *testing.T) {
		src := `package test

func ProcessData() (_ int, err error) {
	if true {
		return 42, nil
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "ProcessData" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:ProcessData",
					FunctionName:  "ProcessData",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should not contain "return _" (which would be invalid)
		assert.NotContains(t, outputStr, "return _")

		// Should compile
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)
	})

	t.Run("interface_type", func(t *testing.T) {
		src := `package test
import "math"

// math is an interface that conflicts with the package name
type math interface {
	Calculate() float64
}

func GetInterface() math {
	_ = math.Pi // using the package
	if true {
		return nil
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "GetInterface" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:GetInterface",
					FunctionName:  "GetInterface",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should compile
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)
	})

	t.Run("all_blank_identifiers", func(t *testing.T) {
		src := `package test

func ProcessBoth() (_ int, _ error) {
	if true {
		return 42, nil
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "ProcessBoth" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:ProcessBoth",
					FunctionName:  "ProcessBoth",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should not contain "return _" (which would be invalid)
		assert.NotContains(t, outputStr, "return _")
		// Should contain naked return
		assert.Contains(t, outputStr, "return")

		// Should compile
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)
	})

	t.Run("mixed_blank_named_unnamed", func(t *testing.T) {
		src := `package test

func GetComplex() (_ int, name string, err error) {
	if true {
		return 1, "test", nil
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "GetComplex" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:GetComplex",
					FunctionName:  "GetComplex",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should not contain "return _" (which would be invalid)
		assert.NotContains(t, outputStr, "return _")
		// Should use named variable for "name"
		assert.Contains(t, outputStr, "name")

		// Should compile
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)
	})

	t.Run("single_blank_identifier", func(t *testing.T) {
		src := `package test

func GetBlank() (_ string) {
	if true {
		return "test"
	}
}
`
		tmpDir := t.TempDir()
		testFile := filepath.Join(tmpDir, "test.go")
		err := os.WriteFile(testFile, []byte(src), 0644)
		require.NoError(t, err)

		// Parse
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, testFile, src, 0)
		require.NoError(t, err)

		// Create modifier and inject
		modifier := &ASTModifier{}
		for _, decl := range file.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "GetBlank" {
				funcInfo := &Function{
					FilePath:      testFile,
					PackageName:   "test",
					FunctionIdent: "test:GetBlank",
					FunctionName:  "GetBlank",
				}
				_, err := modifier.InjectFuncPointReturnStates(funcInfo)
				require.NoError(t, err)
				break
			}
		}

		output, err := os.ReadFile(testFile)
		require.NoError(t, err)
		outputStr := string(output)

		// Should not contain "return _" (which would be invalid)
		assert.NotContains(t, outputStr, "return _")
		// Should have a return statement
		assert.Contains(t, outputStr, "return")

		// Should compile
		_, err = parser.ParseFile(fset, "test.go", outputStr, 0)
		require.NoError(t, err)
	})
}

func TestInjectASTClient(t *testing.T) {
	t.Parallel()

	t.Run("basic_injection", func(t *testing.T) {
		dir := t.TempDir()
		src := `package testpkg

func Foo() int {
	return 42
}
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "test.go"), []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		// Verify client file was created
		_, err = os.Stat(filepath.Join(dir, "xx_lens_client_gen.go"))
		require.NoError(t, err)

		// Verify API file was created
		_, err = os.Stat(filepath.Join(dir, "xx_lens_api_gen.go"))
		require.NoError(t, err)
	})

	t.Run("skip_already_injected", func(t *testing.T) {
		dir := t.TempDir()
		src := `package testpkg

func Foo() int {
	return 42
}
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "test.go"), []byte(src), 0644))

		mod := &ASTModifier{}

		// First injection
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		// Second injection should be skipped (no error)
		err = mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)
	})

	// Dot-import symbol collision bug
	// When package A dot-imports package B, and both have lens client files injected,
	// the exported symbols (SendLensPointMessage, etc.) collide.
	t.Run("dot_import_symbol_collision", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()
		pkgADir := filepath.Join(dir, "pkga")
		pkgBDir := filepath.Join(dir, "pkgb")

		require.NoError(t, os.MkdirAll(pkgADir, 0755))
		require.NoError(t, os.MkdirAll(pkgBDir, 0755))

		// Package B - a simple package
		pkgBSrc := `package pkgb

func DoSomething() string {
	return "hello"
}
`
		require.NoError(t, os.WriteFile(filepath.Join(pkgBDir, "pkgb.go"), []byte(pkgBSrc), 0644))

		// Package A - dot-imports Package B
		pkgASrc := `package pkga

import . "example.com/test/pkgb"

func UseIt() string {
	return DoSomething()
}
`
		require.NoError(t, os.WriteFile(filepath.Join(pkgADir, "pkga.go"), []byte(pkgASrc), 0644))

		// Create go.mod at root
		goMod := `module example.com/test

go 1.21
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		mod := &ASTModifier{}

		// Inject into pkgB (no error expected)
		err := mod.InjectASTClient(pkgBDir, 8448, 20, 1024)
		require.NoError(t, err)

		// Inject into pkgA (should detect conflict and handle it)
		err = mod.InjectASTClient(pkgADir, 8448, 20, 1024)
		require.NoError(t, err)

		// Verify both packages have injected files
		_, err = os.Stat(filepath.Join(pkgBDir, "xx_lens_client_gen.go"))
		require.NoError(t, err)
		_, err = os.Stat(filepath.Join(pkgADir, "xx_lens_client_gen.go"))
		require.NoError(t, err)

		cmd := exec.Command("go", "build", "./...")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()

		outputStr := string(output)
		if strings.Contains(outputStr, "already declared through dot-import") ||
			strings.Contains(outputStr, "sendLensPointMessage") {
			t.Errorf("Dot-import symbol collision.\nBuild output:\n%s", outputStr)
		}
		require.NoError(t, err, "Build failed with different error: %s", outputStr)
	})

	t.Run("go_version_injection", func(t *testing.T) {
		dir := t.TempDir()

		// Create go.mod with Go 1.18 (above minimum)
		goMod := `module newmodule
go 1.18
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		// Create a simple Go file
		src := `package newmodule

func Hello() string {
	return "hello"
}
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)

		// Should succeed
		require.NoError(t, err)

		// Verify files were created
		_, err = os.Stat(filepath.Join(dir, "xx_lens_client_gen.go"))
		require.NoError(t, err)
	})
}

func TestInjectFuncPointEntry(t *testing.T) {
	t.Parallel()

	t.Run("basic_injection", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		src := `package testpkg

func Foo() int {
	return 42
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Foo",
			FunctionName:  "Foo",
		}

		pointID, err := mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)
		assert.Positive(t, pointID)
	})

	t.Run("method_injection", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		src := `package testpkg

type MyType struct{}

func (m *MyType) Method() int {
	return 42
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:*MyType.Method",
			FunctionName:  "Method",
		}

		pointID, err := mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)
		assert.Positive(t, pointID)
	})

	t.Run("multiline_call", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source with a multi-line function call - arguments on separate lines
		src := `package testpkg

func target(a, b, c, d int) int {
	return a + b + c + d
}

func getValue() int {
	return 42
}

func Process() int {
	return target(
		1,
		getValue(),
		3,
		4,
	)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
		}

		// Inject instrumentation before the target call
		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "target"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		code := string(modifiedSrc)
		assert.Contains(t, code, "sendLensPointStateMessage")
		assert.Contains(t, code, "lenSyntheticArg")

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("composite_literal", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source with composite literal arguments spanning multiple lines
		src := `package testpkg

type Config struct {
	A int
	B string
	C float64
}

func target(cfg Config, x int) int {
	return cfg.A + x
}

func Process() int {
	return target(Config{
		A: 1,
		B: "test",
		C: 3.14,
	}, 42)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
		}

		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "target"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("nested_calls", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source mimicking complex CGo patterns with nested calls
		src := `package testpkg

func outer(a, b, c int) int {
	return a + b + c
}

func inner1() int { return 1 }
func inner2() int { return 2 }
func inner3() int { return 3 }

func Process() int {
	return outer(
		inner1(),
		inner2(),
		inner3(),
	)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
		}

		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "outer"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("cgo_style", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source mimicking CGo patterns - arguments on same line with different position info
		src := `package testpkg

func ccgoCall(a, b, c, d, e, f, g int) int { return a }

func Process() int {
	return ccgoCall(1, 2, 3,
		4, 5, 6,
		7)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
		}

		_, err = mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("no_trailing_comma", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Multi-line call where closing paren is on same line as last arg (no trailing comma needed)
		// But internal lines have arguments without trailing commas
		src := `package testpkg

func multiArg(a, b, c int) int { return a + b + c }

func Process() int {
	return multiArg(
		1,
		2,
		3)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:Process",
			FunctionName:  "Process",
		}

		_, err = mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("multiple_functions", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source with multiple functions containing multi-line calls
		src := `package testpkg

func helper(a, b, c int) int { return a + b + c }

func Func1() int {
	return helper(
		1,
		2,
		3,
	)
}

func Func2() int {
	return helper(
		4,
		5,
		6,
	)
}

func Func3() int {
	return helper(
		7,
		8,
		9,
	)
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		// Modify multiple functions in sequence (like module handling does)
		functions := []string{"Func1", "Func2", "Func3"}
		for _, fnName := range functions {
			fn := &Function{
				FilePath:      filePath,
				PackageName:   "testpkg",
				FunctionIdent: "testpkg:" + fnName,
				FunctionName:  fnName,
			}

			_, err = mod.InjectFuncPointEntry(fn)
			require.NoError(t, err)

			_, err = mod.InjectFuncPointPanic(fn)
			require.NoError(t, err)
		}

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		assert.Equal(t, 3, countFunctionCalls(t, modifiedSrc, "sendLensPointMessage"))

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("snapshot_multiline", func(t *testing.T) {
		// Parse a multi-line expression to get position info
		src := `package test

func foo() {
	x := Config{
		A: 1,
		B: "test",
		C: 3.14,
	}
	_ = x
}
`
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, "test.go", src, 0)
		require.NoError(t, err)

		// Find the composite literal
		var compositeLit *ast.CompositeLit
		ast.Inspect(file, func(n ast.Node) bool {
			if cl, ok := n.(*ast.CompositeLit); ok {
				compositeLit = cl
				return false
			}
			return true
		})
		require.NotNil(t, compositeLit)

		snapshot := makeSnapshotLit("x", compositeLit)

		var buf bytes.Buffer
		err = format.Node(&buf, token.NewFileSet(), snapshot)
		require.NoError(t, err)
	})

	t.Run("cgo_transpiled", func(t *testing.T) {
		dir := t.TempDir()
		filePath := filepath.Join(dir, "test.go")
		// Source mimicking CGo-transpiled code with very long complex expressions
		src := `package testpkg

import "unsafe"

type TDateTime struct {
	FiJD     int64
	FvalidJD int8
}

func helper(a, b, c, d, e, f, g int) int { return a }

func _clearYMD_HMS_TZ(p uintptr) {}
func _sqlite3StmtCurrentTime(context uintptr) int64 { return 0 }

func _setDateTimeToCurrent(context uintptr, p uintptr) (r int32) {
	(*TDateTime)(unsafe.Pointer(p)).FiJD = _sqlite3StmtCurrentTime(context)
	if (*TDateTime)(unsafe.Pointer(p)).FiJD > 0 {
		(*TDateTime)(unsafe.Pointer(p)).FvalidJD = int8(1)
		helper(int((*TDateTime)(unsafe.Pointer(p)).FiJD), 1, 3, 0x8, int((*TDateTime)(unsafe.Pointer(p)).FvalidJD), 4, 0x10)
		_clearYMD_HMS_TZ(p)
		return 0
	} else {
		return int32(1)
	}
	return r
}
`
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:_setDateTimeToCurrent",
			FunctionName:  "_setDateTimeToCurrent",
		}

		_, err = mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)

		_, err = mod.InjectFuncPointPanic(fn)
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, 0)
		require.NoError(t, err)
	})

	t.Run("assembly_only_function", func(t *testing.T) {
		dir := t.TempDir()

		// Go file with assembly-only function (no body, like golang.org/x/crypto/sha3:keccakF1600)
		asmSrc := `package testpkg

//go:noescape
func keccakF1600(state *[25]uint64)
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "asm.go"), []byte(asmSrc), 0644))

		// Need a non-assembly file for detectPackageName
		normalSrc := `package testpkg

func NormalFunc() int {
	return 42
}
`
		require.NoError(t, os.WriteFile(filepath.Join(dir, "normal.go"), []byte(normalSrc), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filepath.Join(dir, "asm.go"),
			PackageName:   "testpkg",
			FunctionIdent: "testpkg:keccakF1600",
			FunctionName:  "keccakF1600",
		}

		// Try to inject - this should fail with ErrNoFunctionBody
		_, err = mod.InjectFuncPointEntry(fn)
		require.Error(t, err)
		assert.True(t, IsNormalAstError(err))
		assert.ErrorIs(t, err, ErrNoFunctionBody)
	})
}

// TestCompilerDirectivePreservation verifies that compiler directives (//go:embed, //go:noinline, etc.)
// remain correctly positioned after AST modification and commit.
// This is a regression test for the fresh FileSet change in loadParsedFileNode.
func TestCompilerDirectivePreservation(t *testing.T) {
	t.Parallel()

	t.Run("go_embed_directive", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()

		// Create go.mod
		goMod := testGoMod
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		// Create a file to embed
		require.NoError(t, os.WriteFile(filepath.Join(dir, "data.txt"), []byte("hello"), 0644))

		// Create source with //go:embed directive - directive must be immediately before var
		src := `package testmod

import _ "embed"

//go:embed data.txt
var content string

func GetContent() string {
	return content
}
`
		filePath := filepath.Join(dir, "main.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testmod",
			FunctionIdent: "testmod:GetContent",
			FunctionName:  "GetContent",
		}

		// Inject instrumentation
		pointID, err := mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)
		assert.Positive(t, pointID)

		// Commit the modified file
		require.NoError(t, mod.CommitFile(filePath))

		// Read the modified file
		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		// Verify the file still parses
		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.ParseComments)
		require.NoError(t, err, "Modified file should parse: %s", string(modifiedSrc))

		// Verify the file compiles (catches "misplaced compiler directive" errors)
		cmd := exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Build failed with: %s\n\nModified source:\n%s", string(output), string(modifiedSrc))
	})

	t.Run("go_noinline_directive", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()

		// Create go.mod
		goMod := testGoMod
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		// Create source with //go:noinline directive
		src := `package testmod

//go:noinline
func NoInlineFunc() int {
	return 42
}

func Caller() int {
	return NoInlineFunc()
}
`
		filePath := filepath.Join(dir, "main.go")
		require.NoError(t, os.WriteFile(filePath, []byte(src), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testmod",
			FunctionIdent: "testmod:Caller",
			FunctionName:  "Caller",
		}

		// Inject instrumentation into Caller (not NoInlineFunc)
		pointID, err := mod.InjectFuncPointEntry(fn)
		require.NoError(t, err)
		assert.Positive(t, pointID)

		// Commit the modified file
		require.NoError(t, mod.CommitFile(filePath))

		// Read the modified file
		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		// Verify the file still parses
		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.ParseComments)
		require.NoError(t, err, "Modified file should parse: %s", string(modifiedSrc))

		// Verify the directive is on the line immediately before the function
		lines := strings.Split(string(modifiedSrc), "\n")
		foundDirective := false
		for i, line := range lines {
			if strings.TrimSpace(line) == "//go:noinline" {
				foundDirective = true
				// Next non-empty line should be the func declaration
				for j := i + 1; j < len(lines); j++ {
					nextLine := strings.TrimSpace(lines[j])
					if nextLine == "" {
						continue
					}
					assert.True(t, strings.HasPrefix(nextLine, "func NoInlineFunc"),
						"//go:noinline should be immediately before func NoInlineFunc, but found: %s", nextLine)
					break
				}
			}
		}
		assert.True(t, foundDirective)

		// Verify the file compiles
		cmd := exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Build failed with: %s\n\nModified source:\n%s", string(output), string(modifiedSrc))
	})
}

// TestImportedTypeCompositeLiteral verifies that composite literals with imported package types
// are handled correctly during AST modification. This is a regression test for the
// "images.Image is not a type" error.
func TestImportedTypeCompositeLiteral(t *testing.T) {
	t.Parallel()

	t.Run("imported_type_literal", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()

		// Create go.mod
		goMod := testGoMod
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		// Create a separate package with types to import
		typesDir := filepath.Join(dir, "images")
		require.NoError(t, os.MkdirAll(typesDir, 0755))

		typesSrc := `package images

type Image struct {
	Width  int
	Height int
	Data   []byte
}

type Gallery struct {
	Images []Image
}
`
		require.NoError(t, os.WriteFile(filepath.Join(typesDir, "types.go"), []byte(typesSrc), 0644))

		// Create main file that imports and uses these types in function calls
		mainSrc := `package testmod

import "testmod/images"

func processImage(img images.Image) int {
	return img.Width * img.Height
}

func processGallery(g images.Gallery) int {
	return len(g.Images)
}

func CreateAndProcess() int {
	// Call with composite literal using imported type
	result1 := processImage(images.Image{
		Width:  100,
		Height: 200,
	})

	// Another call with nested composite literal
	result2 := processGallery(images.Gallery{
		Images: []images.Image{
			{Width: 50, Height: 50},
			{Width: 100, Height: 100},
		},
	})

	return result1 + result2
}
`
		filePath := filepath.Join(dir, "main.go")
		require.NoError(t, os.WriteFile(filePath, []byte(mainSrc), 0644))

		// Verify the source compiles before modification
		cmd := exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Original source should compile: %s", string(output))

		mod := &ASTModifier{}
		err = mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testmod",
			FunctionIdent: "testmod:CreateAndProcess",
			FunctionName:  "CreateAndProcess",
		}

		// Inject instrumentation before processImage and processGallery calls
		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "processImage" || ident.Name == "processGallery"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		// Commit the modified file
		require.NoError(t, mod.CommitFile(filePath))

		// Read the modified file
		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		// Verify the file still parses
		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.ParseComments)
		require.NoError(t, err, "Modified file should parse: %s", string(modifiedSrc))

		// Verify the file compiles (catches "is not a type" errors)
		cmd = exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err = cmd.CombinedOutput()
		require.NoError(t, err, "Build failed with: %s\n\nModified source:\n%s", string(output), string(modifiedSrc))
	})

	t.Run("pointer_to_imported_type", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()

		// Create go.mod
		goMod := testGoMod
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		// Create a package with types
		typesDir := filepath.Join(dir, "images")
		require.NoError(t, os.MkdirAll(typesDir, 0755))

		typesSrc := `package images

type Image struct {
	Width  int
	Height int
}
`
		require.NoError(t, os.WriteFile(filepath.Join(typesDir, "types.go"), []byte(typesSrc), 0644))

		// Create main file with pointer composite literals
		mainSrc := `package testmod

import "testmod/images"

func processImagePtr(img *images.Image) int {
	if img == nil {
		return 0
	}
	return img.Width * img.Height
}

func CreateAndProcess() int {
	// Call with pointer to composite literal using imported type
	result := processImagePtr(&images.Image{
		Width:  100,
		Height: 200,
	})
	return result
}
`
		filePath := filepath.Join(dir, "main.go")
		require.NoError(t, os.WriteFile(filePath, []byte(mainSrc), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testmod",
			FunctionIdent: "testmod:CreateAndProcess",
			FunctionName:  "CreateAndProcess",
		}

		// Inject instrumentation before processImagePtr call
		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "processImagePtr"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		// Verify the file parses
		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.ParseComments)
		require.NoError(t, err, "Modified file should parse: %s", string(modifiedSrc))

		// Verify the file compiles
		cmd := exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Build failed with: %s\n\nModified source:\n%s", string(output), string(modifiedSrc))
	})

	t.Run("imported_type_assertion", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		dir := t.TempDir()

		goMod := testGoMod
		require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(goMod), 0644))

		typesDir := filepath.Join(dir, "images")
		require.NoError(t, os.MkdirAll(typesDir, 0755))

		typesSrc := `package images

type Image struct {
	Width  int
	Height int
}
`
		require.NoError(t, os.WriteFile(filepath.Join(typesDir, "types.go"), []byte(typesSrc), 0644))

		// Create main file with type assertions
		mainSrc := `package testmod

import "testmod/images"

func processAny(v any) int {
	if img, ok := v.(images.Image); ok {
		return img.Width * img.Height
	}
	if imgPtr, ok := v.(*images.Image); ok {
		return imgPtr.Width * imgPtr.Height
	}
	return 0
}

func CreateAndProcess() int {
	img := images.Image{Width: 100, Height: 200}
	return processAny(img)
}
`
		filePath := filepath.Join(dir, "main.go")
		require.NoError(t, os.WriteFile(filePath, []byte(mainSrc), 0644))

		mod := &ASTModifier{}
		err := mod.InjectASTClient(dir, 8448, 20, 1024)
		require.NoError(t, err)

		fn := &Function{
			FilePath:      filePath,
			PackageName:   "testmod",
			FunctionIdent: "testmod:CreateAndProcess",
			FunctionName:  "CreateAndProcess",
		}

		_, err = mod.InjectFuncPointBeforeCall(fn, func(call *ast.CallExpr) (any, bool) {
			if ident, ok := call.Fun.(*ast.Ident); ok {
				return struct{}{}, ident.Name == "processAny"
			}
			return struct{}{}, false
		})
		require.NoError(t, err)

		require.NoError(t, mod.CommitFile(filePath))

		modifiedSrc, err := os.ReadFile(filePath)
		require.NoError(t, err)

		fset := token.NewFileSet()
		_, err = parser.ParseFile(fset, filePath, modifiedSrc, parser.ParseComments)
		require.NoError(t, err, "Modified file should parse: %s", string(modifiedSrc))

		cmd := exec.Command("go", "build", ".")
		cmd.Dir = dir
		output, err := cmd.CombinedOutput()
		require.NoError(t, err, "Build failed with: %s\n\nModified source:\n%s", string(output), string(modifiedSrc))
	})
}
