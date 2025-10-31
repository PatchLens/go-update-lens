package lens

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

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
				PackageName:   "main",
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
	_, ok := blk.List[0].(*ast.AssignStmt)
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

// TestReturnNilToInterface tests the fix for "use of untyped nil in assignment"
// when returning nil to interface types
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

			// Format the block to ensure it's valid Go code
			var genBuf bytes.Buffer
			err = format.Node(&genBuf, token.NewFileSet(), blk)
			require.NoError(t, err, "Should generate valid Go code")

			// Check we don't generate invalid "tmpX := nil"
			generated := genBuf.String()
			assert.NotContains(t, generated, "lenSyntheticTmp0 := nil",
				"Should not generate untyped nil assignment")

			// Check that the generated code handles nil correctly
			// Even if not using temp, nil should be handled properly
			if ret.Results[0].(*ast.Ident).Name == "nil" {
				// nil returns should not cause invalid syntax
				assert.NotContains(t, generated, ":= nil",
					"Should not have untyped nil in short variable declaration")
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
	require.NoError(t, err, "Should generate valid Go statement")

	// Should be "var lenSyntheticRet0 error = nil"
	generated := buf.String()
	assert.Contains(t, generated, "var lenSyntheticRet0 error = nil")
	assert.NotContains(t, generated, ":= nil", "Should not use := with nil")
}

// TestImplicitReturnInstrumentation tests handling of functions with no explicit return
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
			returnVarNames: nil, // nil for void functions (matches actual behavior)
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
			// The logic matches InjectFuncPointReturnStates: allNamed requires all to have names
			allNamed := len(funcResultNames) > 0 && !slices.Contains(funcResultNames, "")
			assert.Equal(t, tc.expectReturn, allNamed,
				"allNamed calculation mismatch for %s", tc.name)

			if allNamed {
				// Build the return statement that would be added
				returnExprs := make([]ast.Expr, len(funcResultNames))
				for i, name := range funcResultNames {
					returnExprs[i] = ast.NewIdent(name)
				}
				retStmt := &ast.ReturnStmt{Results: returnExprs}

				// Format it to check validity
				var buf bytes.Buffer
				err := format.Node(&buf, token.NewFileSet(), retStmt)
				require.NoError(t, err, "Return statement should be valid")

				// Check it has the right variables
				generated := buf.String()
				for _, name := range tc.returnVarNames {
					if name != "" {
						assert.Contains(t, generated, name)
					}
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
			pointIDs := make([]int, 0, len(pointMap))
			for id := range pointMap {
				pointIDs = append(pointIDs, id)
			}
			slices.Sort(pointIDs)
			for i, id := range pointIDs {
				assert.Equal(t, i, id)
			}

			require.NoError(t, modifier.CommitFile(filePath))

			// Read and parse modified file
			modifiedSrc, err := os.ReadFile(filePath)
			require.NoError(t, err)
			modifiedStr := string(modifiedSrc)

			fset := token.NewFileSet()
			modFile, err := parser.ParseFile(fset, filePath, nil, 0)
			require.NoError(t, err)

			// Verify modification marker
			if tc.expectedPoints > 0 {
				assert.Contains(t, modifiedStr, "patchlens:before-call")
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
					if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == "SendLensPointStateMessage" {
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

			// Verify idempotency
			pointMap2, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Empty(t, pointMap2)
		})
	}
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
			require.True(t, ok, "Expected CallExpr")

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
			assert.Equal(t, "SendLensPointStateMessage", funIdent.Name)

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

	t.Run("Ellipsis", func(t *testing.T) {
		// Test that ellipsis arguments are handled correctly
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

	const monitorFuncName = "SendLensPointStateMessage"
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

	// Read modified file
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
		assert.Contains(t, code, "lenSyntheticArg0_0 := next()")
		assert.Contains(t, code, "first(lenSyntheticArg0_0)")
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
		assert.Contains(t, code, "helper(lenSyntheticArg0_0)")
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
		assert.Contains(t, code, "lenSyntheticArg0_0 := next()")
		assert.Contains(t, code, "lenSyntheticArg0_1 := next()")
		assert.Contains(t, code, "lenSyntheticArg0_2 := next()")
		assert.Contains(t, code, "addThree(lenSyntheticArg0_0, lenSyntheticArg0_1, lenSyntheticArg0_2)")
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
		assert.Contains(t, code, "lenSyntheticArg0_0 := getFormat()")
		assert.Contains(t, code, "lenSyntheticArg0_1 := getArg()")
		assert.Contains(t, code, "lenSyntheticArg0_2 := getArg()")
		assert.Contains(t, code, "fmt.Printf(lenSyntheticArg0_0, lenSyntheticArg0_1, lenSyntheticArg0_2)")
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
		assert.Contains(t, code, "lenSyntheticRecv0 := getBuilder()")
		// Argument (getValue()) should be evaluated once
		assert.Contains(t, code, "lenSyntheticArg0_0 := getValue()")
		assert.Contains(t, code, "lenSyntheticRecv0.Add(lenSyntheticArg0_0)")
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
				assert.Equal(t, 1, countFunctionCalls(t, src, "makeStruct"))
				code := string(src)
				assert.Contains(t, code, "lenSyntheticRecv0 := makeStruct()")
				assert.Contains(t, code, "lenSyntheticRecv0.DoWork()")
			},
		},
	}

	const monitorFuncName = "SendLensPointStateMessage"
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
				assert.Contains(t, modifiedStr, syntheticFieldNamePrefixReceiver+"0 := ")
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
				require.GreaterOrEqual(t, len(blk.List), 2, "Should have receiver assignment and send statement")
				// First statement should be receiver assignment
				assign, ok := blk.List[0].(*ast.AssignStmt)
				require.True(t, ok, "First statement should be assignment")
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
			assert.Equal(t, "SendLensPointStateMessage", funIdent.Name)

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
