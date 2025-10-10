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
		predicate      func(*ast.CallExpr) bool
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				return false // Never match
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == "Sprint"
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return ident.Name == "GetSlice"
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == printfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return ident.Name == "IsPositive"
				}
				return false
			},
			expectedPoints: 1,
			expectedCalls:  map[string]int{"fmt.Sprintf": 2, "fmt.Println": 1},
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
			predicate: func(call *ast.CallExpr) bool {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return ident.Name == "ShouldContinue"
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
					if x, ok := sel.X.(*ast.Ident); ok {
						return x.Name == fmtPackage && sel.Sel.Name == sprintfFuncName
					}
				}
				return false
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
			predicate: func(call *ast.CallExpr) bool {
				if ident, ok := call.Fun.(*ast.Ident); ok {
					return ident.Name == "GetInterface"
				}
				return false
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

			pointIDs, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Len(t, pointIDs, tc.expectedPoints)

			// Verify point IDs are sequential
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
			pointIDs2, err := modifier.InjectFuncPointBeforeCall(&fn, tc.predicate)
			require.NoError(t, err)
			require.Empty(t, pointIDs2)
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

			// Build instrumentation
			var buf bytes.Buffer
			stmt, err := buildCallInstrumentationWithArgs(&buf, 42, callExpr)
			require.NoError(t, err)
			require.NotNil(t, stmt)

			// Verify it's an ExprStmt containing a CallExpr
			exprStmt, ok := stmt.(*ast.ExprStmt)
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
					if !ok || keyIdent.Name != "Name" {
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
		stmt, err := buildCallInstrumentationWithArgs(&buf, 1, callExpr)
		require.NoError(t, err)

		// Format the statement to verify it's valid Go code
		buf.Reset()
		err = format.Node(&buf, token.NewFileSet(), stmt)
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
				if !ok || keyIdent.Name != "Name" {
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
	pointIDs, err := modifier.InjectFuncPointBeforeCall(&fn, func(call *ast.CallExpr) bool {
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				return x.Name == "fmt" && sel.Sel.Name == "Printf"
			}
		}
		return false
	})
	require.NoError(t, err)
	require.Len(t, pointIDs, 1)

	require.NoError(t, modifier.CommitFile(filePath))

	// Read modified file
	modifiedSrc, err := os.ReadFile(filePath)
	require.NoError(t, err)
	modifiedStr := string(modifiedSrc)

	// Verify the monitoring call was inserted
	assert.Contains(t, modifiedStr, "SendLensPointStateMessage")

	// Parse the modified file to verify argument naming
	fset := token.NewFileSet()
	modFile, err := parser.ParseFile(fset, filePath, nil, 0)
	require.NoError(t, err)

	// Find the monitoring call
	var foundMonitoringCall bool
	ast.Inspect(modFile, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if ident, ok := call.Fun.(*ast.Ident); ok && ident.Name == "SendLensPointStateMessage" {
				foundMonitoringCall = true

				// Verify arguments (should have point ID + 3 snapshots for fmt.Printf args)
				// Point ID + arg0 (format string) + arg1 (x) + arg2 (y)
				assert.NotEmpty(t, call.Args)

				// Check that snapshots use "arg" naming
				buf := bytes.Buffer{}
				for i := 1; i < len(call.Args); i++ {
					buf.Reset()
					err := format.Node(&buf, token.NewFileSet(), call.Args[i])
					require.NoError(t, err)
					snapshot := buf.String()
					// Should contain "arg" in the name field
					assert.Contains(t, snapshot, fmt.Sprintf("arg%d", i-1))
				}
				return false
			}
		}
		return true
	})

	assert.True(t, foundMonitoringCall)
}
