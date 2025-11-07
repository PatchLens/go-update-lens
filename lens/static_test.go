package lens

import (
	"errors"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

func TestReverseDFS(t *testing.T) {
	t.Parallel()

	type testCase struct {
		name         string
		graphFn      func() *callgraph.Node
		rootDepth    int // depth at which to prune (0 for no pruning)
		errAt        int // call index at which visitFunc returns an error (-1 for no error)
		wantErr      bool
		wantChainsFn func(start *callgraph.Node) [][]*callgraph.Node
	}

	cases := []testCase{
		{
			name:      "wide_graph_no_roots",
			graphFn:   func() *callgraph.Node { g, _ := makeWideTestGraph(3); return g },
			rootDepth: 0,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				// initial call for start only
				chains = append(chains, []*callgraph.Node{start})
				// expect callers in LIFO (reverse insertion) order
				for i := len(start.In) - 1; i >= 0; i-- {
					caller := start.In[i].Caller
					chains = append(chains, []*callgraph.Node{start, caller})
				}
				return chains
			},
		},
		{
			name:      "deep_graph_no_roots",
			graphFn:   func() *callgraph.Node { g, _ := makeDeepTestGraph(3); return g },
			rootDepth: 0,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				// traverse depth-first: start, n1, n2, n3
				chains = append(chains, []*callgraph.Node{start})
				n1 := start.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, n1})
				n2 := n1.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, n1, n2})
				n3 := n2.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, n1, n2, n3})
				return chains
			},
		},
		{
			name:      "prune_at_root_depth_2",
			graphFn:   func() *callgraph.Node { g, _ := makeDeepTestGraph(3); return g },
			rootDepth: 2,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				// stop traversal when reaching depth-2
				chains = append(chains, []*callgraph.Node{start})
				n1 := start.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, n1})
				n2 := n1.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, n1, n2})
				return chains
			},
		},
		{
			name:      "error_during_visit",
			graphFn:   func() *callgraph.Node { g, _ := makeWideTestGraph(2); return g },
			rootDepth: 0,
			errAt:     2,
			wantErr:   true,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				// expect start, then first caller popped (index 1)
				chains = append(chains, []*callgraph.Node{start})
				// callers reversed: start.In[1] is popped first
				caller := start.In[1].Caller
				chains = append(chains, []*callgraph.Node{start, caller})
				return chains
			},
		},
		{
			name: "skip_nil_callers",
			graphFn: func() *callgraph.Node {
				start := &callgraph.Node{}
				// first edge has nil Caller, second is a real node
				start.In = []*callgraph.Edge{
					{Caller: nil},
					{Caller: &callgraph.Node{}},
				}
				return start
			},
			rootDepth: 0,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				valid := start.In[1].Caller
				return [][]*callgraph.Node{
					{start},
					{start, valid},
				}
			},
		},
		{
			name: "cycle_graph",
			graphFn: func() *callgraph.Node {
				a := &callgraph.Node{}
				b := &callgraph.Node{}
				// a -> b -> a
				a.In = append(a.In, &callgraph.Edge{Caller: b})
				b.In = append(b.In, &callgraph.Edge{Caller: a})
				return a
			},
			rootDepth: 0,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				b := start.In[0].Caller
				return [][]*callgraph.Node{
					{start},
					{start, b},
				}
			},
		},
		{
			name: "combination_wide_and_deep",
			graphFn: func() *callgraph.Node {
				start := &callgraph.Node{}
				// branch 1: start ← c1 ← c1a
				c1 := &callgraph.Node{}
				c1a := &callgraph.Node{}
				c1.In = append(c1.In, &callgraph.Edge{Caller: c1a})
				// branch 2: start ← c2
				c2 := &callgraph.Node{}
				start.In = []*callgraph.Edge{
					{Caller: c1},
					{Caller: c2},
				}
				return start
			},
			rootDepth: 0,
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				chains = append(chains, []*callgraph.Node{start})
				// LIFO: second edge (c2) first
				chains = append(chains, []*callgraph.Node{start, start.In[1].Caller})
				// then first edge (c1)
				c1 := start.In[0].Caller
				chains = append(chains, []*callgraph.Node{start, c1})
				// and finally its child
				chains = append(chains, []*callgraph.Node{start, c1, c1.In[0].Caller})
				return chains
			},
		},
		{
			name: "prune_deepwide_at_depth1",
			graphFn: func() *callgraph.Node {
				start := &callgraph.Node{}
				c1 := &callgraph.Node{}
				c1a := &callgraph.Node{}
				c1.In = append(c1.In, &callgraph.Edge{Caller: c1a})
				c2 := &callgraph.Node{}
				start.In = []*callgraph.Edge{
					{Caller: c1},
					{Caller: c2},
				}
				return start
			},
			rootDepth: 1, // prune when you hit c1 (depth‑1)
			errAt:     -1,
			wantErr:   false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				var chains [][]*callgraph.Node
				chains = append(chains, []*callgraph.Node{start})
				// still get both branches, but do NOT descend into c1a
				chains = append(chains, []*callgraph.Node{start, start.In[1].Caller})
				chains = append(chains, []*callgraph.Node{start, start.In[0].Caller})
				return chains
			},
		},
		{
			name:    "no_edges_nil_In",
			graphFn: func() *callgraph.Node { return &callgraph.Node{} },
			wantErr: false,
			wantChainsFn: func(start *callgraph.Node) [][]*callgraph.Node {
				return [][]*callgraph.Node{{start}}
			},
		},
	}

	for _, tc := range cases {
		tc := tc // capture range variable
		t.Run(tc.name, func(t *testing.T) {
			start := tc.graphFn()

			// Setup rootNodes map if pruning is requested
			var rootNodes map[*callgraph.Node]bool
			if tc.rootDepth > 0 {
				rootNodes = make(map[*callgraph.Node]bool)
				n := start
				for i := 0; i < tc.rootDepth; i++ {
					n = n.In[0].Caller
				}
				rootNodes[n] = true
			}

			var chains [][]*callgraph.Node
			var count int
			err := reverseDFS(start, rootNodes, func(chain []*callgraph.Node) error {
				// record a copy of the chain
				copyChain := make([]*callgraph.Node, len(chain))
				copy(copyChain, chain)
				chains = append(chains, copyChain)
				count++
				if tc.errAt >= 0 && count == tc.errAt {
					return errors.New("visit error")
				}
				return nil
			})

			if tc.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}

			wantChains := tc.wantChainsFn(start)
			if debugCallChain == "" {
				// chain will be truncated for efficiency
				assert.Len(t, chains, len(wantChains))
				for i := range wantChains {
					assert.Equal(t, wantChains[i][len(wantChains[i])-1], chains[i][0])
				}
			} else {
				assert.Equal(t, wantChains, chains)
			}
		})
	}
}

// buildSSAPackage builds an SSA package from the provided source files.
func buildSSAPackage(t *testing.T, pkgPath string, files map[string]string) *ssa.Package {
	t.Helper()

	fset := token.NewFileSet()
	astFiles := make([]*ast.File, 0, len(files))
	for name, src := range files {
		f, err := parser.ParseFile(fset, name, src, 0)
		require.NoError(t, err)
		astFiles = append(astFiles, f)
	}

	conf := &types.Config{Importer: importer.Default()}
	info := &types.Info{
		Types: make(map[ast.Expr]types.TypeAndValue),
		Defs:  make(map[*ast.Ident]types.Object),
		Uses:  make(map[*ast.Ident]types.Object),
	}
	typPkg, err := conf.Check(pkgPath, fset, astFiles, info)
	require.NoError(t, err)

	prog := ssa.NewProgram(fset, 0)
	for _, imp := range typPkg.Imports() {
		prog.CreatePackage(imp, nil, nil, true)
	}
	pkg := prog.CreatePackage(typPkg, astFiles, info, true)
	prog.Build()
	return pkg
}

func TestFunctionClassifications(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	// main package with a main function
	mainPkg := buildSSAPackage(t, "main", map[string]string{
		"main.go": "package main\nfunc main(){}\nfunc other(){}\n",
	})
	mainFn := mainPkg.Func("main")
	otherFn := mainPkg.Func("other")
	require.NotNil(t, mainFn)
	require.NotNil(t, otherFn)
	assert.True(t, isMainFunction(mainFn))
	assert.False(t, isMainFunction(otherFn))

	// package with an init function
	initPkg := buildSSAPackage(t, "foo", map[string]string{
		"foo.go": "package foo\nfunc init(){}\nfunc Bar(){}\n",
	})
	var initFn, barFn *ssa.Function
	for _, m := range initPkg.Members {
		if fn, ok := m.(*ssa.Function); ok {
			switch fn.Name() {
			case "Bar":
				barFn = fn
			default:
				if fn.Pos() != 0 && strings.HasPrefix(fn.Name(), "init") {
					initFn = fn
				}
			}
		}
	}
	require.NotNil(t, initFn)
	require.NotNil(t, barFn)
	assert.True(t, isInitFunction(initFn))
	assert.False(t, isInitFunction(barFn))

	// package with Go tests
	testPkg := buildSSAPackage(t, "foo", map[string]string{
		"foo_test.go": "package foo\nimport \"testing\"\nfunc TestFoo(t *testing.T) {}\nfunc NotTest() {}\n",
	})
	testFn := testPkg.Func("TestFoo")
	notTestFn := testPkg.Func("NotTest")
	require.NotNil(t, testFn)
	require.NotNil(t, notTestFn)
	assert.True(t, isGoTestFunction(testFn))
	assert.False(t, isGoTestFunction(notTestFn))
}

func TestMakeFunctionIdentStr(t *testing.T) {
	t.Parallel()

	assert.Equal(t, "pkg:Type.Method", makeFunctionIdentStr("pkg", "Type", "Method"))
	assert.Equal(t, "pkg:Func", makeFunctionIdentStr("pkg", "", "Func"))
}

func TestAnalyzeSSAFunctionReturnPoints(t *testing.T) {
	t.Parallel()

	pkg := buildSSAPackage(t, "foo", map[string]string{
		"foo.go": "package foo\n\nfunc A() int {\n    return 1\n}\n\nfunc B(x int) int {\n    if x > 0 {\n        return A()\n    }\n    return 0\n}\n\nfunc C() int {\n    panic(\"bad\")\n}\n",
	})

	a := pkg.Func("A")
	b := pkg.Func("B")
	c := pkg.Func("C")
	require.NotNil(t, a)
	require.NotNil(t, b)
	require.NotNil(t, c)

	entry, returns, ends := analyzeSSAFunctionReturnPoints(a)
	assert.Equal(t, uint32(3), entry)
	assert.Equal(t, []FunctionReturn{{Line: 4, CallCount: 0}}, returns)
	assert.False(t, ends)

	entry, returns, ends = analyzeSSAFunctionReturnPoints(b)
	assert.Equal(t, uint32(7), entry)
	assert.Equal(t, []FunctionReturn{{Line: 9, CallCount: 1}, {Line: 11, CallCount: 0}}, returns)
	assert.False(t, ends)

	entry, returns, ends = analyzeSSAFunctionReturnPoints(c)
	assert.Equal(t, uint32(14), entry)
	assert.Equal(t, []FunctionReturn{{Line: 15, CallCount: 0}}, returns)
	assert.True(t, ends)
}

func TestMergeReturnInfos(t *testing.T) {
	t.Parallel()

	got := mergeReturnInfos([]FunctionReturn{
		{Line: 2, CallCount: 1},
		{Line: 1, CallCount: 1},
		{Line: 2, CallCount: 2},
		{Line: 1, CallCount: 1},
	})

	want := []FunctionReturn{{Line: 1, CallCount: 2}, {Line: 2, CallCount: 3}}
	assert.Equal(t, want, got)
}

func TestIsGeneratedFile(t *testing.T) {
	t.Parallel()

	cases := []struct {
		file string
		want bool
	}{
		{"a.pb.go", true},
		{"service_grpc.pb.go", true},
		{"foo_gen.go", true},
		{"foo_mock.go", true},
		{"regular.go", false},
	}

	for _, c := range cases {
		assert.Equal(t, c.want, IsGeneratedFile(c.file), c.file)
	}
}

func TestFilePathAndIdent(t *testing.T) {
	t.Parallel()

	pkg := buildSSAPackage(t, "foo", map[string]string{"foo.go": "package foo\nfunc F(){}\n"})
	fn := pkg.Func("F")
	require.NotNil(t, fn)

	assert.Equal(t, "foo.go", filePathForSSAFunc(fn))
	ident, ok := MakeSSAFunctionIdent(fn)
	assert.True(t, ok)
	assert.Equal(t, "foo:F", ident)
}

func TestAnalyzeASTFunctionReturnPoints(t *testing.T) {
	t.Parallel()

	src := `package foo

func A() int {
    return 1
}

func B(x int) int {
    if x > 0 {
        return A()
    }
    return 0
}

func C() int {
    panic("bad")
}`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "foo.go", src, 0)
	require.NoError(t, err)

	var aDecl, bDecl, cDecl *ast.FuncDecl
	for _, decl := range file.Decls {
		if fd, ok := decl.(*ast.FuncDecl); ok {
			switch fd.Name.Name {
			case "A":
				aDecl = fd
			case "B":
				bDecl = fd
			case "C":
				cDecl = fd
			}
		}
	}
	require.NotNil(t, aDecl)
	require.NotNil(t, bDecl)
	require.NotNil(t, cDecl)

	entry, returns, ends := AnalyzeASTFunctionReturnPoints(fset, aDecl)
	assert.Equal(t, uint32(3), entry)
	assert.Equal(t, []FunctionReturn{{Line: 4, CallCount: 0}}, returns)
	assert.False(t, ends)

	entry, returns, ends = AnalyzeASTFunctionReturnPoints(fset, bDecl)
	assert.Equal(t, uint32(7), entry)
	assert.Equal(t, []FunctionReturn{{Line: 9, CallCount: 1}, {Line: 11, CallCount: 0}}, returns)
	assert.False(t, ends)

	entry, returns, ends = AnalyzeASTFunctionReturnPoints(fset, cDecl)
	assert.Equal(t, uint32(14), entry)
	assert.Empty(t, returns)
	assert.True(t, ends)
}

func TestLoadProjectPackageCallGraph(t *testing.T) {
	t.Run("workspace", func(t *testing.T) {
		t.Parallel()

		root := t.TempDir()
		modules := []string{"ffmap", "charts", "combo"}
		for _, m := range modules {
			dir := filepath.Join(root, m)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			mod := fmt.Sprintf("module example.com/%s\n\ngo 1.20\n", m)
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(mod), 0o644))
			src := fmt.Sprintf("package %s\n\nfunc X() {}\n", m)
			require.NoError(t, os.WriteFile(filepath.Join(dir, "x.go"), []byte(src), 0o644))
		}
		work := "go 1.20\nuse (\n    ./ffmap\n    ./charts\n    ./combo\n)\n"
		require.NoError(t, os.WriteFile(filepath.Join(root, "go.work"), []byte(work), 0o644))

		cg, err := loadProjectPackageCallGraph(root, false)
		require.NoError(t, err)
		require.NotNil(t, cg)
	})
}

func createStaticAnalysisProject(t *testing.T) string {
	t.Helper()

	root := t.TempDir()
	mod := `module example.com/projtest

go 1.24

require github.com/go-analyze/flat-file-map v0.3.8
`
	require.NoError(t, os.WriteFile(filepath.Join(root, "go.mod"), []byte(mod), 0o644))
	sum := `github.com/go-analyze/flat-file-map v0.3.8 h1:dvAOXhEBnwPis6JYil4SDdKsjNgrcGe5J/9yvbEzdbY=
github.com/go-analyze/flat-file-map v0.3.8/go.mod h1:lX9GD3ZNnlv7k8Jtw5lB9LJ24kY69i6qstBbL7o8QRo=
`
	require.NoError(t, os.WriteFile(filepath.Join(root, "go.sum"), []byte(sum), 0o644))

	projDir := filepath.Join(root, "proj")
	require.NoError(t, os.MkdirAll(projDir, 0o755))
	projSrc := `package proj

import "github.com/go-analyze/flat-file-map/ffmap"

type Runner struct{}

func (r Runner) StepA() { r.StepB() }
func (r Runner) StepB() { r.StepC() }
func (r Runner) StepC() { ffmap.SetMapValues(nil, map[string]int{}) }
func (r Runner) StepD() { ffmap.OpenCSV("") }
func (r Runner) Unused() {}

func StepA() { StepB() }
func StepB() { StepC() }
func StepC() { ffmap.SetMapValues(nil, map[string]int{}) }
func StepD() { ffmap.OpenCSV("") }
func Unused() {}
`
	require.NoError(t, os.WriteFile(filepath.Join(projDir, "proj.go"), []byte(projSrc), 0o644))

	testSrc := `package proj

import "testing"

func TestStepB(t *testing.T) { StepB() }
func TestStepD(t *testing.T) { StepD() }
func TestRunnerStepA(t *testing.T) { var r Runner; r.StepA() }
func TestRunnerStepD(t *testing.T) { var r Runner; r.StepD() }
func TestUnused(t *testing.T) { Unused() }
func TestRunnerUnused(t *testing.T) { var r Runner; r.Unused() }
`
	require.NoError(t, os.WriteFile(filepath.Join(projDir, "proj_test.go"), []byte(testSrc), 0o644))

	mainSrc := `package main

import "example.com/projtest/proj"

func main() {
    proj.StepA()
    proj.StepD()
    proj.Unused()
    var r proj.Runner
    r.StepA()
    r.StepD()
    r.Unused()
}`
	require.NoError(t, os.WriteFile(filepath.Join(root, "main.go"), []byte(mainSrc), 0o644))

	return root
}

func TestCallerStaticAnalysis(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	root := createStaticAnalysisProject(t)

	changes := []*ModuleFunction{
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:SetMapValues"}},
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:OpenCSV"}},
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:sliceUniqueUnion"}},
	}

	callers, reachable, _, _, _, err := CallerStaticAnalysis(changes, root)
	require.NoError(t, err)
	assert.Len(t, callers, 8)

	got := make([]string, len(callers))
	for i, c := range callers {
		got[i] = c.FunctionIdent
	}
	want := []string{
		"example.com/projtest/proj:StepA",
		"example.com/projtest/proj:StepB",
		"example.com/projtest/proj:StepC",
		"example.com/projtest/proj:StepD",
		"example.com/projtest/proj:Runner.StepA",
		"example.com/projtest/proj:Runner.StepB",
		"example.com/projtest/proj:Runner.StepC",
		"example.com/projtest/proj:Runner.StepD",
	}
	assert.ElementsMatch(t, want, got)
	assert.NotContains(t, got, "example.com/projtest/proj:Unused")
	assert.NotContains(t, got, "example.com/projtest/proj:Runner.Unused")

	assert.Contains(t, reachable, "github.com/go-analyze/flat-file-map/ffmap:SetMapValues")
	assert.Contains(t, reachable, "github.com/go-analyze/flat-file-map/ffmap:OpenCSV")
	assert.NotContains(t, reachable, "github.com/go-analyze/flat-file-map/ffmap:sliceUniqueUnion")
}

func TestTestStaticAnalysis(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	root := createStaticAnalysisProject(t)

	changes := []*ModuleFunction{
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:SetMapValues"}},
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:OpenCSV"}},
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:sliceUniqueUnion"}},
	}

	callers, _, _, _, _, err := CallerStaticAnalysis(changes, root)
	require.NoError(t, err)

	tests, err := TestStaticAnalysis(callers, root)
	require.NoError(t, err)
	assert.Len(t, tests, 4)

	got := make([]string, len(tests))
	for i, tf := range tests {
		got[i] = tf.FunctionIdent
	}
	want := []string{
		"example.com/projtest/proj:TestStepB",
		"example.com/projtest/proj:TestStepD",
		"example.com/projtest/proj:TestRunnerStepA",
		"example.com/projtest/proj:TestRunnerStepD",
	}
	assert.ElementsMatch(t, want, got)
	assert.NotContains(t, got, "example.com/projtest/proj:TestUnused")
	assert.NotContains(t, got, "example.com/projtest/proj:TestRunnerUnused")
}

func TestExtractCallGraphEdges(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	root := createStaticAnalysisProject(t)

	changes := []*ModuleFunction{
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:SetMapValues"}},
		{Function: Function{FunctionIdent: "github.com/go-analyze/flat-file-map/ffmap:OpenCSV"}},
	}

	_, _, cg, _, _, err := CallerStaticAnalysis(changes, root)
	require.NoError(t, err)
	require.NotNil(t, cg, "call graph should not be nil")

	// Extract edges
	edges := extractCallGraphEdges(cg)
	require.NotNil(t, edges)

	// Validate expected call relationships exist in the edge map
	// StepA -> StepB
	stepAEdges := edges["example.com/projtest/proj:StepA"]
	assert.Contains(t, stepAEdges, "example.com/projtest/proj:StepB")

	// StepB -> StepC
	stepBEdges := edges["example.com/projtest/proj:StepB"]
	assert.Contains(t, stepBEdges, "example.com/projtest/proj:StepC")

	// StepC -> ffmap.SetMapValues
	stepCEdges := edges["example.com/projtest/proj:StepC"]
	require.NotNil(t, stepCEdges)
	// External module functions may have simplified identifiers
	hasSetMapValues := false
	for _, edge := range stepCEdges {
		if strings.Contains(edge, "SetMapValues") {
			hasSetMapValues = true
			break
		}
	}
	assert.True(t, hasSetMapValues)

	// StepD -> ffmap.OpenCSV
	stepDEdges := edges["example.com/projtest/proj:StepD"]
	require.NotNil(t, stepDEdges)
	hasOpenCSV := false
	for _, edge := range stepDEdges {
		if strings.Contains(edge, "OpenCSV") {
			hasOpenCSV = true
			break
		}
	}
	assert.True(t, hasOpenCSV)

	// Runner.StepA -> Runner.StepB
	runnerStepAEdges := edges["example.com/projtest/proj:Runner.StepA"]
	assert.Contains(t, runnerStepAEdges, "example.com/projtest/proj:Runner.StepB")

	// Runner.StepB -> Runner.StepC
	runnerStepBEdges := edges["example.com/projtest/proj:Runner.StepB"]
	assert.Contains(t, runnerStepBEdges, "example.com/projtest/proj:Runner.StepC")

	// Runner.StepC -> ffmap.SetMapValues
	runnerStepCEdges := edges["example.com/projtest/proj:Runner.StepC"]
	require.NotNil(t, runnerStepCEdges)
	hasRunnerSetMapValues := false
	for _, edge := range runnerStepCEdges {
		if strings.Contains(edge, "SetMapValues") {
			hasRunnerSetMapValues = true
			break
		}
	}
	assert.True(t, hasRunnerSetMapValues)

	// Runner.StepD -> ffmap.OpenCSV
	runnerStepDEdges := edges["example.com/projtest/proj:Runner.StepD"]
	require.NotNil(t, runnerStepDEdges)
	hasRunnerOpenCSV := false
	for _, edge := range runnerStepDEdges {
		if strings.Contains(edge, "OpenCSV") {
			hasRunnerOpenCSV = true
			break
		}
	}
	assert.True(t, hasRunnerOpenCSV)

	// Validate that functions with no outgoing calls have nil edges (memory efficiency)
	// or are not in the map (since their leaf functions)
	unused := edges["example.com/projtest/proj:Unused"]
	assert.Nil(t, unused, "Unused function should have nil edges as it has no outgoing calls")

	runnerUnused := edges["example.com/projtest/proj:Runner.Unused"]
	assert.Nil(t, runnerUnused, "Runner.Unused should have nil edges as it has no outgoing calls")
}

func TestExtractCallGraphEdges_NilGraph(t *testing.T) {
	t.Parallel()

	edges := extractCallGraphEdges(nil)
	assert.NotNil(t, edges)
	assert.Empty(t, edges)
}
