package lens

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strconv"
	"testing"

	"github.com/go-analyze/charts"
	"github.com/stretchr/testify/require"
	"github.com/vmihailenco/msgpack/v5"
	"golang.org/x/tools/go/callgraph"
)

// makeWideTestGraph builds a “short & wide” call graph: `start` has `width` callers, each of which has no further callers.
func makeWideTestGraph(width int) (*callgraph.Node, map[*callgraph.Node]bool) {
	start := &callgraph.Node{}
	for i := 0; i < width; i++ {
		caller := &callgraph.Node{}
		edge := &callgraph.Edge{Caller: caller}
		start.In = append(start.In, edge)
	}
	// no roots to prune in this benchmark
	return start, map[*callgraph.Node]bool{}
}

// makeDeepTestGraph builds a “deep & narrow” call graph of depth `depth`:  start → n1 → n2 → … → n_depth
func makeDeepTestGraph(depth int) (*callgraph.Node, map[*callgraph.Node]bool) {
	start := &callgraph.Node{}
	prev := start
	for i := 0; i < depth; i++ {
		node := &callgraph.Node{}
		edge := &callgraph.Edge{Caller: node}
		prev.In = append(prev.In, edge)
		prev = node
	}
	return start, map[*callgraph.Node]bool{}
}

func BenchmarkReverseDFSWide(b *testing.B) {
	for _, width := range []int{10, 100, 1000} {
		width := width // capture
		b.Run(fmt.Sprintf("Wide-%d", width), func(b *testing.B) {
			start, rootNodes := makeWideTestGraph(width)
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				_ = reverseDFS(start, rootNodes, func(chain []*callgraph.Node) error {
					return nil // no-op
				})
			}
		})
	}
}

func BenchmarkReverseDFSDeep(b *testing.B) {
	for _, depth := range []int{10, 100, 1000} {
		depth := depth // capture
		b.Run(fmt.Sprintf("Deep-%d", depth), func(b *testing.B) {
			start, rootNodes := makeDeepTestGraph(depth)
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				_ = reverseDFS(start, rootNodes, func(chain []*callgraph.Node) error {
					return nil // no-op
				})
			}
		})
	}
}

func BenchmarkASTClientServer(b *testing.B) {
	pointMap := map[int]*string{
		1: charts.Ptr("fooStr"),
		2: charts.Ptr("barStr"),
	}
	srv, err := astExecServerStart(lensMonitorServerHost, lensMonitorServerPort, nil)
	require.NoError(b, err)
	defer func() {
		_ = srv.Stop(b.Context())
	}()
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		monitor := newTestMonitor(nil, "", "fakeProjectDir", pointMap, pointMap, pointMap, pointMap)
		err = srv.SetPointHandler(monitor)
		require.NoError(b, err)

		SendLensPointMessage(1)
		SendLensPointStateMessage(2,
			LensMonitorFieldSnapshot{Name: "b", Val: b},
			LensMonitorFieldSnapshot{Name: "pointMap", Val: pointMap},
			LensMonitorFieldSnapshot{Name: "monitor", Val: monitor},
			LensMonitorFieldSnapshot{Name: "srv", Val: srv})
	}
	b.StopTimer()
}

func BenchmarkMemStorage_SaveLoad(b *testing.B) {
	storage := NewMemStorage()
	defer storage.Close()

	key := "mem-key"
	value := make([]byte, 2048) // 2KB test value
	for i := range value {
		value[i] = byte(i)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if err := storage.SaveState(key, value); err != nil {
			b.Fatalf("SaveState failed: %v", err)
		} else if _, ok, err := storage.LoadState(key); err != nil || !ok {
			b.Fatalf("LoadState failed: %v", err)
		} else if err := storage.DeleteState(key); err != nil {
			b.Fatalf("DeleteState failed: %v", err)
		}
	}
}

func BenchmarkBadgerStorage_SaveLoad(b *testing.B) {
	dir, err := os.MkdirTemp("", "badger-bench")
	if err != nil {
		b.Fatalf("Failed to create temp dir: %v", err)
	}
	storage, err := NewBadgerStorage(dir, 16) // 16MB memory
	if err != nil {
		b.Fatalf("Failed to create Badger storage: %v", err)
	}
	defer storage.Close()

	key := "badger-key"
	value := make([]byte, 2048) // 2KB test value
	for i := range value {
		value[i] = byte(i)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if err := storage.SaveState(key, value); err != nil {
			b.Fatalf("SaveState failed: %v", err)
		} else if _, ok, err := storage.LoadState(key); err != nil || !ok {
			b.Fatalf("LoadState failed: %v", err)
		} else if err := storage.DeleteState(key); err != nil {
			b.Fatalf("DeleteState failed: %v", err)
		}
	}
}

func BenchmarkBadgerStorage_SaveLoadLarge(b *testing.B) {
	dir, err := os.MkdirTemp("", "badger-bench")
	if err != nil {
		b.Fatalf("Failed to create temp dir: %v", err)
	}
	origLimit := badgerSplitLimit
	badgerSplitLimit = 1024 * 16
	defer func() { badgerSplitLimit = origLimit }()
	storage, err := NewBadgerStorage(dir, 64) // 64MB memory
	if err != nil {
		b.Fatalf("Failed to create Badger storage: %v", err)
	}
	defer storage.Close()

	key := "badger-key"
	value := make([]byte, 1024*1024*2) // 2MB test value
	for i := range value {
		value[i] = byte(i)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if err := storage.SaveState(key, value); err != nil {
			b.Fatalf("SaveState failed: %v", err)
		} else if _, ok, err := storage.LoadState(key); err != nil || !ok {
			b.Fatalf("LoadState failed: %v", err)
		} else if err := storage.DeleteState(key); err != nil {
			b.Fatalf("DeleteState failed: %v", err)
		}
	}
}

func BenchmarkCloneNodeNoPos(b *testing.B) {
	expr, _ := parser.ParseExpr("a + b*c")
	var buf bytes.Buffer
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = cloneExprNoPos(&buf, expr)
	}
}

func BenchmarkBuildReturnInstrumentation(b *testing.B) {
	iface, _ := parser.ParseExpr("interface{}")
	type bc struct {
		name        string
		src         string
		resultTypes []ast.Expr
		resultNames []string
	}
	cases := []bc{
		{
			name: "Named",
			src: `package foo
func Bar() (x int) {
    x = 5
    return
}`,
			resultTypes: []ast.Expr{ast.NewIdent("int")},
			resultNames: []string{"x"},
		},
		{
			name: "BasicLit",
			src: `package foo
func Foo() int { return 42 }`,
			resultTypes: []ast.Expr{ast.NewIdent("int")},
			resultNames: []string{""},
		},
		{
			name: "BasicLitIface",
			src: `package foo
func FooIface() interface{} { return 42 }`,
			resultTypes: []ast.Expr{iface},
			resultNames: []string{""},
		},
		{
			name: "CallMulti",
			src: `package foo
func CallMulti() (int, int) { return bar() }`,
			resultTypes: []ast.Expr{ast.NewIdent("int"), ast.NewIdent("int")},
			resultNames: []string{"", ""},
		},
		{
			name: "Recursive",
			src: `package foo
func Rec(n int) int {
    if n > 0 { return Rec(n-1) }
    return 1
}`,
			resultTypes: []ast.Expr{ast.NewIdent("int")},
			resultNames: []string{""},
		},
		{
			name: "RecursiveIface",
			src: `package foo
func RecIface(n int) interface{} {
    if n > 0 { return RecIface(n-1) }
    return n
}`,
			resultTypes: []ast.Expr{iface},
			resultNames: []string{""},
		},
	}

	type retCase struct {
		fnName   string
		ret      *ast.ReturnStmt
		decls    []declInfo
		resTypes []ast.Expr
		resNames []string
	}
	var retCases []retCase
	for _, c := range cases {
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, "foo.go", c.src, 0)
		require.NoError(b, err)
		fn := file.Decls[0].(*ast.FuncDecl)
		ast.Inspect(fn, func(n ast.Node) bool {
			if r, ok := n.(*ast.ReturnStmt); ok {
				retCases = append(retCases, retCase{
					fnName:   fn.Name.Name,
					ret:      r,
					decls:    visibleDeclsBefore(fn, r.Pos()),
					resTypes: c.resultTypes,
					resNames: c.resultNames,
				})
			}
			return true
		})
	}

	var buf bytes.Buffer
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for _, rc := range retCases {
			_, _ = buildReturnInstrumentation(&buf, rc.ret, 1,
				&Function{FunctionName: rc.fnName}, rc.decls, rc.resTypes, nil, rc.resNames)
		}
	}
}

// benchTestResult creates a moderately sized structure for encoding benchmarks
func benchTestResult() *TestResult {
	tr := &TestResult{
		TestFunction:  MinimumTestFunction{FunctionIdent: "bench.fn", FunctionName: "TestBench"},
		CallerResults: make(map[string][]CallFrame),
	}

	sharedNode := &FieldValue{Value: "dup", Children: FieldValues{"leaf": &FieldValue{Value: "v"}}}
	sharedFV := FieldValues{"a": &FieldValue{Value: "1"}, "n": sharedNode}
	sharedSt := []StackFrame{{File: "file.go", Line: 1, Function: "fn"}}

	// all fields duplicated
	dupFrames := make([]CallFrame, 5)
	for i := range dupFrames {
		dupFrames[i] = CallFrame{FieldValues: sharedFV, Stack: sharedSt}
	}
	tr.CallerResults["dup"] = dupFrames

	// same node, different maps
	nodeDup := make([]CallFrame, 5)
	for i := range nodeDup {
		fv := FieldValues{"n": sharedNode, "u": &FieldValue{Value: strconv.Itoa(i)}}
		nodeDup[i] = CallFrame{FieldValues: fv, Stack: sharedSt}
	}
	tr.CallerResults["nodeDup"] = nodeDup

	// same map, different stacks
	fvDup := make([]CallFrame, 5)
	for i := range fvDup {
		st := []StackFrame{{File: "file.go", Line: uint32(i + 2), Function: "fn"}}
		fvDup[i] = CallFrame{FieldValues: sharedFV, Stack: st}
	}
	tr.CallerResults["fvDup"] = fvDup

	// unique map and stack
	uniq := make([]CallFrame, 5)
	for i := range uniq {
		fv := FieldValues{"u": &FieldValue{Value: strconv.Itoa(i)}}
		st := []StackFrame{{File: "u" + strconv.Itoa(i) + ".go", Line: uint32(i), Function: "fn"}}
		uniq[i] = CallFrame{FieldValues: fv, Stack: st}
	}
	tr.CallerResults["unique"] = uniq

	return tr
}

func BenchmarkTestResultEncode(b *testing.B) {
	tr := benchTestResult()
	enc := msgpack.GetEncoder()
	defer msgpack.PutEncoder(enc)
	var buf bytes.Buffer
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		_, _ = tr.marshalMsgpack(enc, &buf)
	}
}

func BenchmarkTestResultDecode(b *testing.B) {
	tr := benchTestResult()
	data, err := tr.MarshalMsgpack()
	require.NoError(b, err)
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		var out TestResult
		_ = out.UnmarshalMsgpack(data)
	}
}

func BenchmarkTestResultEncodeBaseline1(b *testing.B) {
	tr := benchTestResult()
	baselineTR := baselineTestResult{
		TestFunction:     tr.TestFunction,
		CallerResults:    tr.CallerResults,
		ProjectPanics:    tr.ProjectPanics,
		ModulePanics:     tr.ModulePanics,
		ModuleChangesHit: tr.ModuleChangesHit,
		TestFailure:      tr.TestFailure,
	}
	enc := msgpack.GetEncoder()
	defer msgpack.PutEncoder(enc)
	var buf bytes.Buffer
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		buf.Reset()
		enc.Reset(&buf)
		require.NoError(b, enc.Encode(baselineTR))
	}
}

func BenchmarkTestResultDecodeBaseline(b *testing.B) {
	tr := benchTestResult()
	data, err := encodeBaseline(tr)
	require.NoError(b, err)
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		var simple baselineTestResult
		require.NoError(b, msgpack.Unmarshal(data, &simple))
	}
}
