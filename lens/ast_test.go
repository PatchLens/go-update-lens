package lens

import (
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

type captureHandler struct {
	mu          sync.Mutex
	points      []LensMonitorMessagePoint
	statePoints []LensMonitorMessagePointState
	panicPoints []LensMonitorMessagePointPanic
}

func (h *captureHandler) HandleFuncPoint(m LensMonitorMessagePoint) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.points = append(h.points, m)
}
func (h *captureHandler) HandleFuncPointState(m LensMonitorMessagePointState) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.statePoints = append(h.statePoints, m)
}

func (h *captureHandler) HandleFuncPointPanic(m LensMonitorMessagePointPanic) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.panicPoints = append(h.panicPoints, m)
}

// freePort returns an ephemeral TCP port.
func freePort(t *testing.T) int {
	t.Helper()

	l, err := net.Listen("tcp", "127.0.0.1:0")
	require.NoError(t, err)
	defer func() { _ = l.Close() }()
	return l.Addr().(*net.TCPAddr).Port
}

func TestASTEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}

	// singleReturnInjector helps implement our test case function to match other injection functions
	singleReturnInjectorFactory := func(f func(m *ASTModifier, fn *Function) (int, error)) func(m *ASTModifier, fn *Function) ([]int, error) {
		return func(m *ASTModifier, fn *Function) ([]int, error) {
			id, err := f(m, fn)
			if err != nil {
				return nil, err
			}
			return []int{id}, nil
		}
	}

	testCases := []struct {
		name                string
		fnName              string
		src                 string
		inject              func(m *ASTModifier, fn *Function) ([]int, error)
		expectedPoints      int
		expectedStatePoints int
		expectedPanicPoints int
		pointValidator      func(*testing.T, []LensMonitorMessagePoint)
		statePointValidator func(*testing.T, []LensMonitorMessagePointState)
		panicPointValidator func(*testing.T, []LensMonitorMessagePointPanic)
		fnIdent             string
	}{
		{
			name: "basic", // no function injection, only direct client call
			src: `package main
func main() {
	SendLensPointMessage(-1)
}`,
			inject: func(m *ASTModifier, fn *Function) ([]int, error) {
				return nil, nil // no-op
			},
			expectedPoints: 1,
			pointValidator: func(t *testing.T, points []LensMonitorMessagePoint) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				assert.Len(t, p.Stack, 3)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[0].Function)
			},
		},
		{
			name:   "point_entry",
			fnName: "TargetEntry",
			src: `package main
import "fmt"

func TargetEntry() {
	fmt.Println("Test Exec")
}
func main() {
	TargetEntry()
}`,
			inject:         singleReturnInjectorFactory((*ASTModifier).InjectFuncPointEntry),
			expectedPoints: 1,
			pointValidator: func(t *testing.T, points []LensMonitorMessagePoint) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				assert.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetEntry", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
			},
		},
		{
			name:   "point_finish",
			fnName: "TargetFinish",
			src: `package main
func TargetFinish() {}
func main(){ TargetFinish() }`,
			inject:         singleReturnInjectorFactory((*ASTModifier).InjectFuncPointFinish),
			expectedPoints: 1,
		},
		{
			name:   "point_entry+finish",
			fnName: "TargetBoth",
			src: `package main
func TargetBoth() {}
func main(){ TargetBoth() }`,
			inject: func(m *ASTModifier, fn *Function) ([]int, error) {
				if id1, err := m.InjectFuncPointEntry(fn); err != nil {
					return nil, err
				} else if id2, err := m.InjectFuncPointFinish(fn); err != nil {
					return nil, err
				} else {
					return []int{id1, id2}, nil
				}
			},
			expectedPoints: 2,
		},
		{
			name:   "point_panic_normal",
			fnName: "TargetFinish",
			src: `package main
func TargetFinish() {}
func main(){ TargetFinish() }`,
			inject: singleReturnInjectorFactory((*ASTModifier).InjectFuncPointPanic),
			// no points expected
		},
		{
			name:   "point_panic",
			fnName: "TargetFinish",
			src: `package main
func TargetFinish() { panic("expected") }
func main(){ TargetFinish() }`,
			inject:              singleReturnInjectorFactory((*ASTModifier).InjectFuncPointPanic),
			expectedPanicPoints: 1,
			panicPointValidator: func(t *testing.T, panics []LensMonitorMessagePointPanic) {
				assert.Positive(t, panics[0].TimeNS)
				assert.Equal(t, "expected", panics[0].Message)
			},
		},
		{
			name:   "point_return_state_minimal",
			fnName: "TargetState",
			src: `package main
func TargetState() { }
func main() { TargetState() }`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				require.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetState", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
				assert.Empty(t, p.Fields) // no fields in this example
			},
		},
		{
			name:   "point_return_state_fields",
			fnName: "TargetState",
			src: `package main
import "fmt"

func TargetState(a, b int) int {
	foo := b
	a *= -1
	if bar := foo + 1; bar > 10 {
		fmt.Printf("Test Exec: %d", foo)
	}
	return a
}
func main() {
	_ = TargetState(1, 2)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				require.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetState", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
				assert.Len(t, p.Fields, 3)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, -1, p.Fields[0].Value, 0)
				assert.Equal(t, "b", p.Fields[1].Name)
				assert.InDelta(t, 2, p.Fields[1].Value, 0)
				assert.Equal(t, "foo", p.Fields[2].Name)
				assert.InDelta(t, 2, p.Fields[2].Value, 0)
			},
		},
		{
			name:   "point_return_state_named_return",
			fnName: "TargetState",
			src: `package main
func TargetState(a, b int) (result int) {
	result = b + 1
	a *= -1
	return
}
func main() {
	_ = TargetState(-1, 1)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				require.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetState", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
				assert.Len(t, p.Fields, 3)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 1, p.Fields[0].Value, 0)
				assert.Equal(t, "b", p.Fields[1].Name)
				assert.InDelta(t, 1, p.Fields[1].Value, 0)
				assert.Equal(t, "result", p.Fields[2].Name)
				assert.InDelta(t, 2, p.Fields[2].Value, 0)
			},
		},
		{
			name:   "point_return_state_func_return",
			fnName: "TargetState",
			src: `package main
func value() int { return 10 }
func TargetState(a int) (int, int) {
	return a + 1, value()
}
func main() {
	_, _ = TargetState(1)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				require.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetState", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
				assert.Len(t, p.Fields, 3)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 1, p.Fields[0].Value, 0)
				assert.Equal(t, "ret0", p.Fields[1].Name)
				assert.InDelta(t, 2, p.Fields[1].Value, 0)
				assert.Equal(t, "ret1", p.Fields[2].Name)
				assert.InDelta(t, 10, p.Fields[2].Value, 0)
			},
		},
		{
			name:   "point_return_state_func_multi_field_return",
			fnName: "TargetState",
			src: `package main
func value() (int, int) { return 2, 10 }
func TargetState(a int) (int, int) {
	return value()
}
func main() {
	_, _ = TargetState(1)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				assert.Positive(t, p.TimeNS)
				require.Len(t, p.Stack, 4)
				assert.True(t, strings.HasSuffix(p.Stack[0].File, "/main.go"))
				assert.Equal(t, "main.TargetState", p.Stack[0].Function)
				assert.True(t, strings.HasSuffix(p.Stack[1].File, "/main.go"))
				assert.Equal(t, "main.main", p.Stack[1].Function)
				assert.Len(t, p.Fields, 3)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 1, p.Fields[0].Value, 0)
				assert.Equal(t, "ret0", p.Fields[1].Name)
				assert.InDelta(t, 2, p.Fields[1].Value, 0)
				assert.Equal(t, "ret1", p.Fields[2].Name)
				assert.InDelta(t, 10, p.Fields[2].Value, 0)
			},
		},
		{
			name:   "point_return_state_interface_return",
			fnName: "TargetState",
			src: `package main
func TargetState(a int) interface{} {
	return a
}
func main() {
	_ = TargetState(1)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 2)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 1, p.Fields[0].Value, 0)
				assert.Equal(t, "ret0", p.Fields[1].Name)
				assert.InDelta(t, 1, p.Fields[1].Value, 0)
			},
		},
		{
			name:   "point_return_state_interface_struct",
			fnName: "TargetState",
			src: `package main
type person struct{ Name string; Age int }
func TargetState() interface{} {
       return person{Name: "Bob", Age: 5}
}
func main() {
       _ = TargetState()
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 1)
				f := p.Fields[0]
				assert.Equal(t, "ret0", f.Name)
				assert.Equal(t, "main.person", f.Type)
				require.Len(t, f.Children, 2)
				assert.Equal(t, "Name", f.Children[0].Name)
				assert.Equal(t, "string", f.Children[0].Type)
				assert.Equal(t, "Bob", f.Children[0].Value)
				assert.Equal(t, "Age", f.Children[1].Name)
				assert.Equal(t, "int", f.Children[1].Type)
				assert.InDelta(t, 5, f.Children[1].Value, 0)
			},
		},
		{
			name:   "point_return_state_interface_slice",
			fnName: "TargetState",
			src: `package main
func TargetState() interface{} {
       return []int{1, 2, 3}
}
func main() {
       _ = TargetState()
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 1)
				f := p.Fields[0]
				assert.Equal(t, "ret0", f.Name)
				assert.Equal(t, "[]int", f.Type)
				assert.Equal(t, []interface{}{float64(1), float64(2), float64(3)}, f.Value)
			},
		},
		{
			name:   "point_return_state_interface_map",
			fnName: "TargetState",
			src: `package main
func TargetState() interface{} {
       return map[string]int{"a": 1, "b": 2}
}
func main() {
       _ = TargetState()
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 1)
				f := p.Fields[0]
				assert.Equal(t, "ret0", f.Name)
				assert.Equal(t, "map[string]int", f.Type)
				require.Len(t, f.Children, 2)
				names := []string{f.Children[0].Name, f.Children[1].Name}
				assert.ElementsMatch(t, []string{"a", "b"}, names)
			},
		},
		{
			name:   "point_return_state_generic_return",
			fnName: "TargetState",
			src: `package main
func TargetState[T any](a T) T {
	return a
}
func main() {
	_ = TargetState[int](2)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 2)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 2, p.Fields[0].Value, 0)
				assert.Equal(t, "ret0", p.Fields[1].Name)
				assert.InDelta(t, 2, p.Fields[1].Value, 0)
			},
		},
		{
			name:   "point_return_state_const_return",
			fnName: "TargetState",
			src: `package main
func TargetState() int {
	return 5
}
func main() {
	_ = TargetState()
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 1)
				assert.Equal(t, "int", p.Fields[0].Type)
				assert.Equal(t, "ret0", p.Fields[0].Name)
				assert.InDelta(t, 5, p.Fields[0].Value, 0)
			},
		},
		{
			name:   "point_return_state_alias_param",
			fnName: "TargetState",
			src: `package main
type MyInt = int
func TargetState(a MyInt) int {
	return a
}
func main() {
	_ = TargetState(3)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 1,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				p := points[0]
				require.Len(t, p.Fields, 2)
				for i := range p.Fields {
					assert.Equal(t, "int", p.Fields[i].Type)
				}
				assert.Equal(t, "a", p.Fields[0].Name)
				assert.InDelta(t, 3, p.Fields[0].Value, 0)
				assert.Equal(t, "ret0", p.Fields[1].Name)
				assert.InDelta(t, 3, p.Fields[1].Value, 0)
			},
		},
		{
			name:   "point_return_state_recursive",
			fnName: "TargetState",
			src: `package main
func TargetState(a int) int {
	if a > 4 {
		return a
	}
	return TargetState(a + 1)
}
func main() {
	_ = TargetState(1)
}`,
			inject:              (*ASTModifier).InjectFuncPointReturnStates,
			expectedStatePoints: 5,
			statePointValidator: func(t *testing.T, points []LensMonitorMessagePointState) {
				for i, p := range points {
					assert.Positive(t, p.TimeNS)
					if i > 0 {
						assert.GreaterOrEqual(t, p.TimeNS, points[i-1].TimeNS)
					}
					assert.Len(t, p.Stack, 8-i)
					for i := range p.Fields {
						assert.Equal(t, "int", p.Fields[i].Type)
					}
					if i == 0 {
						require.Len(t, p.Fields, 1)
					} else {
						require.Len(t, p.Fields, 2)
					}
					assert.Equal(t, "a", p.Fields[0].Name)
					assert.InDelta(t, 5-i, p.Fields[0].Value, 0)
					if i > 0 {
						assert.Equal(t, "rec0", p.Fields[1].Name)
						assert.InDelta(t, 5, p.Fields[1].Value, 0)
					}
				}
			},
		},
		{
			name:   "generic_func",
			fnName: "Generic",
			src: `package main
func Generic[T any](v T) T { return v }
func main() { _ = Generic(1) }`,
			inject: func(m *ASTModifier, fn *Function) ([]int, error) {
				id1, err := m.InjectFuncPointEntry(fn)
				if err != nil {
					return nil, err
				}
				id2, err := m.InjectFuncPointFinish(fn)
				if err != nil {
					return nil, err
				}
				ids, err := m.InjectFuncPointReturnStates(fn)
				if err != nil {
					return nil, err
				}
				return append([]int{id1, id2}, ids...), nil
			},
			expectedPoints:      2,
			expectedStatePoints: 1,
		},
		{
			name:   "generic_method_value",
			fnName: "Get",
			src: `package main
type Box[T any] struct{ v T }
func (b Box[T]) Get() T { return b.v }
func main() { b := Box[int]{v: 2}; _ = b.Get() }`,
			inject: func(m *ASTModifier, fn *Function) ([]int, error) {
				id1, err := m.InjectFuncPointEntry(fn)
				if err != nil {
					return nil, err
				}
				id2, err := m.InjectFuncPointFinish(fn)
				if err != nil {
					return nil, err
				}
				ids, err := m.InjectFuncPointReturnStates(fn)
				if err != nil {
					return nil, err
				}
				return append([]int{id1, id2}, ids...), nil
			},
			expectedPoints:      2,
			expectedStatePoints: 1,
			fnIdent:             "main:Box[T].Get",
		},
		{
			name:   "generic_method_ptr",
			fnName: "Set",
			src: `package main
type Box[T any] struct{ v T }
func (b *Box[T]) Set(v T) T { old := b.v; b.v = v; return old }
func main() { b := &Box[int]{v: 3}; _ = b.Set(4) }`,
			inject: func(m *ASTModifier, fn *Function) ([]int, error) {
				id1, err := m.InjectFuncPointEntry(fn)
				if err != nil {
					return nil, err
				}
				id2, err := m.InjectFuncPointFinish(fn)
				if err != nil {
					return nil, err
				}
				ids, err := m.InjectFuncPointReturnStates(fn)
				if err != nil {
					return nil, err
				}
				return append([]int{id1, id2}, ids...), nil
			},
			expectedPoints:      2,
			expectedStatePoints: 1,
			fnIdent:             "main:*Box[T].Set",
		},
	}

	for _, tc := range testCases {
		tc := tc // capture for parallel run
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			tmp := t.TempDir()

			// write out test case application into the directory
			err := os.WriteFile(filepath.Join(tmp, "go.mod"), []byte("module testapp\ngo 1.22\n"), 0o644)
			require.NoError(t, err)
			mainPath := filepath.Join(tmp, "main.go")
			err = os.WriteFile(mainPath, []byte(tc.src), 0o644)
			require.NoError(t, err)

			// choose an unused TCP port
			port := freePort(t)

			// inject the client and test injection points
			mod := &ASTModifier{}
			err = mod.InjectASTClient(tmp, port, 5, 256)
			require.NoError(t, err)
			ident := tc.fnIdent
			if ident == "" {
				ident = "main:" + tc.fnName
			}
			_, err = tc.inject(mod, &Function{
				PackageName:   "main",
				FilePath:      mainPath,
				FunctionName:  tc.fnName,
				FunctionIdent: ident,
			})
			require.NoError(t, err)
			require.NoError(t, mod.Commit())
			// start the monitoring server
			handler := &captureHandler{}
			srv, err := astExecServerStart("127.0.0.1", port, handler)
			require.NoError(t, err)
			t.Cleanup(func() { _ = srv.Stop(t.Context()) })

			// run the instrumented program
			var cmd *exec.Cmd
			if tc.expectedPanicPoints > 0 {
				cmd = NewProjectExec(tmp, nil, "go", "run", ".")
			} else {
				cmd = NewProjectLoggedExec(tmp, nil, "go", "run", ".")
			}
			t.Cleanup(func() { _ = cmd.Process.Kill() })
			err = cmd.Run()
			if tc.expectedPanicPoints == 0 {
				require.NoError(t, err)
			}

			err = srv.StopOnProcessOrTimeout(cmd.Process.Pid, time.Minute)
			require.NoError(t, err)

			// verify point callbacks
			handler.mu.Lock()
			defer handler.mu.Unlock()
			// require len validation so that validation functions know the size has already been validated
			require.Len(t, handler.points, tc.expectedPoints)
			require.Len(t, handler.statePoints, tc.expectedStatePoints)
			require.Len(t, handler.panicPoints, tc.expectedPanicPoints)
			if tc.pointValidator != nil {
				tc.pointValidator(t, handler.points)
			}
			if tc.statePointValidator != nil {
				tc.statePointValidator(t, handler.statePoints)
			}
			if tc.panicPointValidator != nil {
				tc.panicPointValidator(t, handler.panicPoints)
			}
		})
	}
}

func TestCaptureLensMonitorStack(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		skip       int
		expectFunc string // substring we expect to see in the first frame's Function field
	}{
		{
			skip:       1,
			expectFunc: "captureLensMonitorStack",
		},
		{
			skip:       2,
			expectFunc: "dummyFuncLevel2",
		},
		{
			skip:       3,
			expectFunc: "dummyFuncLevel1",
		},
		{
			skip:       4,
			expectFunc: "TestCaptureLensMonitorStack",
		},
	}

	for _, tc := range testCases {
		t.Run("skip"+strconv.Itoa(tc.skip), func(t *testing.T) {
			frames := dummyFuncLevel1(tc.skip)
			require.NotEmpty(t, frames)

			first := frames[0]
			assert.Contains(t, first.Function, tc.expectFunc)
			assert.NotEmpty(t, first.File)
			assert.NotZero(t, first.Line)
		})
	}
}

func dummyFuncLevel1(skip int) []LensMonitorStackFrame {
	return dummyFuncLevel2(skip)
}

func dummyFuncLevel2(skip int) []LensMonitorStackFrame {
	return captureLensMonitorStack(skip)
}

func TestExtensionPointEndToEnd(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}

	t.Parallel()
	tmp := t.TempDir()

	// Source with a helper function to monitor via extension points
	src := `package main
import "fmt"

func Helper(x int) int {
	return x * 2
}

func Target(a int) int {
	val := Helper(a)
	return val + 10
}

func main() {
	result := Target(5)
	fmt.Println(result)
}`

	err := os.WriteFile(filepath.Join(tmp, "go.mod"), []byte("module testapp\ngo 1.22\n"), 0o644)
	require.NoError(t, err)
	mainPath := filepath.Join(tmp, "main.go")
	err = os.WriteFile(mainPath, []byte(src), 0o644)
	require.NoError(t, err)

	port := freePort(t)

	// Inject AST client
	mod := &ASTModifier{}
	err = mod.InjectASTClient(tmp, port, 5, 256)
	require.NoError(t, err)

	// Inject regular monitoring on Target function
	targetFunc := &Function{
		PackageName:   "main",
		FilePath:      mainPath,
		FunctionName:  "Target",
		FunctionIdent: "main:Target",
	}
	targetPointIds, err := mod.InjectFuncPointReturnStates(targetFunc)
	require.NoError(t, err)

	// Inject extension monitoring on Helper function (simulating security sink monitoring)
	helperFunc := &Function{
		PackageName:   "main",
		FilePath:      mainPath,
		FunctionName:  "Helper",
		FunctionIdent: "main:Helper",
	}
	helperPointIds, err := mod.InjectFuncPointReturnStates(helperFunc)
	require.NoError(t, err)

	// Configure extension points mapping
	extensionKey := "test:helper:call"
	extensionPoints := make(map[int]*string)
	for _, pointId := range helperPointIds {
		extensionPoints[pointId] = &extensionKey
	}

	// Configure regular project points mapping
	targetKey := "main:Target"
	projectPoints := make(map[int]*string)
	for _, pointId := range targetPointIds {
		projectPoints[pointId] = &targetKey
	}

	require.NoError(t, mod.Commit())

	// Start monitoring server with testMonitor to route messages
	srv, err := astExecServerStart("127.0.0.1", port, nil)
	require.NoError(t, err)
	t.Cleanup(func() { _ = srv.Stop(t.Context()) })

	monitor := newTestMonitor(nil, "", tmp,
		projectPoints,         // projectStatePointIdToIdent
		make(map[int]*string), // projectPanicPointIdToIdent
		make(map[int]*string), // moduleEntryPointIdToIdent
		make(map[int]*string), // modulePanicPointIdToIdent
		extensionPoints,       // extensionStatePointIdToIdent
	)
	err = srv.SetPointHandler(monitor)
	require.NoError(t, err)

	// Run the instrumented program
	cmd := NewProjectLoggedExec(tmp, nil, "go", "run", ".")
	t.Cleanup(func() { _ = cmd.Process.Kill() })
	err = cmd.Run()
	require.NoError(t, err)

	err = srv.StopOnProcessOrTimeout(cmd.Process.Pid, time.Minute)
	require.NoError(t, err)

	// Wait for async processing
	monitor.wait.Wait()

	// Verify regular caller results were captured
	require.Contains(t, monitor.callerFrames, targetKey)
	targetFrames := monitor.callerFrames[targetKey]
	require.NotEmpty(t, targetFrames)

	// Verify target frame captured the expected fields (a, val, ret0)
	targetFV := targetFrames[0].FieldValues.FlattenFieldValues()
	require.Contains(t, targetFV, "a")
	require.Contains(t, targetFV, "val")
	require.Contains(t, targetFV, "ret0")

	// Verify extension frames were captured for helper function
	require.Contains(t, monitor.extensionFrames, extensionKey)
	extFrames := monitor.extensionFrames[extensionKey]
	require.NotEmpty(t, extFrames)

	// Verify extension frame captured the expected fields (x, ret0)
	extFV := extFrames[0].FieldValues.FlattenFieldValues()
	require.Contains(t, extFV, "x")
	assert.Equal(t, "5", extFV["x"])
	require.Contains(t, extFV, "ret0")
	assert.Equal(t, "10", extFV["ret0"])

	// Verify both have stack traces
	require.NotEmpty(t, targetFrames[0].Stack)
	require.NotEmpty(t, extFrames[0].Stack)
}
