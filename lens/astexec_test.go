package lens

import (
	"bytes"
	"fmt"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestCollectFields(t *testing.T) {
	t.Parallel()

	t.Run("simple", func(t *testing.T) {
		fields := make(FieldValues)
		collectFields(fields, "int", int64(7), "int64", nil)
		collectFields(fields, "str", "s", "string", nil)

		assert.Equal(t, map[string]string{
			"int": "7",
			"str": "s",
		}, fields.FlattenFieldValues())
	})

	t.Run("nested", func(t *testing.T) {
		fields := make(FieldValues)
		collectFields(fields, "parent", nil, "struct", []LensMonitorField{
			{Name: "child", Type: "string", Value: "v"},
			{Name: "nest", Type: "struct", Children: []LensMonitorField{
				{Name: "inner", Type: "int", Value: int64(1)},
			}},
		})

		assert.Equal(t, map[string]string{
			"parent.child":      "v",
			"parent.nest.inner": "1",
		}, fields.FlattenFieldValues())
	})

	t.Run("long_nonstring", func(t *testing.T) {
		fields := make(FieldValues)
		slice := make([]int, 200)
		collectFields(fields, "big", slice, "[]int", nil)

		vals := fields.FlattenFieldValues()
		val, ok := vals["big"]
		require.True(t, ok)
		require.True(t, strings.HasPrefix(val, HashFieldValuePrefix))
		assert.NotEqual(t, fmt.Sprint(slice), val)
	})
}

func TestTestResultStableFields(t *testing.T) {
	t.Parallel()

	t.Run("caller_results", func(t *testing.T) {
		t.Parallel()

		r1 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			CallerResults: map[string][]CallFrame{
				"caller1": {
					{
						FieldValues: FieldValues{
							"same":  &FieldValue{Value: "val"},
							"diff":  &FieldValue{Value: "r1"},
							"extra": &FieldValue{Value: "only1"},
						},
						Stack: []StackFrame{
							{File: "file1", Line: 1, Function: "func1"},
						},
					},
				},
			},
			ProjectPanics: map[string][]string{
				"caller1": {"p1", "p2"},
			},
			ModulePanics: map[string][]string{
				"modFn": {"m1"},
			},
			ModuleChangesHit: 1,
			TestFailure:      false,
		}

		r2 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			CallerResults: map[string][]CallFrame{
				"caller1": {
					{
						FieldValues: FieldValues{
							"same":  &FieldValue{Value: "val"},
							"diff":  &FieldValue{Value: "r2"},
							"other": &FieldValue{Value: "ignored"},
						},
						Stack: []StackFrame{
							{File: "file1", Line: 1, Function: "func1"},
						},
					},
				},
			},
			ProjectPanics: map[string][]string{
				"caller1": {"p2", "p3"},
			},
			ModulePanics: map[string][]string{
				"modFn": {"m2"},
			},
			ModuleChangesHit: 2,
			TestFailure:      true,
		}

		result := testResultStableFields(r1, r2)

		require.Equal(t, r1.TestFunction, result.TestFunction)
		assert.True(t, result.TestFailure)
		assert.Equal(t, r1.ModuleChangesHit, result.ModuleChangesHit)

		frames, ok := result.CallerResults["caller1"]
		require.True(t, ok)
		require.Len(t, frames, 1)
		assert.Equal(t, map[string]string{"same": "val"}, frames[0].FieldValues.FlattenFieldValues())
		assert.Equal(t, []string{"p2"}, result.ProjectPanics["caller1"])
		_, ok = result.ModulePanics["modFn"]
		assert.False(t, ok)
	})

	t.Run("extension_frames", func(t *testing.T) {
		t.Parallel()

		r1 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			CallerResults: map[string][]CallFrame{
				"caller1": {
					{
						FieldValues: FieldValues{
							"same": &FieldValue{Value: "val"},
							"diff": &FieldValue{Value: "r1"},
						},
						Stack: []StackFrame{{File: "file1", Line: 1, Function: "func1"}},
					},
				},
			},
			ExtensionFrames: map[string][]CallFrame{
				"security:network:dial": {
					{
						FieldValues: FieldValues{
							"addr":  &FieldValue{Value: "127.0.0.1"},
							"port":  &FieldValue{Value: "8080"},
							"extra": &FieldValue{Value: "only1"},
						},
						Stack: []StackFrame{{File: "./app.go", Line: 10, Function: "dialServer"}},
					},
				},
				"security:file:open": {
					{
						FieldValues: FieldValues{
							"path": &FieldValue{Value: "/tmp/test"},
						},
						Stack: []StackFrame{{File: "./app.go", Line: 20, Function: "openFile"}},
					},
				},
			},
			ModuleChangesHit: 1,
			TestFailure:      false,
		}

		r2 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			CallerResults: map[string][]CallFrame{
				"caller1": {
					{
						FieldValues: FieldValues{
							"same":  &FieldValue{Value: "val"},
							"diff":  &FieldValue{Value: "r2"},
							"other": &FieldValue{Value: "ignored"},
						},
						Stack: []StackFrame{{File: "file1", Line: 1, Function: "func1"}},
					},
				},
			},
			ExtensionFrames: map[string][]CallFrame{
				"security:network:dial": {
					{
						FieldValues: FieldValues{
							"addr":  &FieldValue{Value: "127.0.0.1"},
							"port":  &FieldValue{Value: "8080"},
							"other": &FieldValue{Value: "only2"},
						},
						Stack: []StackFrame{{File: "./app.go", Line: 10, Function: "dialServer"}},
					},
				},
				"security:file:open": {
					{
						FieldValues: FieldValues{
							"path": &FieldValue{Value: "/tmp/different"},
						},
						Stack: []StackFrame{{File: "./app.go", Line: 20, Function: "openFile"}},
					},
				},
			},
			ModuleChangesHit: 2,
			TestFailure:      true,
		}

		result := testResultStableFields(r1, r2)

		require.Equal(t, r1.TestFunction, result.TestFunction)
		assert.True(t, result.TestFailure)
		assert.Equal(t, r1.ModuleChangesHit, result.ModuleChangesHit)

		// Verify caller results stability
		frames, ok := result.CallerResults["caller1"]
		require.True(t, ok)
		require.Len(t, frames, 1)
		assert.Equal(t, map[string]string{"same": "val"}, frames[0].FieldValues.FlattenFieldValues())

		// Verify extension frames stability
		extFrames, ok := result.ExtensionFrames["security:network:dial"]
		require.True(t, ok)
		require.Len(t, extFrames, 1)
		assert.Equal(t, map[string]string{"addr": "127.0.0.1", "port": "8080"},
			extFrames[0].FieldValues.FlattenFieldValues())

		extFileFrames, ok := result.ExtensionFrames["security:file:open"]
		require.True(t, ok)
		require.Len(t, extFileFrames, 1)
		// path differs between runs, so should be empty
		assert.Empty(t, extFileFrames[0].FieldValues.FlattenFieldValues())
	})

	t.Run("extension_frames_missing", func(t *testing.T) {
		t.Parallel()

		r1 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			ExtensionFrames: map[string][]CallFrame{
				"security:network:dial": {
					{
						FieldValues: FieldValues{
							"addr": &FieldValue{Value: "127.0.0.1"},
						},
						Stack: []StackFrame{{File: "./app.go", Line: 10, Function: "dialServer"}},
					},
				},
			},
		}

		r2 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			// No extension frames in second run
		}

		result := testResultStableFields(r1, r2)

		// Extension frames should not be present in result when missing in second run
		assert.Empty(t, result.ExtensionFrames)
	})

	t.Run("reordered", func(t *testing.T) {
		t.Parallel()

		stackA := []StackFrame{{File: "a.go", Line: 1, Function: "fa"}}
		stackB := []StackFrame{{File: "b.go", Line: 2, Function: "fb"}}

		r1 := TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "TestFn"},
			CallerResults: map[string][]CallFrame{
				"caller": {
					{
						FieldValues: FieldValues{
							"same": &FieldValue{Value: "shared"},
							"a":    &FieldValue{Value: "1"},
						},
						Stack: stackA,
					},
					{
						FieldValues: FieldValues{
							"same": &FieldValue{Value: "shared"},
							"b":    &FieldValue{Value: "1"},
						},
						Stack: stackB,
					},
				},
			},
		}

		r2 := TestResult{
			TestFunction: r1.TestFunction,
			CallerResults: map[string][]CallFrame{
				"caller": {
					{
						FieldValues: FieldValues{
							"same": &FieldValue{Value: "shared"},
							"b":    &FieldValue{Value: "2"},
						},
						Stack: stackB,
					},
					{
						FieldValues: FieldValues{
							"same": &FieldValue{Value: "shared"},
							"a":    &FieldValue{Value: "2"},
						},
						Stack: stackA,
					},
				},
			},
		}

		result := testResultStableFields(r1, r2)

		frames := result.CallerResults["caller"]
		require.Len(t, frames, 2)
		for _, cf := range frames {
			assert.Equal(t, map[string]string{"same": "shared"}, cf.FieldValues.FlattenFieldValues())
		}
	})
}

func TestStableFieldValues(t *testing.T) {
	t.Parallel()

	t.Run("partial_match", func(t *testing.T) {
		f1 := FieldValues{
			"root": &FieldValue{Children: FieldValues{
				"child1": &FieldValue{Value: "shared"},
				"child2": &FieldValue{Value: "a"},
			}},
		}
		f2 := FieldValues{
			"root": &FieldValue{Children: FieldValues{
				"child1": &FieldValue{Value: "shared"},
				"child2": &FieldValue{Value: "b"},
			}},
		}
		got := stableFieldValues(f1, f2)
		assert.Equal(t, map[string]string{"root.child1": "shared"}, got.FlattenFieldValues())
	})

	t.Run("leaf_vs_node", func(t *testing.T) {
		f1 := FieldValues{
			"root": &FieldValue{Children: FieldValues{
				"child": &FieldValue{Value: "shared"},
			}},
		}
		f2 := FieldValues{
			"root": &FieldValue{Value: "shared"},
		}
		got := stableFieldValues(f1, f2)
		assert.Empty(t, got)
	})

	t.Run("deep_match", func(t *testing.T) {
		f1 := FieldValues{
			"root": &FieldValue{Children: FieldValues{
				"lvl1": &FieldValue{Children: FieldValues{
					"lvl2": &FieldValue{Value: "shared"},
				}},
			}},
		}
		f2 := FieldValues{
			"root": &FieldValue{Children: FieldValues{
				"lvl1": &FieldValue{Children: FieldValues{
					"lvl2": &FieldValue{Value: "shared"},
				}},
			}},
		}
		got := stableFieldValues(f1, f2)
		assert.Equal(t, map[string]string{"root.lvl1.lvl2": "shared"}, got.FlattenFieldValues())
	})
}

func TestProjectFrames(t *testing.T) {
	in := StackFrame{File: "./in.go", Line: 1, Function: "f"}
	out := StackFrame{File: "/ext/out.go", Line: 2, Function: "f"}
	frames := []StackFrame{in, out}

	got := ProjectFrames(frames)
	require.Len(t, got, 1)
	assert.Equal(t, in, got[0])
}

func TestStackFramesKey(t *testing.T) {
	f1 := StackFrame{File: "a.go", Line: 1, Function: "fa"}
	f2 := StackFrame{File: "b.go", Line: 2, Function: "fb"}

	var bb bytes.Buffer
	key1 := StackFramesKey(&bb, []StackFrame{f1, f2})
	key2 := StackFramesKey(&bb, []StackFrame{f1, f2})
	key3 := StackFramesKey(&bb, []StackFrame{f2, f1})

	assert.Equal(t, key1, key2)
	assert.NotEqual(t, key1, key3)
}

func TestTrimStackFile(t *testing.T) {
	dir := filepath.Join("/tmp", "project")
	in := filepath.Join(dir, "pkg", "file.go")
	got := trimStackFile(dir, "", in)
	assert.Equal(t, "./pkg/file.go", got)

	mod := filepath.Join(dir, "..", "pkg", "mod", "github.com", "foo@v1.0.0", "bar.go")
	got = trimStackFile(dir, "", mod)
	assert.Equal(t, "github.com/foo@v1.0.0/bar.go", got)
}
