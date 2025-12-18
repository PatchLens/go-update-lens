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
		// Empty parent type for top-level fields
		collectFields(fields, "int", int64(7), "int64", nil, "")
		collectFields(fields, "str", "s", "string", nil, "")

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
		}, "")

		assert.Equal(t, map[string]string{
			"parent.child":      "v",
			"parent.nest.inner": "1",
		}, fields.FlattenFieldValues())
	})

	t.Run("long_nonstring", func(t *testing.T) {
		fields := make(FieldValues)
		slice := make([]int, 200)
		collectFields(fields, "big", slice, "[]int", nil, "")

		vals := fields.FlattenFieldValues()
		val, ok := vals["big"]
		require.True(t, ok)
		require.True(t, strings.HasPrefix(val, HashFieldValuePrefix))
		assert.NotEqual(t, fmt.Sprint(slice), val)
	})

	t.Run("reflection_filtering", func(t *testing.T) {
		// Test type-based filtering - should filter out internal reflect.Value metadata
		fields := make(FieldValues)
		collectFields(fields, "arg0", nil, "reflect.Value", []LensMonitorField{
			// These internal fields should be filtered out
			{Name: "typ_", Type: "reflect.rtype", Children: []LensMonitorField{
				{Name: "Hash", Type: "uint32", Value: uint32(123)},
				{Name: "Str", Type: "string", Value: "someType"},
			}},
			{Name: "flag", Type: "reflect.flag", Value: uintptr(456)},
			{Name: "ptr", Type: "unsafe.Pointer", Value: "0x12345"},
			// This field should be kept (actual data)
			{Name: "data", Type: "string", Value: "important"},
		}, "")

		// Only non-internal fields should remain
		flattened := fields.FlattenFieldValues()
		assert.Contains(t, flattened, "arg0.data")
		assert.Equal(t, "important", flattened["arg0.data"])

		// Internal fields should be filtered out
		assert.NotContains(t, flattened, "arg0.typ_")
		assert.NotContains(t, flattened, "arg0.flag")
		assert.NotContains(t, flattened, "arg0.ptr")
	})

	t.Run("reflection_keeps_data_fields", func(t *testing.T) {
		// Test that actual data fields are kept (not filtered)
		fields := make(FieldValues)
		collectFields(fields, "arg0", "targetValue", "string", nil, "")
		collectFields(fields, "arg1", int64(42), "int", nil, "")

		flattened := fields.FlattenFieldValues()
		assert.Equal(t, map[string]string{
			"arg0": "targetValue",
			"arg1": "42",
		}, flattened)
	})

	t.Run("non_reflection_no_filtering", func(t *testing.T) {
		// Test that fields with names like "typ_", "flag", "ptr" are kept when parent is not reflect.Value
		fields := make(FieldValues)
		collectFields(fields, "value", nil, "CustomStruct", []LensMonitorField{
			{Name: "typ_", Type: "string", Value: "someType"}, // Would be filtered if parent was reflect.Value
			{Name: "flag", Type: "int", Value: int64(123)},    // Would be filtered if parent was reflect.Value
			{Name: "ptr", Type: "string", Value: "pointer"},   // Would be filtered if parent was reflect.Value
			{Name: "data", Type: "string", Value: "content"},
		}, "")

		// All fields should be present (no filtering for non-reflect.Value parent)
		flattened := fields.FlattenFieldValues()
		assert.Len(t, flattened, 4)
		assert.Equal(t, "someType", flattened["value.typ_"])
		assert.Equal(t, "123", flattened["value.flag"])
		assert.Equal(t, "pointer", flattened["value.ptr"])
		assert.Equal(t, "content", flattened["value.data"])
	})

	t.Run("nested_reflection_filtering", func(t *testing.T) {
		// Test nested reflect.Value structures - all internal fields should be filtered
		fields := make(FieldValues)
		collectFields(fields, "outer", nil, "reflect.Value", []LensMonitorField{
			{Name: "typ_", Type: "reflect.rtype", Value: "ignored"},
			{Name: "inner", Type: "reflect.Value", Children: []LensMonitorField{
				{Name: "typ_", Type: "reflect.rtype", Value: "also_ignored"},
				{Name: "flag", Type: "reflect.flag", Value: uintptr(123)},
				{Name: "actualData", Type: "string", Value: "keep_this"},
			}},
		}, "")

		flattened := fields.FlattenFieldValues()
		// The nested actual data should be kept
		assert.Contains(t, flattened, "outer.inner.actualData")
		assert.Equal(t, "keep_this", flattened["outer.inner.actualData"])

		// All internal fields should be filtered
		assert.NotContains(t, flattened, "outer.typ_")
		assert.NotContains(t, flattened, "outer.inner.typ_")
		assert.NotContains(t, flattened, "outer.inner.flag")
	})

	t.Run("mixed_reflection_and_custom_types", func(t *testing.T) {
		// Test mixed scenario: reflect.Value containing a custom type with similar field names
		fields := make(FieldValues)
		collectFields(fields, "arg", nil, "reflect.Value", []LensMonitorField{
			{Name: "typ_", Type: "reflect.rtype", Value: "filtered"},
			{Name: "ptr", Type: "unsafe.Pointer", Value: "filtered"},
			{Name: "customStruct", Type: "MyStruct", Children: []LensMonitorField{
				// These should NOT be filtered because parent is not reflect.Value
				{Name: "typ_", Type: "string", Value: "not_filtered"},
				{Name: "flag", Type: "int", Value: int64(99)},
				{Name: "data", Type: "string", Value: "important"},
			}},
		}, "")

		flattened := fields.FlattenFieldValues()

		// reflect.Value internals should be filtered
		assert.NotContains(t, flattened, "arg.typ_")
		assert.NotContains(t, flattened, "arg.ptr")

		// Custom struct fields should NOT be filtered (parent is MyStruct, not reflect.Value)
		assert.Contains(t, flattened, "arg.customStruct.typ_")
		assert.Equal(t, "not_filtered", flattened["arg.customStruct.typ_"])
		assert.Contains(t, flattened, "arg.customStruct.flag")
		assert.Equal(t, "99", flattened["arg.customStruct.flag"])
		assert.Contains(t, flattened, "arg.customStruct.data")
		assert.Equal(t, "important", flattened["arg.customStruct.data"])
	})

	t.Run("reflect_rtype_and_flag_filtering", func(t *testing.T) {
		// Test that reflect.rtype and reflect.flag types are filtered regardless of parent
		fields := make(FieldValues)
		collectFields(fields, "container", nil, "SomeStruct", []LensMonitorField{
			{Name: "metadata", Type: "reflect.rtype", Children: []LensMonitorField{
				{Name: "Size", Type: "uintptr", Value: uintptr(8)},
			}},
			{Name: "flags", Type: "reflect.flag", Value: uintptr(456)},
			{Name: "normal", Type: "string", Value: "keep"},
		}, "")

		flattened := fields.FlattenFieldValues()

		// reflect.rtype and reflect.flag should be filtered even in non-reflect.Value parent
		assert.NotContains(t, flattened, "container.metadata")
		assert.NotContains(t, flattened, "container.metadata.Size")
		assert.NotContains(t, flattened, "container.flags")

		// Normal fields should be kept
		assert.Contains(t, flattened, "container.normal")
		assert.Equal(t, "keep", flattened["container.normal"])
	})

	t.Run("deeply_nested_with_reflect_at_multiple_levels", func(t *testing.T) {
		// Test deep nesting with reflect.Value at multiple levels
		fields := make(FieldValues)
		collectFields(fields, "level1", nil, "CustomType", []LensMonitorField{
			{Name: "data1", Type: "string", Value: "keep1"},
			{Name: "level2", Type: "reflect.Value", Children: []LensMonitorField{
				{Name: "typ_", Type: "reflect.rtype", Value: "filter1"},
				{Name: "data2", Type: "string", Value: "keep2"},
				{Name: "level3", Type: "AnotherType", Children: []LensMonitorField{
					{Name: "typ_", Type: "string", Value: "keep3"}, // Not filtered, parent is AnotherType
					{Name: "level4", Type: "reflect.Value", Children: []LensMonitorField{
						{Name: "ptr", Type: "unsafe.Pointer", Value: "filter2"},
						{Name: "data4", Type: "string", Value: "keep4"},
					}},
				}},
			}},
		}, "")

		flattened := fields.FlattenFieldValues()

		// Data at all levels should be kept
		assert.Equal(t, "keep1", flattened["level1.data1"])
		assert.Equal(t, "keep2", flattened["level1.level2.data2"])
		assert.Equal(t, "keep3", flattened["level1.level2.level3.typ_"]) // Not filtered
		assert.Equal(t, "keep4", flattened["level1.level2.level3.level4.data4"])

		// reflect.Value internals should be filtered at appropriate levels
		assert.NotContains(t, flattened, "level1.level2.typ_")              // Filtered (parent is reflect.Value)
		assert.NotContains(t, flattened, "level1.level2.level3.level4.ptr") // Filtered (parent is reflect.Value)
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

func TestFilterModulesByGoVersion(t *testing.T) {
	t.Parallel()

	t.Run("skip_old_go_version", func(t *testing.T) {
		t.Parallel()

		oldModule := &ModuleChange{Name: "old/module", GoVersion: "1.12"}
		newModule := &ModuleChange{Name: "new/module", GoVersion: "1.18"}

		reachable := ReachableModuleChange{
			"old/module.OldFunc": &ModuleFunction{
				Function: Function{FunctionIdent: "old/module.OldFunc"},
				Module:   oldModule,
			},
			"new/module.NewFunc": &ModuleFunction{
				Function: Function{FunctionIdent: "new/module.NewFunc"},
				Module:   newModule,
			},
		}

		filtered, skipped := FilterModulesByGoVersion(reachable)

		assert.Equal(t, 1, skipped)
		assert.Len(t, filtered, 1)
		assert.Equal(t, "new/module.NewFunc", filtered[0].FunctionIdent)
	})

	t.Run("skip_multiple_functions_same_module", func(t *testing.T) {
		t.Parallel()

		oldModule := &ModuleChange{Name: "old/module", GoVersion: "1.12"}

		reachable := ReachableModuleChange{
			"old/module.Func1": &ModuleFunction{
				Function: Function{FunctionIdent: "old/module.Func1"},
				Module:   oldModule,
			},
			"old/module.Func2": &ModuleFunction{
				Function: Function{FunctionIdent: "old/module.Func2"},
				Module:   oldModule,
			},
			"old/module.Func3": &ModuleFunction{
				Function: Function{FunctionIdent: "old/module.Func3"},
				Module:   oldModule,
			},
		}

		filtered, skipped := FilterModulesByGoVersion(reachable)

		assert.Equal(t, 3, skipped)
		assert.Empty(t, filtered)
	})

	t.Run("keep_all_with_new_versions", func(t *testing.T) {
		t.Parallel()

		mod13 := &ModuleChange{Name: "mod13", GoVersion: "1.13"}
		mod18 := &ModuleChange{Name: "mod18", GoVersion: "1.18"}
		mod21 := &ModuleChange{Name: "mod21", GoVersion: "1.21"}

		reachable := ReachableModuleChange{
			"mod13.Func": &ModuleFunction{
				Function: Function{FunctionIdent: "mod13.Func"},
				Module:   mod13,
			},
			"mod18.Func": &ModuleFunction{
				Function: Function{FunctionIdent: "mod18.Func"},
				Module:   mod18,
			},
			"mod21.Func": &ModuleFunction{
				Function: Function{FunctionIdent: "mod21.Func"},
				Module:   mod21,
			},
		}

		filtered, skipped := FilterModulesByGoVersion(reachable)

		assert.Equal(t, 0, skipped)
		assert.Len(t, filtered, 3)
	})

	t.Run("keep_module_with_empty_go_version", func(t *testing.T) {
		t.Parallel()

		modNoVersion := &ModuleChange{Name: "mod/noversion", GoVersion: ""}

		reachable := ReachableModuleChange{
			"mod/noversion.Func": &ModuleFunction{
				Function: Function{FunctionIdent: "mod/noversion.Func"},
				Module:   modNoVersion,
			},
		}

		filtered, skipped := FilterModulesByGoVersion(reachable)

		assert.Equal(t, 0, skipped)
		assert.Len(t, filtered, 1)
	})
}
