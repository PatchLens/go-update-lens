package lens

import (
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"github.com/vmihailenco/msgpack/v5"
)

// baselineTestResult mirrors TestResult without dictionaries for comparisons
type baselineTestResult struct {
	TestFunction     MinimumTestFunction    `msgpack:"tf"`
	CallerResults    map[string][]CallFrame `msgpack:"cr"`
	ProjectPanics    map[string][]string    `msgpack:"pp,omitempty"`
	ModulePanics     map[string][]string    `msgpack:"mp,omitempty"`
	ModuleChangesHit int                    `msgpack:"mh"`
	TestFailure      bool                   `msgpack:"fail"`
}

func encodeBaseline(tr *TestResult) ([]byte, error) {
	simple := baselineTestResult{
		TestFunction:     tr.TestFunction,
		CallerResults:    tr.CallerResults,
		ProjectPanics:    tr.ProjectPanics,
		ModulePanics:     tr.ModulePanics,
		ModuleChangesHit: tr.ModuleChangesHit,
		TestFailure:      tr.TestFailure,
	}
	return msgpack.Marshal(simple)
}

func TestStackFrame(t *testing.T) {
	t.Run("id", func(t *testing.T) {
		t.Parallel()

		sf1 := &StackFrame{File: "fileA", Function: "Fn", Line: 42}
		sf2 := &StackFrame{File: "fileA", Function: "Fn", Line: 42}
		sf3 := &StackFrame{File: "fileB", Function: "Fn", Line: 42}

		id1 := sf1.ID()
		id2 := sf2.ID()
		id3 := sf3.ID()

		// identical content -> identical ID
		assert.Equal(t, id1, id2)
		// differing file -> different ID
		assert.NotEqual(t, id1, id3)
	})

	t.Run("equal", func(t *testing.T) {
		t.Parallel()

		sf := &StackFrame{File: "file", Function: "fn", Line: 1}

		// same pointer
		require.True(t, sf.Equal(sf))

		// same content, different instance
		otherSame := &StackFrame{File: "file", Function: "fn", Line: 1}
		assert.True(t, sf.Equal(otherSame))

		// different file
		diffFile := &StackFrame{File: "file2", Function: "fn", Line: 1}
		assert.False(t, sf.Equal(diffFile))

		// different line
		diffLine := &StackFrame{File: "file", Function: "fn", Line: 2}
		assert.False(t, sf.Equal(diffLine))

		// different function
		diffFn := &StackFrame{File: "file", Function: "fn2", Line: 1}
		assert.False(t, sf.Equal(diffFn))
	})
}

func TestTestResultMsgpackEncoding(t *testing.T) {
	dupNestedNode := func() *FieldValue {
		return &FieldValue{
			Value:    "dup",
			Children: FieldValues{"leaf": &FieldValue{Value: "val"}},
		}
	}
	dupNestedFieldValues := func() FieldValues {
		return FieldValues{
			"first":  dupNestedNode(),
			"second": dupNestedNode(),
		}
	}
	dupStack := func() []StackFrame {
		return []StackFrame{
			{File: "file.go", Line: 1, Function: "fn1"},
			{File: "file.go", Line: 2, Function: "fn2"},
		}
	}

	// Define all test case structures early so they can be reused by tests

	// Basic test case - simple structure
	basicTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.func",
			FunctionName:  "TestFunc",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{
					FieldValues: FieldValues{
						"field1": &FieldValue{Value: "value1"},
						"field2": &FieldValue{Value: "value2"},
					},
					Stack: []StackFrame{
						{File: "file1.go", Line: 10, Function: "func1"},
						{File: "file2.go", Line: 20, Function: "func2"},
					},
					TimeMillis: 100,
				},
			},
		},
		ProjectPanics:    map[string][]string{"panic1": {"msg1"}},
		ModulePanics:     map[string][]string{"panic2": {"msg2"}},
		ModuleChangesHit: 5,
		TestFailure:      false,
	}

	// Shared reference test case - exact same references
	sharedFV := FieldValues{
		"shared": &FieldValue{Value: "sharedValue"},
		"common": &FieldValue{Value: "commonValue"},
	}
	sharedRefTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.func",
			FunctionName:  "TestFunc",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{FieldValues: sharedFV, Stack: []StackFrame{{File: "f1", Line: 1, Function: "fn1"}}, TimeMillis: 10},
				{FieldValues: sharedFV, Stack: []StackFrame{{File: "f2", Line: 2, Function: "fn2"}}, TimeMillis: 20},
			},
			"caller2": {
				{FieldValues: sharedFV, Stack: []StackFrame{{File: "f3", Line: 3, Function: "fn3"}}, TimeMillis: 30},
			},
		},
	}

	// Edge cases test case - nil and empty values
	edgeCasesTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.func",
			FunctionName:  "TestFunc",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{
					FieldValues: FieldValues{
						"nil_children": &FieldValue{Value: "value", Children: nil},
					},
				},
				{
					FieldValues: nil,
					Stack:       nil,
				},
			},
		},
	}

	// complex nested structure
	complexNestedTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "github.com/example/package.TestFunction",
			FunctionName:  "TestFunction",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{
					FieldValues: FieldValues{
						"field1": &FieldValue{Value: "value1"},
						"nested": &FieldValue{
							Value: "parent",
							Children: FieldValues{
								"child": &FieldValue{Value: "childValue"},
							},
						},
					},
					Stack: []StackFrame{
						{File: "test.go", Line: 100, Function: "testFunc"},
						{File: "main.go", Line: 50, Function: "main"},
					},
				},
				{
					FieldValues: FieldValues{
						"field2": &FieldValue{Value: "value2"},
					},
					Stack: []StackFrame{
						{File: "other.go", Line: 200, Function: "otherFunc"},
					},
				},
			},
			"caller2": {
				{
					FieldValues: FieldValues{
						"shared": &FieldValue{Value: "sharedValue"},
					},
					Stack: []StackFrame{
						{File: "test.go", Line: 100, Function: "testFunc"},
					},
				},
			},
		},
		ProjectPanics:    map[string][]string{"projPanic": {"panic message"}},
		ModulePanics:     map[string][]string{"modPanic": {"mod panic message"}},
		ModuleChangesHit: 42,
		TestFailure:      true,
	}

	// another nested structure (showed bug at one point)
	nestedSharedNode := func() *FieldValue {
		return &FieldValue{
			Value: "repeated value",
			Children: FieldValues{
				"child1": &FieldValue{Value: "nested child value"},
				"child2": &FieldValue{Value: "another nested child value"},
			},
		}
	}
	nestedSharedFV := func() FieldValues {
		return FieldValues{
			"repeated": nestedSharedNode(),
			"common":   &FieldValue{Value: "common value"},
		}
	}
	nestedTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.func",
			FunctionName:  "TestFunc",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{FieldValues: nestedSharedFV(), Stack: []StackFrame{{File: "f1", Line: 1, Function: "fn1"}}},
				{FieldValues: nestedSharedFV(), Stack: []StackFrame{{File: "f2", Line: 2, Function: "fn2"}}},
			},
		},
	}

	// Logical deduplication test case - logically identical but separate instances
	createSharedFV := func() FieldValues {
		return FieldValues{
			"field1": &FieldValue{Value: "shared value 1"},
			"field2": &FieldValue{Value: "shared value 2"},
		}
	}
	logicalDeduplicationTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.func",
			FunctionName:  "TestFunc",
		},
		CallerResults: map[string][]CallFrame{
			"caller1": {
				{FieldValues: createSharedFV(), Stack: []StackFrame{{File: "f1", Line: 1, Function: "fn1"}}},
				{FieldValues: createSharedFV(), Stack: []StackFrame{{File: "f2", Line: 2, Function: "fn2"}}},
			},
			"caller2": {
				{FieldValues: createSharedFV(), Stack: []StackFrame{{File: "f3", Line: 3, Function: "fn3"}}},
			},
		},
	}

	// High duplication test case - many duplicates for compression testing
	createSharedNode := func() *FieldValue {
		return &FieldValue{
			Value: "this is a repeated value that appears many times and should be heavily compressed",
			Children: FieldValues{
				"child1": &FieldValue{Value: "nested child value"},
				"child2": &FieldValue{Value: "another nested child value"},
			},
		}
	}
	createSharedFVHighDup := func() FieldValues {
		return FieldValues{
			"repeated": createSharedNode(),
			"common":   &FieldValue{Value: "common value"},
		}
	}
	createSharedStack := func() []StackFrame {
		return []StackFrame{
			{File: "/long/path/to/source/file.go", Line: 12345, Function: "github.com/example/project/pkg.(*Handler).ProcessRequest"},
			{File: "/another/long/path/to/file.go", Line: 67890, Function: "github.com/example/project/internal.(*Service).Handle"},
		}
	}
	highDuplicationTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "github.com/example/project/test.TestSomething",
			FunctionName:  "TestSomething",
		},
		CallerResults: make(map[string][]CallFrame),
	}
	// Create many callers with logically identical but separate instances
	for i := 0; i < 100; i++ {
		callerName := "caller" + string(rune('A'+i%26)) + string(rune('0'+i%10))
		frames := make([]CallFrame, 10)
		for j := range frames {
			frames[j] = CallFrame{
				FieldValues: createSharedFVHighDup(),
				Stack:       createSharedStack(),
			}
		}
		highDuplicationTestResult.CallerResults[callerName] = frames
	}

	// No duplication test case - large structure with no duplicates
	noDuplicationTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "github.com/example/project/test.TestUnique",
			FunctionName:  "TestUnique",
		},
		CallerResults: make(map[string][]CallFrame),
	}
	// Create many unique callers with completely different data
	for i := 0; i < 50; i++ {
		callerName := "uniqueCaller" + strconv.Itoa(i)
		frames := make([]CallFrame, 5)
		for j := range frames {
			frames[j] = CallFrame{
				FieldValues: FieldValues{
					"unique_field_" + strconv.Itoa(i*10+j): &FieldValue{
						Value: "unique_value_" + strconv.Itoa(i*10+j),
						Children: FieldValues{
							"nested_" + strconv.Itoa(j): &FieldValue{Value: "nested_unique_" + strconv.Itoa(i*100+j)},
						},
					},
				},
				Stack: []StackFrame{
					{File: "/unique/path/" + strconv.Itoa(i) + "/file.go", Line: uint32(i*100 + j), Function: "uniqueFunc" + strconv.Itoa(i*10+j)},
				},
			}
		}
		noDuplicationTestResult.CallerResults[callerName] = frames
	}

	// Medium duplication test case
	mediumDuplicationTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "github.com/example/project/test.TestMedium",
			FunctionName:  "TestMedium",
		},
		CallerResults: make(map[string][]CallFrame),
	}
	// Create some duplicated and some unique data
	sharedFields := []FieldValues{
		{"type1": &FieldValue{Value: "shared_type1_value"}},
		{"type2": &FieldValue{Value: "shared_type2_value"}},
		{"type3": &FieldValue{Value: "shared_type3_value"}},
	}
	sharedStacks := [][]StackFrame{
		{{File: "/shared/stack1.go", Line: 100, Function: "sharedFunc1"}},
		{{File: "/shared/stack2.go", Line: 200, Function: "sharedFunc2"}},
	}
	for i := 0; i < 30; i++ {
		callerName := "mediumCaller" + strconv.Itoa(i)
		frames := make([]CallFrame, 8)
		for j := range frames {
			// Mix of shared and unique data
			var fv FieldValues
			var stack []StackFrame
			if j%3 == 0 { // Use shared data
				fv = sharedFields[j%len(sharedFields)]
				stack = sharedStacks[j%len(sharedStacks)]
			} else { // Use unique data
				fv = FieldValues{
					"unique_" + strconv.Itoa(i*10+j): &FieldValue{Value: "unique_value_" + strconv.Itoa(i*10+j)},
				}
				stack = []StackFrame{
					{File: "/unique/" + strconv.Itoa(i) + ".go", Line: uint32(i*10 + j), Function: "uniqueFunc" + strconv.Itoa(i*10+j)},
				}
			}
			frames[j] = CallFrame{
				FieldValues: fv,
				Stack:       stack,
			}
		}
		mediumDuplicationTestResult.CallerResults[callerName] = frames
	}

	// Low duplication test case
	lowDuplicationTestResult := &TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "github.com/example/project/test.TestLow",
			FunctionName:  "TestLow",
		},
		CallerResults: make(map[string][]CallFrame),
	}
	for i := 0; i < 30; i++ {
		callerName := "lowCaller" + strconv.Itoa(i)
		frames := make([]CallFrame, 8)
		for j := range frames {
			// Mix of shared and unique data
			var fv FieldValues
			var stack []StackFrame
			if j == 10 || j == 20 { // Use shared data
				fv = sharedFields[0]
				stack = sharedStacks[0]
			} else { // Use unique data
				fv = FieldValues{
					"unique_" + strconv.Itoa(i*10+j): &FieldValue{Value: "unique_value_" + strconv.Itoa(i*10+j)},
				}
				stack = []StackFrame{
					{File: "/unique/" + strconv.Itoa(i) + ".go", Line: uint32(i*10 + j), Function: "uniqueFunc" + strconv.Itoa(i*10+j)},
				}
			}
			frames[j] = CallFrame{
				FieldValues: fv,
				Stack:       stack,
			}
		}
		lowDuplicationTestResult.CallerResults[callerName] = frames
	}

	// =================== TEST CASES ===================

	t.Run("basic", func(t *testing.T) {
		t.Parallel()

		data, err := basicTestResult.MarshalMsgpack()
		require.NoError(t, err)
		require.NotEmpty(t, data)

		var decoded TestResult
		err = msgpack.Unmarshal(data, &decoded)
		require.NoError(t, err)

		assert.Equal(t, *basicTestResult, decoded)
	})

	t.Run("deduplicated_field_values", func(t *testing.T) {
		t.Parallel()

		data, err := sharedRefTestResult.MarshalMsgpack()
		require.NoError(t, err)

		// Decode to verify structure
		var encResult encTestResult
		err = msgpack.Unmarshal(data, &encResult)
		require.NoError(t, err)

		// Should have dictionary for shared FieldValues
		assert.NotEmpty(t, encResult.FVDict, "Should have FVDict for duplicate FieldValues")
		assert.Len(t, encResult.FVDict, 1, "Should have exactly one entry in FVDict")

		// All CallFrames should reference the dictionary
		for _, frames := range encResult.CallerResults {
			for _, frame := range frames {
				assert.NotNil(t, frame.FVi, "Should reference FVDict")
				assert.Nil(t, frame.FV, "Should not have inline FV when using dictionary")
			}
		}
	})

	t.Run("edge_cases", func(t *testing.T) {
		t.Parallel()

		data, err := edgeCasesTestResult.MarshalMsgpack()
		require.NoError(t, err)
		require.NotEmpty(t, data)

		var decoded TestResult
		err = msgpack.Unmarshal(data, &decoded)
		require.NoError(t, err)
		assert.Equal(t, *edgeCasesTestResult, decoded)
	})

	t.Run("logical_deduplication", func(t *testing.T) {
		t.Parallel()

		data, err := logicalDeduplicationTestResult.MarshalMsgpack()
		require.NoError(t, err)

		// Decode to check structure
		var encResult encTestResult
		err = msgpack.Unmarshal(data, &encResult)
		require.NoError(t, err)

		// Should detect the logically identical FieldValues as duplicates
		assert.NotEmpty(t, encResult.FVDict, "Should detect logically identical FieldValues as duplicates")
		assert.Len(t, encResult.FVDict, 1, "Should have exactly one FVDict entry")

		// All frames should reference the dictionary
		for _, frames := range encResult.CallerResults {
			for _, frame := range frames {
				assert.NotNil(t, frame.FVi, "All frames should reference FVDict")
				assert.Nil(t, frame.FV, "Frames should not have inline FV when using dictionary")
			}
		}
	})

	t.Run("nested_structure", func(t *testing.T) {
		t.Parallel()

		data, err := nestedTestResult.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)
		assert.Equal(t, *nestedTestResult, decoded)
	})

	t.Run("complex_nested", func(t *testing.T) {
		t.Parallel()

		data, err := complexNestedTestResult.MarshalMsgpack()
		require.NoError(t, err)
		require.NotEmpty(t, data)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)
		assert.Equal(t, *complexNestedTestResult, decoded)
	})

	t.Run("fv_node_dict", func(t *testing.T) {
		t.Parallel()

		tr := &TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "nodetest", FunctionName: "TestNode"},
			CallerResults: map[string][]CallFrame{
				"caller": {
					{FieldValues: dupNestedFieldValues(), Stack: []StackFrame{{File: "a.go", Line: 1, Function: "f"}}},
					{FieldValues: dupNestedFieldValues(), Stack: []StackFrame{{File: "b.go", Line: 2, Function: "f"}}},
				},
			},
		}

		data, err := tr.MarshalMsgpack()
		require.NoError(t, err)

		var enc encTestResult
		err = msgpack.Unmarshal(data, &enc)
		require.NoError(t, err)

		assert.NotEmpty(t, enc.FVNodeDict)
	})

	t.Run("st_dict", func(t *testing.T) {
		t.Parallel()

		tr := &TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "stacktest", FunctionName: "TestStack"},
			CallerResults: map[string][]CallFrame{
				"caller": {
					{FieldValues: FieldValues{"a": &FieldValue{Value: "1"}}, Stack: dupStack()},
					{FieldValues: FieldValues{"b": &FieldValue{Value: "2"}}, Stack: dupStack()},
				},
			},
		}

		data, err := tr.MarshalMsgpack()
		require.NoError(t, err)

		var enc encTestResult
		err = msgpack.Unmarshal(data, &enc)
		require.NoError(t, err)

		assert.NotEmpty(t, enc.STDict)
	})

	t.Run("large_data_structures", func(t *testing.T) {
		t.Parallel()

		// Test with very large strings and deep nesting
		largeValue := strings.Repeat("x", 10000)
		current := FieldValues{}
		for i := 0; i < 50; i++ {
			key := "level" + strconv.Itoa(i)
			current[key] = &FieldValue{
				Value:    largeValue,
				Children: FieldValues{},
			}
			current = current[key].Children
		}

		tr := &TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "largetest", FunctionName: "TestLarge"},
			CallerResults: map[string][]CallFrame{
				"caller": {{FieldValues: nil}},
			},
		}

		data, err := tr.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)

		assert.Equal(t, *tr, decoded)
	})

	t.Run("concurrent_access", func(t *testing.T) {
		t.Parallel()

		tr := &TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "concurrenttest", FunctionName: "TestConcurrent"},
			CallerResults: map[string][]CallFrame{
				"caller": {
					{FieldValues: FieldValues{"field": &FieldValue{Value: "value"}}},
				},
			},
		}

		// Test concurrent marshaling
		const numGoroutines = 100
		results := make(chan []byte, numGoroutines)
		errors := make(chan error, numGoroutines)

		for i := 0; i < numGoroutines; i++ {
			go func() {
				data, err := tr.MarshalMsgpack()
				if err != nil {
					errors <- err
					return
				}
				results <- data
			}()
		}

		// Collect results
		var allData [][]byte
		for i := 0; i < numGoroutines; i++ {
			select {
			case data := <-results:
				allData = append(allData, data)
			case err := <-errors:
				t.Fatal("Concurrent marshaling failed:", err)
			}
		}

		// All results should be identical
		for i := 1; i < len(allData); i++ {
			assert.Equal(t, allData[0], allData[i], "Concurrent marshaling should produce identical results")
		}
	})

	t.Run("corrupted_data", func(t *testing.T) {
		t.Parallel()

		// Test handling of corrupted msgpack data
		corruptedData := []byte{0xFF, 0xFF, 0xFF, 0xFF}
		var tr TestResult
		err := tr.UnmarshalMsgpack(corruptedData)
		assert.Error(t, err, "Should handle corrupted data gracefully")
	})

	t.Run("small_value_optimization", func(t *testing.T) {
		t.Parallel()

		// Test that small values without children don't get dictionary optimization
		tr := &TestResult{
			TestFunction: MinimumTestFunction{FunctionIdent: "smalltest", FunctionName: "TestSmall"},
			CallerResults: map[string][]CallFrame{
				"caller1": {
					{FieldValues: FieldValues{"a": &FieldValue{Value: "x"}}},
					{FieldValues: FieldValues{"a": &FieldValue{Value: "x"}}},
					{FieldValues: FieldValues{"a": &FieldValue{Value: "x"}}},
				},
			},
		}

		data, err := tr.MarshalMsgpack()
		require.NoError(t, err)

		var enc encTestResult
		err = msgpack.Unmarshal(data, &enc)
		require.NoError(t, err)

		// Small values should not be in node dictionary
		assert.Empty(t, enc.FVNodeDict, "Small values without children should not be dictionary-optimized")

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)
		assert.Equal(t, *tr, decoded)
	})

	t.Run("efficiency", func(t *testing.T) {
		t.Parallel()

		// Test cases for efficiency analysis
		testCases := []struct {
			name          string
			testResult    *TestResult
			expectedRatio float64 // minimum expected compression ratio
		}{
			{
				name:          "HighDuplication",
				testResult:    highDuplicationTestResult,
				expectedRatio: 23.04,
			},
			{
				name:          "MediumDuplication",
				testResult:    mediumDuplicationTestResult,
				expectedRatio: 1.41,
			},
			{
				name:          "LowDuplication",
				testResult:    lowDuplicationTestResult,
				expectedRatio: 0.99, // allow minimal overhead in worst case
			},
			{
				name:          "NoDuplication",
				testResult:    noDuplicationTestResult,
				expectedRatio: 1.0,
			},
			{
				name:          "Basic",
				testResult:    basicTestResult,
				expectedRatio: 1.0,
			},
			{
				name:          "LogicalDeduplication",
				testResult:    logicalDeduplicationTestResult,
				expectedRatio: 1.29,
			},
		}

		for _, tc := range testCases {
			t.Run(tc.name, func(t *testing.T) {
				optimizedData, err := tc.testResult.MarshalMsgpack()
				require.NoError(t, err)

				// Debug the encoded structure
				var encResult encTestResult
				err = msgpack.Unmarshal(optimizedData, &encResult)
				require.NoError(t, err)

				// Create baseline without deduplication
				regularData, err := encodeBaseline(tc.testResult)
				require.NoError(t, err)

				optimizationRatio := float64(len(regularData)) / float64(len(optimizedData))

				t.Logf("%s: Regular=%d bytes, Optimized=%d bytes, Ratio=%.2fx, Dicts(FV=%d,Node=%d,Stack=%d)",
					tc.name, len(regularData), len(optimizedData), optimizationRatio,
					len(encResult.FVDict), len(encResult.FVNodeDict), len(encResult.STDict))

				assert.GreaterOrEqual(t, optimizationRatio, tc.expectedRatio,
					"Should achieve at least %.1fx compression for %s", tc.expectedRatio, tc.name)
				// Allow some variance in compression ratio (±0.02x) for stability
				assert.LessOrEqual(t, optimizationRatio, tc.expectedRatio+0.02,
					"Compression ratio significantly higher than expected for %s (%.2fx vs %.2fx)", tc.name, optimizationRatio, tc.expectedRatio)

				var decoded TestResult
				err = decoded.UnmarshalMsgpack(optimizedData)
				require.NoError(t, err)
				assert.Equal(t, *tc.testResult, decoded)
			})
		}
	})
}

func TestFieldValues(t *testing.T) {
	t.Run("flatten_field_values", func(t *testing.T) {
		t.Parallel()

		v1 := "value1"
		v2 := "value2"

		// nested structure with a leaf, a nested child, and an empty fallback
		fv := FieldValues{
			"a": &FieldValue{Value: v1},
			"b": &FieldValue{Children: FieldValues{
				"c": &FieldValue{Value: v2},
			}},
			"empty": &FieldValue{},
		}

		flat := fv.FlattenFieldValues()

		expected := map[string]string{
			"a":     "value1",
			"b.c":   "value2",
			"empty": "",
		}

		assert.Equal(t, expected, flat)
	})

	t.Run("id", func(t *testing.T) {
		t.Parallel()

		v1 := "1"
		v2 := "2"

		// same entries in different order, same ID
		fv1 := FieldValues{
			"x": &FieldValue{Value: v1},
			"y": &FieldValue{Value: v2},
		}
		fv2 := FieldValues{
			"y": &FieldValue{Value: v2},
			"x": &FieldValue{Value: v1},
		}

		id1 := fv1.ID()
		id2 := fv2.ID()
		assert.Equal(t, id1, id2)

		// different values, different ID
		fv3 := FieldValues{
			"x": &FieldValue{Value: v1},
			"y": &FieldValue{Value: v1},
		}
		id3 := fv3.ID()
		assert.NotEqual(t, id1, id3)
	})
}

func TestTestResultMsgpackUnmarshallErrors(t *testing.T) {
	t.Run("invalid_indicies_fv_dict", func(t *testing.T) {
		t.Parallel()

		var idx int
		enc := encTestResult{
			TestFunction:  MinimumTestFunction{FunctionIdent: "f", FunctionName: "F"},
			CallerResults: map[string][]encCallFrame{"c": {{FVi: &idx}}},
			FVDict:        []encFieldValues{},
		}
		data, err := msgpack.Marshal(&enc)
		require.NoError(t, err)
		var tr TestResult
		err = tr.UnmarshalMsgpack(data)
		require.Error(t, err)
	})

	t.Run("invalid_indicies_fvnode_dict", func(t *testing.T) {
		t.Parallel()

		var idx int
		enc := encTestResult{
			TestFunction:  MinimumTestFunction{FunctionIdent: "f", FunctionName: "F"},
			CallerResults: map[string][]encCallFrame{"c": {{FV: encFieldValues{"a": {Ni: &idx}}}}},
			FVNodeDict:    []encFieldValue{},
		}
		data, err := msgpack.Marshal(&enc)
		require.NoError(t, err)
		var tr TestResult
		err = tr.UnmarshalMsgpack(data)
		require.Error(t, err)
	})

	t.Run("invalid_indicies_stdict", func(t *testing.T) {
		t.Parallel()

		var idx int
		enc := encTestResult{
			TestFunction:  MinimumTestFunction{FunctionIdent: "f", FunctionName: "F"},
			CallerResults: map[string][]encCallFrame{"c": {{Si: &idx}}},
			STDict:        [][]StackFrame{},
		}
		data, err := msgpack.Marshal(&enc)
		require.NoError(t, err)
		var tr TestResult
		err = tr.UnmarshalMsgpack(data)
		require.Error(t, err)
	})
}

func TestCallFrameTimeMillis(t *testing.T) {
	t.Run("time_millis_serialization", func(t *testing.T) {
		t.Parallel()

		// Test CallFrame with TimeMillis
		originalFrame := CallFrame{
			FieldValues: FieldValues{
				"field1": &FieldValue{Value: "value1"},
			},
			Stack: []StackFrame{
				{File: "test.go", Line: 100, Function: "testFunc"},
			},
			TimeMillis: 1500, // 1.5 seconds
		}

		testResult := &TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: "test.func",
				FunctionName:  "TestFunc",
			},
			CallerResults: map[string][]CallFrame{
				"caller1": {originalFrame},
			},
		}

		// Marshal and unmarshal
		data, err := testResult.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)

		// Verify TimeMillis is preserved
		assert.Equal(t, originalFrame.TimeMillis, decoded.CallerResults["caller1"][0].TimeMillis)
		assert.Equal(t, uint32(1500), decoded.CallerResults["caller1"][0].TimeMillis)
	})

	t.Run("time_millis_zero_value", func(t *testing.T) {
		t.Parallel()

		// Test with zero TimeMillis
		originalFrame := CallFrame{
			FieldValues: FieldValues{
				"field1": &FieldValue{Value: "value1"},
			},
			Stack: []StackFrame{
				{File: "test.go", Line: 100, Function: "testFunc"},
			},
			TimeMillis: 0, // zero value
		}

		testResult := &TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: "test.func",
				FunctionName:  "TestFunc",
			},
			CallerResults: map[string][]CallFrame{
				"caller1": {originalFrame},
			},
		}

		// Marshal and unmarshal
		data, err := testResult.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)

		// Verify TimeMillis is preserved even when zero
		assert.Equal(t, originalFrame.TimeMillis, decoded.CallerResults["caller1"][0].TimeMillis)
		assert.Equal(t, uint32(0), decoded.CallerResults["caller1"][0].TimeMillis)
	})

	t.Run("time_millis_multiple_frames", func(t *testing.T) {
		t.Parallel()

		// Test with multiple frames with different TimeMillis values
		frames := []CallFrame{
			{
				FieldValues: FieldValues{"field1": &FieldValue{Value: "value1"}},
				Stack:       []StackFrame{{File: "test.go", Line: 100, Function: "testFunc"}},
				TimeMillis:  100,
			},
			{
				FieldValues: FieldValues{"field2": &FieldValue{Value: "value2"}},
				Stack:       []StackFrame{{File: "test.go", Line: 200, Function: "testFunc2"}},
				TimeMillis:  250,
			},
			{
				FieldValues: FieldValues{"field3": &FieldValue{Value: "value3"}},
				Stack:       []StackFrame{{File: "test.go", Line: 300, Function: "testFunc3"}},
				TimeMillis:  500,
			},
		}

		testResult := &TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: "test.func",
				FunctionName:  "TestFunc",
			},
			CallerResults: map[string][]CallFrame{
				"caller1": frames,
			},
		}

		// Marshal and unmarshal
		data, err := testResult.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)

		// Verify all TimeMillis values are preserved
		decodedFrames := decoded.CallerResults["caller1"]
		require.Len(t, decodedFrames, 3)

		for i, frame := range frames {
			assert.Equal(t, frame.TimeMillis, decodedFrames[i].TimeMillis,
				"TimeMillis should match for frame %d", i)
		}
	})

	t.Run("time_millis_with_duplicates", func(t *testing.T) {
		t.Parallel()

		// Test TimeMillis preservation with duplicate FieldValues (dictionary optimization)
		sharedFV := FieldValues{
			"shared": &FieldValue{Value: "sharedValue"},
		}
		sharedStack := []StackFrame{
			{File: "shared.go", Line: 100, Function: "sharedFunc"},
		}

		frames := []CallFrame{
			{
				FieldValues: sharedFV,
				Stack:       sharedStack,
				TimeMillis:  100,
			},
			{
				FieldValues: sharedFV,
				Stack:       sharedStack,
				TimeMillis:  200, // Different time even with same field values
			},
			{
				FieldValues: sharedFV,
				Stack:       sharedStack,
				TimeMillis:  300,
			},
		}

		testResult := &TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: "test.func",
				FunctionName:  "TestFunc",
			},
			CallerResults: map[string][]CallFrame{
				"caller1": frames,
			},
		}

		// Marshal and unmarshal
		data, err := testResult.MarshalMsgpack()
		require.NoError(t, err)

		var decoded TestResult
		err = decoded.UnmarshalMsgpack(data)
		require.NoError(t, err)

		// Verify TimeMillis values are preserved even with duplicate optimization
		decodedFrames := decoded.CallerResults["caller1"]
		require.Len(t, decodedFrames, 3)

		assert.Equal(t, uint32(100), decodedFrames[0].TimeMillis)
		assert.Equal(t, uint32(200), decodedFrames[1].TimeMillis)
		assert.Equal(t, uint32(300), decodedFrames[2].TimeMillis)
	})
}

func TestTestResult_ExtensionData_Serialization(t *testing.T) {
	// Create a test result with extension data
	original := TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.Example",
			FunctionName:  "Example",
		},
		ExtensionData: map[string][]byte{
			"security:capabilities": []byte(`{"network":true,"filesystem":false}`),
			"custom:metrics":        []byte(`{"count":42}`),
		},
	}

	// Serialize
	data, err := original.MarshalMsgpack()
	require.NoError(t, err)
	require.NotEmpty(t, data)

	// Deserialize
	var decoded TestResult
	err = decoded.UnmarshalMsgpack(data)
	require.NoError(t, err)

	// Verify extension data preserved
	assert.Equal(t, original.ExtensionData, decoded.ExtensionData)
	assert.Equal(t, string(original.ExtensionData["security:capabilities"]),
		string(decoded.ExtensionData["security:capabilities"]))
	assert.Equal(t, string(original.ExtensionData["custom:metrics"]),
		string(decoded.ExtensionData["custom:metrics"]))
}

func TestTestResult_ExtensionData_Empty(t *testing.T) {
	// Test with no extension data
	original := TestResult{
		TestFunction: MinimumTestFunction{
			FunctionIdent: "test.Example",
			FunctionName:  "Example",
		},
	}

	data, err := original.MarshalMsgpack()
	require.NoError(t, err)

	var decoded TestResult
	err = decoded.UnmarshalMsgpack(data)
	require.NoError(t, err)

	// Should be nil or empty
	assert.Empty(t, decoded.ExtensionData)
}
