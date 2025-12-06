package lens

import (
	"bytes"
	"fmt"
	"math"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestStreamField tests the streamField function which is the core field serialization.
func TestStreamField(t *testing.T) {
	t.Parallel()

	t.Run("primitives", func(t *testing.T) {
		tests := []struct {
			name     string
			val      interface{}
			wantType string
		}{
			{"bool", true, "bool"},
			{"int", int64(42), "int64"},
			{"float", 3.14, "float64"},
			{"string", "hello", "string"},
		}
		for _, tt := range tests {
			t.Run(tt.name, func(t *testing.T) {
				var buf bytes.Buffer
				lw := &lensMsgEncoder{w: &buf}
				lw.streamField(tt.name, reflect.ValueOf(tt.val), 0, nil, "")
				decoded := LensMonitorField{}
				err := newLensReader(&buf, 1024).readField(&decoded)
				require.NoError(t, err)
				assert.Equal(t, tt.name, decoded.Name)
				assert.Equal(t, tt.wantType, decoded.Type)
				assert.Equal(t, tt.val, decoded.Value)
			})
		}
	})

	t.Run("nested_struct", func(t *testing.T) {
		type inner struct {
			X int
		}
		type outer struct {
			A string
			I inner
		}
		val := outer{A: "a", I: inner{X: 7}}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("root", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		require.Len(t, decoded.Children, 2)
		childA := decoded.Children[0]
		childI := decoded.Children[1]
		assert.Equal(t, "A", childA.Name)
		assert.Equal(t, "string", childA.Type)
		assert.Equal(t, "a", childA.Value)
		assert.Equal(t, "I", childI.Name)
		require.Len(t, childI.Children, 1)
		assert.Equal(t, "X", childI.Children[0].Name)
		assert.Equal(t, "int", childI.Children[0].Type)
		assert.Equal(t, int64(7), childI.Children[0].Value)
	})

	t.Run("slice", func(t *testing.T) {
		val := []int{1, 2, 3}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("slice", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]int", decoded.Type)
		assert.Equal(t, []int64{1, 2, 3}, decoded.Value)
	})

	t.Run("map", func(t *testing.T) {
		val := map[string]int{"a": 1, "b": 2}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("map", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "map[string]int", decoded.Type)
		require.Len(t, decoded.Children, 2)
		names := []string{decoded.Children[0].Name, decoded.Children[1].Name}
		assert.ElementsMatch(t, []string{"a", "b"}, names)
	})

	t.Run("cycle", func(t *testing.T) {
		type node struct {
			Next *node
		}
		n := &node{}
		n.Next = n
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("n", reflect.ValueOf(n), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		require.Len(t, decoded.Children, 1)
		next := decoded.Children[0]
		assert.Equal(t, "Next", next.Name)
		// Should detect cycle
		assert.Contains(t, next.Value.(string), "<cycle:")
	})

	t.Run("long_string", func(t *testing.T) {
		long := strings.Repeat("x", lensMonitorFieldMaxLen+10)
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("long", reflect.ValueOf(long), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 4096).readField(&decoded)
		require.NoError(t, err)
		s := decoded.Value.(string)
		assert.True(t, strings.HasPrefix(s, strings.Repeat("x", lensMonitorFieldMaxLen)))
		assert.True(t, strings.HasSuffix(s, "more)"))
	})

	t.Run("float_nan", func(t *testing.T) {
		val := math.NaN()
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("nan", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "float64", decoded.Type)
		assert.True(t, math.IsNaN(decoded.Value.(float64)))
	})

	t.Run("float_positive_inf", func(t *testing.T) {
		val := math.Inf(1)
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("inf", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "float64", decoded.Type)
		assert.True(t, math.IsInf(decoded.Value.(float64), 1))
	})

	t.Run("float_negative_inf", func(t *testing.T) {
		val := math.Inf(-1)
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("neginf", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "float64", decoded.Type)
		assert.True(t, math.IsInf(decoded.Value.(float64), -1))
	})

	t.Run("float32_nan", func(t *testing.T) {
		val := float32(math.NaN())
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("nan32", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "float32", decoded.Type)
		assert.True(t, math.IsNaN(float64(decoded.Value.(float32))))
	})

	t.Run("float_slice_with_special_values", func(t *testing.T) {
		val := []float64{1.5, math.NaN(), math.Inf(1), 2.5, math.Inf(-1), 3.14}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("floats", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]float64", decoded.Type)

		slice := decoded.Value.([]float64)
		assert.Len(t, slice, 6)
		assert.InDelta(t, 1.5, slice[0], 0.001)
		assert.True(t, math.IsNaN(slice[1]))
		assert.True(t, math.IsInf(slice[2], 1))
		assert.InDelta(t, 2.5, slice[3], 0.001)
		assert.True(t, math.IsInf(slice[4], -1))
		assert.InDelta(t, 3.14, slice[5], 0.001)
	})

	t.Run("float32_slice_with_special_values", func(t *testing.T) {
		val := []float32{1.5, float32(math.NaN()), float32(math.Inf(1)), 2.5}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("floats32", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]float32", decoded.Type)

		slice := decoded.Value.([]float32)
		assert.Len(t, slice, 4)
		assert.InDelta(t, 1.5, float64(slice[0]), 0.001)
		assert.True(t, math.IsNaN(float64(slice[1])))
		assert.True(t, math.IsInf(float64(slice[2]), 1))
		assert.InDelta(t, 2.5, float64(slice[3]), 0.001)
	})

	t.Run("normal_float_unchanged", func(t *testing.T) {
		const val = 3.14159
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("pi", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "float64", decoded.Type)
		assert.InDelta(t, 3.14159, decoded.Value, 0.00001)
	})

	t.Run("bool_slice_empty", func(t *testing.T) {
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf([]bool{}), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, []bool{}, decoded.Value)
	})

	t.Run("bool_slice_single", func(t *testing.T) {
		input := []bool{true}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf(input), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, input, decoded.Value)
	})

	t.Run("bool_slice_byte_boundary", func(t *testing.T) {
		// Test exactly 8 bools (one full byte)
		input := []bool{true, false, true, false, true, false, true, false}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf(input), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, input, decoded.Value)
	})

	t.Run("bool_slice_partial_byte", func(t *testing.T) {
		// Test 11 bools (1 full byte + 3 bits)
		input := []bool{true, true, false, false, true, true, false, false, true, false, true}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf(input), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, input, decoded.Value)
	})

	t.Run("bool_slice_all_true", func(t *testing.T) {
		input := []bool{true, true, true, true, true, true, true, true, true, true}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf(input), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, input, decoded.Value)
	})

	t.Run("bool_slice_all_false", func(t *testing.T) {
		input := []bool{false, false, false, false, false, false, false, false, false, false}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("bools", reflect.ValueOf(input), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, input, decoded.Value)
	})

	t.Run("byte_slice_non_utf8", func(t *testing.T) {
		// Binary data that is not valid UTF-8
		val := []byte{0x00, 0xff, 0x80, 0x90, 0xfe}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("binary", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]uint8", decoded.Type)
		assert.Equal(t, val, decoded.Value)
	})

	t.Run("byte_array_non_utf8", func(t *testing.T) {
		// Binary array that is not valid UTF-8
		val := [5]byte{0x00, 0xff, 0x80, 0x90, 0xfe}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("binary_arr", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[5]uint8", decoded.Type)
		expected := []byte{0x00, 0xff, 0x80, 0x90, 0xfe}
		assert.Equal(t, expected, decoded.Value)
	})

	t.Run("uint64_slice", func(t *testing.T) {
		val := []uint64{1, 2, math.MaxUint64}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("u64slice", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]uint64", decoded.Type)
		assert.Equal(t, []uint64{1, 2, math.MaxUint64}, decoded.Value)
	})

	t.Run("uint32_slice", func(t *testing.T) {
		val := []uint32{1, 2, math.MaxUint32}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("u32slice", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]uint32", decoded.Type)
		assert.Equal(t, []uint32{1, 2, math.MaxUint32}, decoded.Value)
	})

	t.Run("uint_slice_normalized_to_uint64", func(t *testing.T) {
		// []uint should be normalized to []uint64
		val := []uint{1, 2, 100}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("uintslice", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]uint", decoded.Type)
		// uint slices are normalized to []uint64
		assert.Equal(t, []uint64{1, 2, 100}, decoded.Value)
	})

	t.Run("uint16_slice_normalized_to_uint32", func(t *testing.T) {
		val := []uint16{1, 2, math.MaxUint16}
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("u16slice", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "[]uint16", decoded.Type)
		// uint16 slices are normalized to []uint32
		assert.Equal(t, []uint32{1, 2, math.MaxUint16}, decoded.Value)
	})

	t.Run("map_exceeds_limit_string_keys", func(t *testing.T) {
		// Create a map with more entries than lensMonitorFieldMaxLen
		size := lensMonitorFieldMaxLen + 500
		val := make(map[string]int, size)
		for i := 0; i < size; i++ {
			val[fmt.Sprintf("key%05d", i)] = i
		}

		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("largemap", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, lensMonitorFieldMaxLen).readField(&decoded)
		require.NoError(t, err)

		// Should be limited to lensMonitorFieldMaxLen entries
		require.Len(t, decoded.Children, lensMonitorFieldMaxLen)

		// Keys should be sorted (first key should be "key00000")
		assert.Equal(t, "key00000", decoded.Children[0].Name)
		assert.Equal(t, "key00001", decoded.Children[1].Name)
		// Last key in sorted order up to limit
		assert.Equal(t, fmt.Sprintf("key%05d", lensMonitorFieldMaxLen-1), decoded.Children[lensMonitorFieldMaxLen-1].Name)
	})

	t.Run("map_exceeds_limit_int_keys", func(t *testing.T) {
		size := lensMonitorFieldMaxLen + 200
		val := make(map[int]string, size)
		for i := 0; i < size; i++ {
			val[i] = fmt.Sprintf("value%d", i)
		}

		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		lw.streamField("intmap", reflect.ValueOf(val), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, lensMonitorFieldMaxLen).readField(&decoded)
		require.NoError(t, err)

		require.Len(t, decoded.Children, lensMonitorFieldMaxLen)

		// Keys should be sorted numerically (0, 1, 2, ...)
		assert.Equal(t, "0", decoded.Children[0].Name)
		assert.Equal(t, "1", decoded.Children[1].Name)
		assert.Equal(t, strconv.Itoa(lensMonitorFieldMaxLen-1), decoded.Children[lensMonitorFieldMaxLen-1].Name)
	})

	t.Run("map_deterministic_on_repeat", func(t *testing.T) {
		// Verify encoding is deterministic for large maps
		size := lensMonitorFieldMaxLen + 100
		val := make(map[int]int, size)
		for i := 0; i < size; i++ {
			val[i] = i * 2
		}

		// Encode twice
		var buf1, buf2 bytes.Buffer
		lw1 := &lensMsgEncoder{w: &buf1}
		lw1.streamField("map", reflect.ValueOf(val), 0, nil, "")
		lw2 := &lensMsgEncoder{w: &buf2}
		lw2.streamField("map", reflect.ValueOf(val), 0, nil, "")

		// Should produce identical output
		assert.Equal(t, buf1.Bytes(), buf2.Bytes())
	})
}

func TestLensCompareReflectValue(t *testing.T) {
	t.Parallel()

	t.Run("string_comparison", func(t *testing.T) {
		a := reflect.ValueOf("apple")
		b := reflect.ValueOf("banana")
		c := reflect.ValueOf("apple")

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
		assert.Equal(t, 0, lensCompareReflectValue(a, c))
	})

	t.Run("int_comparison", func(t *testing.T) {
		a := reflect.ValueOf(10)
		b := reflect.ValueOf(20)
		c := reflect.ValueOf(10)

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
		assert.Equal(t, 0, lensCompareReflectValue(a, c))
	})

	t.Run("uint_comparison", func(t *testing.T) {
		a := reflect.ValueOf(uint(5))
		b := reflect.ValueOf(uint(15))

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
	})

	t.Run("float_comparison", func(t *testing.T) {
		a := reflect.ValueOf(1.5)
		b := reflect.ValueOf(2.5)

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
	})

	t.Run("bool_comparison", func(t *testing.T) {
		f := reflect.ValueOf(false)
		tr := reflect.ValueOf(true)

		assert.Equal(t, -1, lensCompareReflectValue(f, tr))
		assert.Equal(t, 1, lensCompareReflectValue(tr, f))
		assert.Equal(t, 0, lensCompareReflectValue(f, f))
		assert.Equal(t, 0, lensCompareReflectValue(tr, tr))
	})

	t.Run("complex_comparison", func(t *testing.T) {
		a := reflect.ValueOf(complex(1, 2))
		b := reflect.ValueOf(complex(1, 3))
		c := reflect.ValueOf(complex(2, 1))

		assert.Equal(t, -1, lensCompareReflectValue(a, b)) // same real, smaller imag
		assert.Equal(t, -1, lensCompareReflectValue(a, c)) // smaller real
		assert.Equal(t, 0, lensCompareReflectValue(a, a))
	})

	t.Run("pointer_comparison", func(t *testing.T) {
		x, y := 1, 2
		a := reflect.ValueOf(&x)
		b := reflect.ValueOf(&y)

		// Pointers compared by address, result depends on allocation order
		result := lensCompareReflectValue(a, b)
		assert.NotEqual(t, 0, result)
		assert.Equal(t, 0, lensCompareReflectValue(a, a))
	})

	t.Run("array_comparison", func(t *testing.T) {
		a := reflect.ValueOf([3]int{1, 2, 3})
		b := reflect.ValueOf([3]int{1, 2, 4})
		c := reflect.ValueOf([3]int{1, 2, 3})

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
		assert.Equal(t, 0, lensCompareReflectValue(a, c))
	})

	t.Run("struct_comparison", func(t *testing.T) {
		type point struct {
			X, Y int
		}
		a := reflect.ValueOf(point{1, 2})
		b := reflect.ValueOf(point{1, 3})
		c := reflect.ValueOf(point{2, 1})
		d := reflect.ValueOf(point{1, 2})

		assert.Equal(t, -1, lensCompareReflectValue(a, b)) // same X, smaller Y
		assert.Equal(t, -1, lensCompareReflectValue(a, c)) // smaller X
		assert.Equal(t, 0, lensCompareReflectValue(a, d))
	})

	t.Run("nested_struct_comparison", func(t *testing.T) {
		type inner struct{ V int }
		type outer struct{ I inner }

		a := reflect.ValueOf(outer{inner{1}})
		b := reflect.ValueOf(outer{inner{2}})

		assert.Equal(t, -1, lensCompareReflectValue(a, b))
		assert.Equal(t, 1, lensCompareReflectValue(b, a))
	})

	t.Run("interface_comparison", func(t *testing.T) {
		var a, b interface{} = 10, 20
		var nilA, nilB interface{}

		assert.Equal(t, -1, lensCompareReflectValue(reflect.ValueOf(&a).Elem(), reflect.ValueOf(&b).Elem()))
		assert.Equal(t, 0, lensCompareReflectValue(reflect.ValueOf(&nilA).Elem(), reflect.ValueOf(&nilB).Elem()))
		assert.Equal(t, -1, lensCompareReflectValue(reflect.ValueOf(&nilA).Elem(), reflect.ValueOf(&a).Elem()))
	})
}

func TestLimitLensMonitorStringSize(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		input    string
		expected string
	}{
		{
			name:     "short_string",
			input:    "hello",
			expected: "hello",
		},
		{
			name:     "empty_string",
			input:    "",
			expected: "",
		},
		{
			name:     "exactly_max_length",
			input:    strings.Repeat("x", lensMonitorFieldMaxLen),
			expected: strings.Repeat("x", lensMonitorFieldMaxLen),
		},
		{
			name:     "over_max_length",
			input:    strings.Repeat("a", lensMonitorFieldMaxLen+15),
			expected: strings.Repeat("a", lensMonitorFieldMaxLen) + "…(15 more)",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := limitLensMonitorStringSize(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}
