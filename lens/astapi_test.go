package lens

import (
	"bytes"
	"errors"
	"math"
	"reflect"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// streamFieldToField is a test helper that encodes a value via streamField and decodes it via readField.
func streamFieldToField(t *testing.T, name string, val interface{}) LensMonitorField {
	t.Helper()
	var buf bytes.Buffer
	lw := &lensMsgEncoder{w: &buf}
	lw.streamField(name, reflect.ValueOf(val), 0, nil, "")
	decoded := LensMonitorField{}
	err := newLensReader(&buf, 1024).readField(&decoded)
	require.NoError(t, err)
	return decoded
}

func TestStreamFieldPrimitives(t *testing.T) {
	t.Parallel()

	t.Run("nil", func(t *testing.T) {
		var buf bytes.Buffer
		lw := &lensMsgEncoder{w: &buf}
		var nilPtr *int
		lw.streamField("nilField", reflect.ValueOf(nilPtr), 0, nil, "")
		decoded := LensMonitorField{}
		err := newLensReader(&buf, 1024).readField(&decoded)
		require.NoError(t, err)
		assert.Equal(t, "nilField", decoded.Name)
		assert.Nil(t, decoded.Value)
	})

	t.Run("bool_true", func(t *testing.T) {
		f := streamFieldToField(t, "b", true)
		assert.Equal(t, "b", f.Name)
		assert.Equal(t, "bool", f.Type)
		assert.Equal(t, true, f.Value)
	})

	t.Run("bool_false", func(t *testing.T) {
		f := streamFieldToField(t, "b", false)
		assert.Equal(t, false, f.Value)
	})

	t.Run("int32_positive", func(t *testing.T) {
		f := streamFieldToField(t, "i", int32(42))
		assert.Equal(t, "int32", f.Type)
		assert.Equal(t, int32(42), f.Value)
	})

	t.Run("int32_negative", func(t *testing.T) {
		f := streamFieldToField(t, "i", int32(-12345))
		assert.Equal(t, int32(-12345), f.Value)
	})

	t.Run("int64_positive", func(t *testing.T) {
		f := streamFieldToField(t, "i", int64(42))
		assert.Equal(t, "int64", f.Type)
		assert.Equal(t, int64(42), f.Value)
	})

	t.Run("int64_max", func(t *testing.T) {
		f := streamFieldToField(t, "i", int64(math.MaxInt64))
		assert.Equal(t, int64(math.MaxInt64), f.Value)
	})

	t.Run("int64_min", func(t *testing.T) {
		f := streamFieldToField(t, "i", int64(math.MinInt64))
		assert.Equal(t, int64(math.MinInt64), f.Value)
	})

	t.Run("int_normalized_to_int64", func(t *testing.T) {
		f := streamFieldToField(t, "i", 42)
		assert.Equal(t, "int", f.Type)
		assert.Equal(t, int64(42), f.Value) // int is encoded as int64
	})

	t.Run("uint32_positive", func(t *testing.T) {
		f := streamFieldToField(t, "u", uint32(999))
		assert.Equal(t, "uint32", f.Type)
		assert.Equal(t, uint32(999), f.Value)
	})

	t.Run("uint64_max", func(t *testing.T) {
		f := streamFieldToField(t, "u", uint64(math.MaxUint64))
		assert.Equal(t, "uint64", f.Type)
		assert.Equal(t, uint64(math.MaxUint64), f.Value)
	})

	t.Run("float32_positive", func(t *testing.T) {
		f := streamFieldToField(t, "f", float32(3.14159))
		assert.Equal(t, "float32", f.Type)
		assert.InDelta(t, 3.14159, f.Value.(float32), 0.00001)
	})

	t.Run("float64_normal", func(t *testing.T) {
		f := streamFieldToField(t, "f", 3.14159)
		assert.Equal(t, "float64", f.Type)
		assert.InDelta(t, 3.14159, f.Value.(float64), 0.00001)
	})

	t.Run("float64_nan", func(t *testing.T) {
		f := streamFieldToField(t, "f", math.NaN())
		assert.True(t, math.IsNaN(f.Value.(float64)))
	})

	t.Run("float64_positive_inf", func(t *testing.T) {
		f := streamFieldToField(t, "f", math.Inf(1))
		assert.True(t, math.IsInf(f.Value.(float64), 1))
	})

	t.Run("float64_negative_inf", func(t *testing.T) {
		f := streamFieldToField(t, "f", math.Inf(-1))
		assert.True(t, math.IsInf(f.Value.(float64), -1))
	})

	t.Run("float64_negative_zero", func(t *testing.T) {
		negZero := math.Copysign(0, -1)
		f := streamFieldToField(t, "f", negZero)
		assert.True(t, math.Signbit(f.Value.(float64)))
	})

	t.Run("string_empty", func(t *testing.T) {
		f := streamFieldToField(t, "s", "")
		assert.Equal(t, "string", f.Type)
		assert.Empty(t, f.Value)
	})

	t.Run("string_ascii", func(t *testing.T) {
		f := streamFieldToField(t, "s", "hello world")
		assert.Equal(t, "hello world", f.Value)
	})

	t.Run("string_unicode", func(t *testing.T) {
		unicodeStr := "hello \u4e16\u754c \U0001F30D" // "hello 世界 🌍"
		f := streamFieldToField(t, "s", unicodeStr)
		assert.Equal(t, unicodeStr, f.Value)
	})

	t.Run("complex64", func(t *testing.T) {
		val := complex64(complex(1.5, -2.5))
		f := streamFieldToField(t, "c", val)
		assert.Equal(t, "complex64", f.Type)
		c := f.Value.(complex128) // complex64 is encoded as complex128
		assert.InDelta(t, 1.5, real(c), 0.001)
		assert.InDelta(t, -2.5, imag(c), 0.001)
	})

	t.Run("complex128", func(t *testing.T) {
		val := complex(3.14, 2.71)
		f := streamFieldToField(t, "c", val)
		assert.Equal(t, "complex128", f.Type)
		assert.Equal(t, val, f.Value)
	})

	t.Run("complex_with_special_values", func(t *testing.T) {
		val := complex(math.NaN(), math.Inf(1))
		f := streamFieldToField(t, "c", val)
		c := f.Value.(complex128)
		assert.True(t, math.IsNaN(real(c)))
		assert.True(t, math.IsInf(imag(c), 1))
	})
}

func TestStreamFieldSlices(t *testing.T) {
	t.Parallel()

	t.Run("bytes_empty", func(t *testing.T) {
		f := streamFieldToField(t, "b", []byte{})
		assert.Equal(t, "[]uint8", f.Type)
		// Empty UTF-8 valid byte slice becomes empty string
		assert.Empty(t, f.Value)
	})

	t.Run("bytes_binary", func(t *testing.T) {
		input := []byte{0x00, 0xff, 0x80, 0x90, 0xfe}
		f := streamFieldToField(t, "b", input)
		assert.Equal(t, "[]uint8", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("bytes_valid_utf8", func(t *testing.T) {
		input := []byte("hello")
		f := streamFieldToField(t, "b", input)
		// Valid UTF-8 bytes are stored as string
		assert.Equal(t, "hello", f.Value)
	})

	t.Run("int32_slice", func(t *testing.T) {
		input := []int32{-1, 0, 1, math.MaxInt32, math.MinInt32}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]int32", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("int64_slice", func(t *testing.T) {
		input := []int64{-1, 0, 1, math.MaxInt64, math.MinInt64}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]int64", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("int_slice_normalized", func(t *testing.T) {
		input := []int{1, 2, 3}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]int", f.Type)
		assert.Equal(t, []int64{1, 2, 3}, f.Value) // normalized to int64
	})

	t.Run("uint32_slice", func(t *testing.T) {
		input := []uint32{0, 1, 999, math.MaxUint32}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]uint32", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("uint64_slice", func(t *testing.T) {
		input := []uint64{0, 1, 999, math.MaxUint64}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]uint64", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("float32_slice", func(t *testing.T) {
		input := []float32{-1.5, 0, 1.5, math.MaxFloat32}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]float32", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("float32_slice_special", func(t *testing.T) {
		input := []float32{float32(math.NaN()), float32(math.Inf(1)), float32(math.Inf(-1))}
		f := streamFieldToField(t, "s", input)
		slice := f.Value.([]float32)
		assert.True(t, math.IsNaN(float64(slice[0])))
		assert.True(t, math.IsInf(float64(slice[1]), 1))
		assert.True(t, math.IsInf(float64(slice[2]), -1))
	})

	t.Run("float64_slice", func(t *testing.T) {
		input := []float64{-1.5, 0, 1.5, math.MaxFloat64}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]float64", f.Type)
		assert.Equal(t, input, f.Value)
	})

	t.Run("float64_slice_special", func(t *testing.T) {
		input := []float64{math.NaN(), math.Inf(1), math.Inf(-1)}
		f := streamFieldToField(t, "s", input)
		slice := f.Value.([]float64)
		assert.True(t, math.IsNaN(slice[0]))
		assert.True(t, math.IsInf(slice[1], 1))
		assert.True(t, math.IsInf(slice[2], -1))
	})

	t.Run("bool_slice_empty", func(t *testing.T) {
		f := streamFieldToField(t, "s", []bool{})
		assert.Equal(t, "[]bool", f.Type)
		assert.Equal(t, []bool{}, f.Value)
	})

	t.Run("bool_slice_byte_boundary", func(t *testing.T) {
		// Test exactly 8 bools (one full byte)
		input := []bool{true, false, true, false, true, false, true, false}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, input, f.Value)
	})

	t.Run("bool_slice_partial_byte", func(t *testing.T) {
		// Test 11 bools (1 full byte + 3 bits)
		input := []bool{true, true, false, false, true, true, false, false, true, false, true}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, input, f.Value)
	})

	t.Run("string_slice", func(t *testing.T) {
		input := []string{"hello", "world"}
		f := streamFieldToField(t, "s", input)
		assert.Equal(t, "[]string", f.Type)
		// String slices are encoded inline as []string value
		assert.Equal(t, []string{"hello", "world"}, f.Value)
		assert.Empty(t, f.Children)
	})

	t.Run("struct_slice", func(t *testing.T) {
		type Item struct {
			Name string
			Val  int
		}
		input := []Item{
			{Name: "first", Val: 1},
			{Name: "second", Val: 2},
		}
		f := streamFieldToField(t, "items", input)
		assert.Equal(t, "[]lens.Item", f.Type)
		// Struct slices are encoded as children with index names
		require.Len(t, f.Children, 2)
		assert.Equal(t, "[0]", f.Children[0].Name)
		require.Len(t, f.Children[0].Children, 2)
		assert.Equal(t, "Name", f.Children[0].Children[0].Name)
		assert.Equal(t, "first", f.Children[0].Children[0].Value)
		assert.Equal(t, "Val", f.Children[0].Children[1].Name)
		assert.Equal(t, int64(1), f.Children[0].Children[1].Value)
		assert.Equal(t, "[1]", f.Children[1].Name)
		assert.Equal(t, "second", f.Children[1].Children[0].Value)
		assert.Equal(t, int64(2), f.Children[1].Children[1].Value)
	})

	t.Run("map_slice", func(t *testing.T) {
		input := []map[string]int{
			{"a": 1, "b": 2},
			{"c": 3},
		}
		f := streamFieldToField(t, "maps", input)
		assert.Equal(t, "[]map[string]int", f.Type)
		require.Len(t, f.Children, 2)
		assert.Equal(t, "[0]", f.Children[0].Name)
		require.Len(t, f.Children[0].Children, 2)
		assert.Equal(t, "[1]", f.Children[1].Name)
		require.Len(t, f.Children[1].Children, 1)
	})

	t.Run("interface_slice", func(t *testing.T) {
		type Inner struct{ X int }
		input := []interface{}{
			42,
			"hello",
			Inner{X: 99},
		}
		f := streamFieldToField(t, "mixed", input)
		assert.Equal(t, "[]interface {}", f.Type)
		require.Len(t, f.Children, 3)
		assert.Equal(t, "[0]", f.Children[0].Name)
		assert.Equal(t, int64(42), f.Children[0].Value)
		assert.Equal(t, "[1]", f.Children[1].Name)
		assert.Equal(t, "hello", f.Children[1].Value)
		assert.Equal(t, "[2]", f.Children[2].Name)
		require.Len(t, f.Children[2].Children, 1)
		assert.Equal(t, "X", f.Children[2].Children[0].Name)
		assert.Equal(t, int64(99), f.Children[2].Children[0].Value)
	})

	t.Run("nested_int_slice", func(t *testing.T) {
		input := [][]int{{1, 2}, {3, 4, 5}}
		f := streamFieldToField(t, "nested", input)
		assert.Equal(t, "[][]int", f.Type)
		require.Len(t, f.Children, 2)
		assert.Equal(t, "[0]", f.Children[0].Name)
		assert.Equal(t, []int64{1, 2}, f.Children[0].Value)
		assert.Equal(t, "[1]", f.Children[1].Name)
		assert.Equal(t, []int64{3, 4, 5}, f.Children[1].Value)
	})

	t.Run("pointer_slice", func(t *testing.T) {
		a, b := 10, 20
		input := []*int{&a, nil, &b}
		f := streamFieldToField(t, "ptrs", input)
		assert.Equal(t, "[]*int", f.Type)
		require.Len(t, f.Children, 3)
		assert.Equal(t, "[0]", f.Children[0].Name)
		assert.Equal(t, int64(10), f.Children[0].Value)
		assert.Equal(t, "[1]", f.Children[1].Name)
		assert.Nil(t, f.Children[1].Value)
		assert.Equal(t, "[2]", f.Children[2].Name)
		assert.Equal(t, int64(20), f.Children[2].Value)
	})
}

func TestStreamFieldComposites(t *testing.T) {
	t.Parallel()

	t.Run("struct_simple", func(t *testing.T) {
		type inner struct {
			X int
			Y string
		}
		val := inner{X: 42, Y: "hello"}
		f := streamFieldToField(t, "s", val)
		require.Len(t, f.Children, 2)
		assert.Equal(t, "X", f.Children[0].Name)
		assert.Equal(t, int64(42), f.Children[0].Value)
		assert.Equal(t, "Y", f.Children[1].Name)
		assert.Equal(t, "hello", f.Children[1].Value)
	})

	t.Run("struct_nested", func(t *testing.T) {
		type inner struct {
			X int
		}
		type outer struct {
			A string
			I inner
		}
		val := outer{A: "a", I: inner{X: 7}}
		f := streamFieldToField(t, "root", val)
		require.Len(t, f.Children, 2)
		assert.Equal(t, "A", f.Children[0].Name)
		assert.Equal(t, "a", f.Children[0].Value)
		assert.Equal(t, "I", f.Children[1].Name)
		require.Len(t, f.Children[1].Children, 1)
		assert.Equal(t, "X", f.Children[1].Children[0].Name)
		assert.Equal(t, int64(7), f.Children[1].Children[0].Value)
	})

	t.Run("struct_empty", func(t *testing.T) {
		type empty struct{}
		val := empty{}
		f := streamFieldToField(t, "e", val)
		// Empty struct uses lensTypeTagStruct with 0 children
		assert.Nil(t, f.Value)
		assert.Empty(t, f.Children)
	})

	t.Run("map", func(t *testing.T) {
		val := map[string]int{"a": 1, "b": 2}
		f := streamFieldToField(t, "m", val)
		assert.Equal(t, "map[string]int", f.Type)
		require.Len(t, f.Children, 2)
		names := []string{f.Children[0].Name, f.Children[1].Name}
		assert.ElementsMatch(t, []string{"a", "b"}, names)
	})

	t.Run("pointer_nil", func(t *testing.T) {
		var ptr *int
		f := streamFieldToField(t, "p", ptr)
		assert.Nil(t, f.Value)
	})

	t.Run("pointer_non_nil", func(t *testing.T) {
		val := 42
		f := streamFieldToField(t, "p", &val)
		assert.Equal(t, int64(42), f.Value)
	})

	t.Run("func", func(t *testing.T) {
		fn := func() {}
		f := streamFieldToField(t, "f", fn)
		assert.Equal(t, "<func>", f.Value)
	})

	t.Run("chan", func(t *testing.T) {
		ch := make(chan int)
		f := streamFieldToField(t, "c", ch)
		assert.Equal(t, "<chan>", f.Value)
	})

	t.Run("cycle_detection", func(t *testing.T) {
		type node struct {
			Next *node
		}
		n := &node{}
		n.Next = n
		f := streamFieldToField(t, "n", n)
		require.Len(t, f.Children, 1)
		next := f.Children[0]
		assert.Equal(t, "Next", next.Name)
		// Should detect cycle and not recurse infinitely
		assert.Contains(t, next.Value.(string), "<cycle:")
	})
}

func TestStreamFieldEdgeCases(t *testing.T) {
	t.Parallel()

	t.Run("read_unknown_tag", func(t *testing.T) {
		var buf bytes.Buffer
		buf.WriteByte(99) // unknown tag
		_, _, err := newLensReader(&buf, 1024).readValue()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "unknown value tag")
	})

	t.Run("read_truncated_data", func(t *testing.T) {
		var buf bytes.Buffer
		buf.WriteByte(lensTypeTagInt64) // tag for int64 but no data
		_, _, err := newLensReader(&buf, 1024).readValue()
		require.Error(t, err)
	})
}

func TestLensEncodeDecodeMessagePoint(t *testing.T) {
	t.Parallel()

	t.Run("empty_stack", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePoint(&buf, 42, 1234567890, []LensMonitorStackFrame{})
		decoded, err := newLensReader(&buf, 1024).decodeMessagePoint()
		require.NoError(t, err)
		assert.Equal(t, uint32(42), decoded.PointID)
		assert.Equal(t, int64(1234567890), decoded.TimeNS)
		assert.Empty(t, decoded.Stack)
	})

	t.Run("with_stack_frames", func(t *testing.T) {
		var buf bytes.Buffer
		stack := []LensMonitorStackFrame{
			{File: "main.go", Function: "main.main", Line: 10},
			{File: "handler.go", Function: "pkg.Handle", Line: 25},
		}
		lensEncodeMessagePoint(&buf, 1, 999, stack)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePoint()
		require.NoError(t, err)
		assert.Equal(t, uint32(1), decoded.PointID)
		assert.Equal(t, int64(999), decoded.TimeNS)
		require.Len(t, decoded.Stack, 2)
		assert.Equal(t, "main.go", decoded.Stack[0].File)
		assert.Equal(t, "main.main", decoded.Stack[0].Function)
		assert.Equal(t, uint(10), decoded.Stack[0].Line)
		assert.Equal(t, "handler.go", decoded.Stack[1].File)
		assert.Equal(t, "pkg.Handle", decoded.Stack[1].Function)
		assert.Equal(t, uint(25), decoded.Stack[1].Line)
	})

	t.Run("negative_time", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePoint(&buf, 5, -1000, nil)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePoint()
		require.NoError(t, err)
		assert.Equal(t, int64(-1000), decoded.TimeNS)
	})
}

func TestLensEncodeDecodeMessagePointState(t *testing.T) {
	t.Parallel()

	t.Run("empty_fields", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePointState(&buf, 10, 5000, []LensMonitorStackFrame{}, nil)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointState()
		require.NoError(t, err)
		assert.Equal(t, uint32(10), decoded.PointID)
		assert.Equal(t, int64(5000), decoded.TimeNS)
		assert.Empty(t, decoded.Stack)
		assert.Empty(t, decoded.Fields)
	})

	t.Run("with_fields", func(t *testing.T) {
		var buf bytes.Buffer
		stack := []LensMonitorStackFrame{
			{File: "test.go", Function: "Test", Line: 100},
		}
		snaps := []LensMonitorFieldSnapshot{
			{Name: "x", Val: int64(1)},
			{Name: "y", Val: "hello"},
		}
		lensEncodeMessagePointState(&buf, 20, 6000, stack, snaps)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointState()
		require.NoError(t, err)
		assert.Equal(t, uint32(20), decoded.PointID)
		require.Len(t, decoded.Stack, 1)
		require.Len(t, decoded.Fields, 2)
		assert.Equal(t, "x", decoded.Fields[0].Name)
		assert.Equal(t, int64(1), decoded.Fields[0].Value)
		assert.Equal(t, "y", decoded.Fields[1].Name)
		assert.Equal(t, "hello", decoded.Fields[1].Value)
	})

	t.Run("fields_with_special_floats", func(t *testing.T) {
		var buf bytes.Buffer
		snaps := []LensMonitorFieldSnapshot{
			{Name: "nan", Val: math.NaN()},
			{Name: "inf", Val: math.Inf(1)},
		}
		lensEncodeMessagePointState(&buf, 30, 7000, nil, snaps)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointState()
		require.NoError(t, err)
		require.Len(t, decoded.Fields, 2)
		assert.True(t, math.IsNaN(decoded.Fields[0].Value.(float64)))
		assert.True(t, math.IsInf(decoded.Fields[1].Value.(float64), 1))
	})
}

func TestLensEncodeDecodeMessagePointPanic(t *testing.T) {
	t.Parallel()

	t.Run("simple_message", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePointPanic(&buf, 100, 999999, "panic: something went wrong")
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointPanic()
		require.NoError(t, err)
		assert.Equal(t, uint32(100), decoded.PointID)
		assert.Equal(t, int64(999999), decoded.TimeNS)
		assert.Equal(t, "panic: something went wrong", decoded.Message)
	})

	t.Run("empty_message", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePointPanic(&buf, 200, 0, "")
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointPanic()
		require.NoError(t, err)
		assert.Equal(t, uint32(200), decoded.PointID)
		assert.Empty(t, decoded.Message)
	})

	t.Run("unicode_message", func(t *testing.T) {
		var buf bytes.Buffer
		// Use escape sequences to avoid gosmopolitan lint
		unicodeMsg := "panic: \u9519\u8bef \U0001F525" // "panic: 错误 🔥"
		lensEncodeMessagePointPanic(&buf, 300, 12345, unicodeMsg)
		decoded, err := newLensReader(&buf, 1024).decodeMessagePointPanic()
		require.NoError(t, err)
		assert.Equal(t, unicodeMsg, decoded.Message)
	})
}

func TestLensEncodeDecodeMessageError(t *testing.T) {
	t.Parallel()

	t.Run("simple_error", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessageError(&buf, 50, errors.New("failed to process"), []LensMonitorStackFrame{})
		decoded, err := newLensReader(&buf, 1024).decodeMessageError()
		require.NoError(t, err)
		assert.Equal(t, uint32(50), decoded.PointID)
		assert.Equal(t, "failed to process", decoded.Message)
		assert.Empty(t, decoded.Stack)
	})

	t.Run("with_stack", func(t *testing.T) {
		var buf bytes.Buffer
		stack := []LensMonitorStackFrame{
			{File: "error.go", Function: "handleError", Line: 50},
		}
		lensEncodeMessageError(&buf, 60, errors.New("error occurred"), stack)
		decoded, err := newLensReader(&buf, 1024).decodeMessageError()
		require.NoError(t, err)
		assert.Equal(t, uint32(60), decoded.PointID)
		assert.Equal(t, "error occurred", decoded.Message)
		require.Len(t, decoded.Stack, 1)
		assert.Equal(t, "error.go", decoded.Stack[0].File)
	})
}
