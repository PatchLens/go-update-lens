package lens

import (
	"reflect"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestBuildLensMonitorField(t *testing.T) {
	t.Run("primitives", func(t *testing.T) {
		t.Parallel()

		vals := map[string]interface{}{
			"bool":   true,
			"int":    int64(42),
			"float":  3.14,
			"string": "hello",
		}
		for name, val := range vals {
			name := name
			val := val
			t.Run(name, func(t *testing.T) {
				f := LensMonitorField{Name: name}
				buildLensMonitorField("", &f, reflect.ValueOf(val), 0, make(map[uintptr]string))
				assert.Equal(t, name, f.Name)
				assert.Equal(t, reflect.TypeOf(val).String(), f.Type)
				assert.Equal(t, val, f.Value)
			})
		}
	})

	t.Run("nested_struct", func(t *testing.T) {
		t.Parallel()

		type inner struct {
			X int
		}
		type outer struct {
			A string
			I inner
		}
		val := outer{A: "a", I: inner{X: 7}}
		f := LensMonitorField{Name: "root"}
		buildLensMonitorField("", &f, reflect.ValueOf(val), 0, make(map[uintptr]string))
		require.Len(t, f.Children, 2)
		childA := f.Children[0]
		childI := f.Children[1]
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
		t.Parallel()

		val := []int{1, 2, 3}
		f := LensMonitorField{Name: "slice"}
		buildLensMonitorField("", &f, reflect.ValueOf(val), 0, make(map[uintptr]string))
		assert.Equal(t, "[]int", f.Type)
		assert.Equal(t, []interface{}{1, 2, 3}, f.Value)
	})

	t.Run("map", func(t *testing.T) {
		t.Parallel()

		val := map[string]int{"a": 1, "b": 2}
		f := LensMonitorField{Name: "map"}
		buildLensMonitorField("", &f, reflect.ValueOf(val), 0, make(map[uintptr]string))
		assert.Equal(t, "map[string]int", f.Type)
		require.Len(t, f.Children, 2)
		names := []string{f.Children[0].Name, f.Children[1].Name}
		assert.ElementsMatch(t, []string{"a", "b"}, names)
	})

	t.Run("cycle", func(t *testing.T) {
		t.Parallel()

		type node struct {
			Next *node
		}
		n := &node{}
		n.Next = n
		f := LensMonitorField{Name: "n"}
		buildLensMonitorField("", &f, reflect.ValueOf(n), 0, make(map[uintptr]string))
		require.Len(t, f.Children, 1)
		next := f.Children[0]
		assert.Equal(t, "Next", next.Name)
		// recursion should stop after hitting max depth
		var depth int
		child := &next
		for len(child.Children) > 0 && depth <= lensMonitorFieldMaxRecurse {
			depth++
			child = &child.Children[0]
		}
		require.LessOrEqual(t, depth, lensMonitorFieldMaxRecurse)
		if depth == lensMonitorFieldMaxRecurse {
			assert.Equal(t, "<max-depth>", child.Value)
		}
	})

	t.Run("long_string", func(t *testing.T) {
		t.Parallel()

		long := strings.Repeat("x", lensMonitorFieldMaxLen+10)
		f := LensMonitorField{Name: "long"}
		buildLensMonitorField("", &f, reflect.ValueOf(long), 0, make(map[uintptr]string))
		s := f.Value.(string)
		assert.True(t, strings.HasPrefix(s, strings.Repeat("x", lensMonitorFieldMaxLen)))
		assert.True(t, strings.HasSuffix(s, "…(10 more)"))
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
