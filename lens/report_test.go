package lens

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestRootModule(t *testing.T) {
	t.Parallel()

	t.Run("single_entry", func(t *testing.T) {
		mods := []*ModuleChange{{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		assert.Equal(t, *mods[0], rootModule(mods))
	})

	t.Run("one_direct_in_multiple", func(t *testing.T) {
		mods := []*ModuleChange{
			{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0", Indirect: true},
			{Name: "modB", PriorVersion: "v0.1.0", NewVersion: "v0.2.0", Indirect: false},
			{Name: "modC", PriorVersion: "v0.9.0", NewVersion: "v1.0.0", Indirect: true},
		}
		assert.Equal(t, *mods[1], rootModule(mods))
	})

	t.Run("multiple_direct_modules", func(t *testing.T) {
		mods := []*ModuleChange{
			{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0", Indirect: false},
			{Name: "modB", PriorVersion: "v0.1.0", NewVersion: "v0.2.0", Indirect: false},
		}
		assert.Equal(t, ModuleChange{}, rootModule(mods))
	})
}

func TestCompareRiskyTests(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name string
		a    []string
		b    []string
		want int // expected result of compareRiskyTests(a, b)
	}{
		{
			name: "generated_tests_sort_last",
			a:    []string{"TestFoo", testPassStr, "0", ""},
			b:    []string{GeneratedTestFunctionPrefix + "Foo", testFailStr, "9", "pkg:F[a|b]"},
			want: -1,
		},
		{
			name: "regressions_sort_first",
			a:    []string{"TestA", testFailStr, "0", ""},
			b:    []string{"TestB", testPassStr, "9", ""},
			want: -1,
		},
		{
			name: "baseline_fail_not_regression",
			a:    []string{"TestA", "Baseline FAIL", "0", ""},
			b:    []string{"TestB", testFailStr, "0", ""},
			want: 1,
		},
		{
			name: "field_change_count_descending",
			a:    []string{"TestA", testPassStr, "12", ""},
			b:    []string{"TestB", testPassStr, "11", ""},
			want: -1,
		},
		{
			name: "full_ties_compare_equal",
			a:    []string{"TestA", testPassStr, "0", "pkg:F[a|b]"},
			b:    []string{"TestB", testPassStr, "0", "(2 more field differences)"},
			want: 0,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, compareRiskyTests(tt.a, tt.b))
		})
	}

	t.Run("sorts_whole_table", func(t *testing.T) {
		rows := [][]string{
			{GeneratedTestFunctionPrefix + "Gen", testFailStr, "9", "pkg:F[x]"},
			{"TestB", testPassStr, "1", ""},
			{"TestC", testPassStr, "2", ""},
			{"TestA", testFailStr, "0", ""},
		}
		slices.SortFunc(rows, compareRiskyTests)
		assert.Equal(t, [][]string{
			{"TestA", testFailStr, "0", ""},
			{"TestC", testPassStr, "2", ""},
			{"TestB", testPassStr, "1", ""},
			{GeneratedTestFunctionPrefix + "Gen", testFailStr, "9", "pkg:F[x]"},
		}, rows)
	})
}
