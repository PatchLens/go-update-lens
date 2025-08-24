package lens

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestRootModule(t *testing.T) {
	t.Parallel()

	t.Run("single_entry", func(t *testing.T) {
		mods := []ModuleChange{{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		assert.Equal(t, mods[0], rootModule(mods))
	})

	t.Run("one_direct_in_multiple", func(t *testing.T) {
		mods := []ModuleChange{
			{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0", Indirect: true},
			{Name: "modB", PriorVersion: "v0.1.0", NewVersion: "v0.2.0", Indirect: false},
			{Name: "modC", PriorVersion: "v0.9.0", NewVersion: "v1.0.0", Indirect: true},
		}
		assert.Equal(t, mods[1], rootModule(mods))
	})

	t.Run("multiple_direct_modules", func(t *testing.T) {
		mods := []ModuleChange{
			{Name: "modA", PriorVersion: "v1.0.0", NewVersion: "v1.1.0", Indirect: false},
			{Name: "modB", PriorVersion: "v0.1.0", NewVersion: "v0.2.0", Indirect: false},
		}
		assert.Equal(t, ModuleChange{}, rootModule(mods))
	})
}
