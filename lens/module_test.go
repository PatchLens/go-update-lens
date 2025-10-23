package lens

import (
	"errors"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/packages"
)

func TestAggregateFunctions(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name          string
		pkgPath       string
		expectedFuncs []string
	}{
		{
			name:    "difflib package",
			pkgPath: "github.com/pmezard/go-difflib/difflib",
			expectedFuncs: []string{
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.GetGroupedOpCodes",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.GetMatchingBlocks",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.GetOpCodes",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.QuickRatio",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.Ratio",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.RealQuickRatio",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.SetSeq1",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.SetSeq2",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.SetSeqs",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.chainB",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.findLongestMatch",
				"github.com/pmezard/go-difflib/difflib:*SequenceMatcher.isBJunk",
				"github.com/pmezard/go-difflib/difflib:GetContextDiffString",
				"github.com/pmezard/go-difflib/difflib:GetUnifiedDiffString",
				"github.com/pmezard/go-difflib/difflib:NewMatcher",
				"github.com/pmezard/go-difflib/difflib:NewMatcherWithJunk",
				"github.com/pmezard/go-difflib/difflib:SplitLines",
				"github.com/pmezard/go-difflib/difflib:WriteContextDiff",
				"github.com/pmezard/go-difflib/difflib:WriteUnifiedDiff",
				"github.com/pmezard/go-difflib/difflib:calculateRatio",
				"github.com/pmezard/go-difflib/difflib:formatRangeContext",
				"github.com/pmezard/go-difflib/difflib:formatRangeUnified",
				"github.com/pmezard/go-difflib/difflib:max",
				"github.com/pmezard/go-difflib/difflib:min",
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			cfg := &packages.Config{
				Mode: packages.NeedName | packages.NeedFiles | packages.NeedSyntax | packages.NeedTypes | packages.NeedTypesInfo,
			}
			pkgs, err := packages.Load(cfg, tc.pkgPath)
			require.NoError(t, err)
			require.Len(t, pkgs, 1)

			funcMap, err := aggregateFunctions(pkgs[0])
			require.NoError(t, err)

			keys := slices.Collect(maps.Keys(funcMap))
			sort.Strings(keys)

			sort.Strings(tc.expectedFuncs)
			assert.Equal(t, tc.expectedFuncs, keys)
		})
	}
}

func TestComputeChangeLineBitmap(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name         string
		oldDef       string
		newDef       string
		newFunc      bool
		radius       int
		expectBitmap []bool
	}{
		{
			name:         "empty newDef",
			oldDef:       "func foo() {}",
			newDef:       "",
			newFunc:      false,
			expectBitmap: []bool{true},
		},
		{
			name:         "empty oldDef",
			oldDef:       "",
			newDef:       "func foo() {}",
			newFunc:      true,
			expectBitmap: []bool{true},
		},
		{
			name:         "identical single line",
			oldDef:       "func foo() {}",
			newDef:       "func foo() {}",
			newFunc:      false,
			expectBitmap: []bool{false},
		},
		{
			name:         "one line changed",
			oldDef:       "func foo() {\n\tbar()\n}",
			newDef:       "func foo() {\n\tbaz()\n}",
			newFunc:      false,
			expectBitmap: []bool{false, true, false},
		},
		{
			name:         "line inserted in middle",
			oldDef:       "func foo() {\n\tbar()\n\tfoo()\n}",
			newDef:       "func foo() {\n\tbar()\n\tbaz()\n\tfoo()\n}",
			newFunc:      false,
			expectBitmap: []bool{false, false, false, false},
		},
		{
			name:         "line deleted from middle",
			oldDef:       "func foo() {\n\tbar()\n\tbaz()\n\tfoo()\n}",
			newDef:       "func foo() {\n\tbar()\n\tfoo()\n}",
			newFunc:      false,
			expectBitmap: []bool{false, false, true, false, false},
		},
		{
			name:         "replace multiple lines",
			oldDef:       "func foo() {\n\tbar()\n\tqux()\n}",
			newDef:       "func foo() {\n\tbaz()\n\tquux()\n}",
			newFunc:      false,
			expectBitmap: []bool{false, true, true, false},
		},
		{
			name:         "focus on newDef (newFunc=true)",
			oldDef:       "func foo() {\n\tbar()\n}",
			newDef:       "func foo() {\n\tbar()\n\tbaz()\n}",
			newFunc:      true,
			expectBitmap: []bool{false, false, true, false},
		},
		{
			name: "complex_diff_mixed_insert_delete",
			oldDef: `func foo() {
    a := 1
    b := 2
    c := a + b
    fmt.Println(c)
}`,
			newDef: `func foo() {
    a := 1
    x := 3
    b := 2
    c := a + b
    fmt.Println(c + x)
}`,
			newFunc:      false,
			expectBitmap: []bool{false, false, false, false, true, false},
		},
		{
			name:         "insert only radius one",
			oldDef:       "func foo() {\n    a := 1\n    b := 2\n}",
			newDef:       "func foo() {\n    a := 1\n    x := 3\n    b := 2\n}",
			newFunc:      false,
			radius:       1,
			expectBitmap: []bool{false, true, true, false},
		},
		{
			name:         "insert only radius two",
			oldDef:       "func foo() {\n    a := 1\n    b := 2\n}",
			newDef:       "func foo() {\n    a := 1\n    x := 3\n    y := 4\n    b := 2\n}",
			newFunc:      false,
			radius:       2,
			expectBitmap: []bool{true, true, true, true},
		},
		{
			name:         "remove only radius one",
			oldDef:       "func foo() {\n    a := 1\n    b := 2\n}",
			newDef:       "func foo() {\n    b := 2\n}",
			newFunc:      false,
			radius:       1,
			expectBitmap: []bool{false, true, false, false},
		},
		{
			name:         "insert next to delete",
			oldDef:       "func foo() {\n    a := 1\n    b := 2\n}",
			newDef:       "func foo() {\n    x := 3\n    b := 2\n}",
			newFunc:      false,
			radius:       1,
			expectBitmap: []bool{false, true, false, false},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			bitmap := computeChangeLineBitmap(tc.oldDef, tc.newDef, tc.newFunc, tc.radius)

			assert.Equal(t, tc.expectBitmap, bitmap)
		})
	}
}

func TestFindModuleVersionInGoMod(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()
	goMod := filepath.Join(dir, "go.mod")
	content := `module example.com/test

go 1.23

require (
    example.com/foo v1.2.3
    example.com/bar v0.1.0 // indirect
)`
	err := os.WriteFile(goMod, []byte(content), 0o644)
	require.NoError(t, err)

	ver, indirect, err := FindModuleVersionInGoMod(goMod, "example.com/foo")
	require.NoError(t, err)
	assert.Equal(t, "v1.2.3", ver)
	assert.False(t, indirect)

	ver, indirect, err = FindModuleVersionInGoMod(goMod, "example.com/bar")
	require.NoError(t, err)
	assert.Equal(t, "v0.1.0", ver)
	assert.True(t, indirect)

	ver, indirect, err = FindModuleVersionInGoMod(goMod, "example.com/missing")
	require.NoError(t, err)
	assert.Empty(t, ver)
	assert.False(t, indirect)
}

func TestDiffModulesFromGoModFiles(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()
	oldMod := filepath.Join(dir, "old.go.mod")
	newMod := filepath.Join(dir, "new.go.mod")
	oldContent := `module example.com/test

go 1.23

require (
    example.com/foo v1.0.0
    example.com/qux v0.1.0 // indirect
)`
	newContent := `module example.com/test

go 1.23

require (
    example.com/foo v1.1.0
    example.com/qux v0.2.0 // indirect
    example.com/bar v0.3.0
)`
	require.NoError(t, os.WriteFile(oldMod, []byte(oldContent), 0o644))
	require.NoError(t, os.WriteFile(newMod, []byte(newContent), 0o644))

	changes, err := DiffModulesFromGoModFiles(oldMod, newMod)
	require.NoError(t, err)

	sort.Slice(changes, func(i, j int) bool { return changes[i].Name < changes[j].Name })
	expected := []ModuleChange{
		{Name: "example.com/foo", PriorVersion: "v1.0.0", NewVersion: "v1.1.0", Indirect: false},
		{Name: "example.com/qux", PriorVersion: "v0.1.0", NewVersion: "v0.2.0", Indirect: true},
	}
	assert.Equal(t, expected, changes)
}

func TestParseGoMod(t *testing.T) {
	t.Parallel()

	cases := []struct {
		name    string
		content string
		want    map[string]string
		wantErr bool
	}{
		{
			name: "valid_gomod_requires",
			content: `module example.com/foo

	go 1.18

	require (
		github.com/foo/bar v1.2.3
		github.com/baz/qux v0.4.5 // indirect
	)
`,
			want: map[string]string{
				"github.com/foo/bar": "v1.2.3",
				"github.com/baz/qux": "v0.4.5",
			},
			wantErr: false,
		},
		{
			name:    "file not exist",
			content: "",
			want:    nil,
			wantErr: true,
		},
		{
			name:    "invalid syntax",
			content: "not a valid go mod content",
			want:    nil,
			wantErr: true,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// setup temp file
			tmp := t.TempDir()
			file := filepath.Join(tmp, "go.mod")
			if tc.name != "file not exist" {
				require.NoError(t, os.WriteFile(file, []byte(tc.content), 0644))
			}

			got, err := parseGoMod(file)

			if tc.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.Equal(t, tc.want, got)
			}
		})
	}
}

func TestParseGoWork(t *testing.T) {
	t.Parallel()

	cases := []struct {
		name    string
		content string
		prepare func(root string) // to create extra dirs
		want    []string
		wantErr bool
	}{
		{
			name: "simple_workspace",
			content: `go 1.18

use (
	./moduleA
	./moduleB
)
`,
			want:    []string{"moduleA", "moduleB"},
			wantErr: false,
		},
		{
			name: "glob_expansion",
			content: `go 1.18

use (
	./srv*
)
`,
			prepare: func(root string) {
				_ = os.MkdirAll(filepath.Join(root, "srv1"), 0755)
				_ = os.MkdirAll(filepath.Join(root, "srv2"), 0755)
			},
			want:    []string{"srv1", "srv2"},
			wantErr: false,
		},
		{
			name:    "file not exist",
			content: "",
			wantErr: true,
		},
		{
			name:    "invalid syntax",
			content: `use (### )`,
			wantErr: true,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			root := t.TempDir()
			workFile := filepath.Join(root, "go.work")
			if tc.prepare != nil {
				tc.prepare(root)
			}
			if tc.name != "file not exist" {
				require.NoError(t,
					os.WriteFile(workFile, []byte(tc.content), 0644),
				)
			}

			got, err := parseGoWork(workFile)

			if tc.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.ElementsMatch(t, tc.want, got)
			}
		})
	}
}

func TestParseProjectDeps(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name       string
		rootMod    string
		work       string
		modules    map[string]string
		pickNewest bool
		want       map[string]string
		wantErr    bool
	}{
		{
			name: "two_modules_prefer_oldest",
			work: "go 1.23\nuse ./m1\nuse ./m2\n",
			modules: map[string]string{
				"m1": `module example.com/m1

go 1.23

require example.com/foo v1.0.0
`,
				"m2": `module example.com/m2

go 1.23

require example.com/bar v0.2.0
`,
			},
			pickNewest: false,
			want: map[string]string{
				"example.com/foo": "v1.0.0",
				"example.com/bar": "v0.2.0",
			},
		},
		{
			name: "conflicting_versions_oldest",
			work: "go 1.23\nuse ./m1\nuse ./m2\n",
			modules: map[string]string{
				"m1": `module example.com/m1

go 1.23

require example.com/foo v1.0.0
`,
				"m2": `module example.com/m2

go 1.23

require example.com/foo v1.2.0
`,
			},
			pickNewest: false,
			want: map[string]string{
				"example.com/foo": "v1.0.0",
			},
		},
		{
			name: "conflicting_versions_newest",
			work: "go 1.23\nuse ./m1\nuse ./m2\n",
			modules: map[string]string{
				"m1": `module example.com/m1

go 1.23

require example.com/foo v1.0.0
`,
				"m2": `module example.com/m2

go 1.23

require example.com/foo v1.2.0
`,
			},
			pickNewest: true,
			want: map[string]string{
				"example.com/foo": "v1.2.0",
			},
		},
		{
			name: "root_work_modules_oldest",
			rootMod: `module example.com/root

go 1.23

require example.com/rootdep v0.1.0
require example.com/foo v1.0.0
`,
			work: "go 1.23\nuse ./m1\n",
			modules: map[string]string{
				"m1": `module example.com/m1

go 1.23

require example.com/foo v1.2.0
`,
			},
			pickNewest: false,
			want: map[string]string{
				"example.com/rootdep": "v0.1.0",
				"example.com/foo":     "v1.0.0",
			},
		},
		{
			name: "root_work_modules_newest",
			rootMod: `module example.com/root

go 1.23

require example.com/rootdep v0.1.0
require example.com/foo v1.0.0
`,
			work: "go 1.23\nuse ./m1\n",
			modules: map[string]string{
				"m1": `module example.com/m1

go 1.23

require example.com/foo v1.2.0
`,
			},
			pickNewest: true,
			want: map[string]string{
				"example.com/rootdep": "v0.1.0",
				"example.com/foo":     "v1.2.0",
			},
		},
		{
			name:       "no go.mod or go.work present",
			modules:    map[string]string{},
			pickNewest: false,
			wantErr:    true,
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()

			// write root go.mod if provided
			if tc.rootMod != "" {
				require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(tc.rootMod), 0o644))
			}
			// write go.work if provided
			if tc.work != "" {
				require.NoError(t, os.WriteFile(filepath.Join(dir, "go.work"), []byte(tc.work), 0o644))
			}
			// write each module's go.mod
			for subdir, content := range tc.modules {
				modDir := filepath.Join(dir, subdir)
				require.NoError(t, os.MkdirAll(modDir, 0o755))
				require.NoError(t, os.WriteFile(filepath.Join(modDir, "go.mod"), []byte(content), 0o644))
			}

			deps, err := parseProjectDeps(dir, tc.pickNewest)
			if tc.wantErr {
				require.Error(t, err)
				return
			}
			require.NoError(t, err)
			assert.Equal(t, tc.want, deps)
		})
	}
}

func TestAnalyzeModuleChanges(t *testing.T) {
	t.Parallel()

	t.Run("basic_change_detection_no_hook", func(t *testing.T) {
		gomodcache := t.TempDir()
		projectDir := t.TempDir()
		const modName = "example.com/hello"
		createModule := func(version, body string) {
			dir := filepath.Join(gomodcache, modName+"@"+version)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			modFile := "module " + modName + "\n\ngo 1.20\n"
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(modFile), 0o644))
			require.NoError(t, os.WriteFile(filepath.Join(dir, "hello.go"), []byte(body), 0o644))
		}

		createModule("v1.0.0", "package hello\n\nfunc Foo() int { return 1 }\n")
		createModule("v1.1.0", "package hello\n\nfunc Foo() int { return 2 }\n")

		mods := []ModuleChange{{Name: modName, PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		funcs, checked, err := AnalyzeModuleChanges(false, gomodcache, projectDir, mods, 0, nil)
		require.NoError(t, err)
		require.Len(t, checked, 1)
		assert.Equal(t, modName, checked[0])
		require.Len(t, funcs, 1)
		assert.Equal(t, "Foo", funcs[0].FunctionName)
		assert.Contains(t, funcs[0].Definition, "return 1")
	})

	t.Run("hook_collects_all_functions", func(t *testing.T) {
		gomodcache := t.TempDir()
		projectDir := t.TempDir()
		const modName = "example.com/multi"
		createModule := func(version, body string) {
			dir := filepath.Join(gomodcache, modName+"@"+version)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			modFile := "module " + modName + "\n\ngo 1.20\n"
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(modFile), 0o644))
			require.NoError(t, os.WriteFile(filepath.Join(dir, "multi.go"), []byte(body), 0o644))
		}

		// Old version has 2 functions
		createModule("v1.0.0", `package multi

func Foo() int { return 1 }
func Bar() int { return 10 }
`)
		// New version: Foo changed, Bar unchanged, Baz added
		createModule("v1.1.0", `package multi

func Foo() int { return 2 }
func Bar() int { return 10 }
func Baz() int { return 30 }
`)

		var hookCalled bool
		var hookData []ModuleAnalysisData
		mods := []ModuleChange{{Name: modName, PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		funcs, checked, err := AnalyzeModuleChanges(false, gomodcache, projectDir, mods, 0, func(data []ModuleAnalysisData) error {
			hookCalled = true
			hookData = data
			return nil
		})

		require.NoError(t, err)
		require.True(t, hookCalled, "hook should be called")
		require.Len(t, hookData, 1)

		// Check ModuleAnalysisData structure
		assert.Equal(t, modName, hookData[0].ModuleChange.Name)
		assert.Equal(t, "v1.0.0", hookData[0].ModuleChange.PriorVersion)
		assert.Equal(t, "v1.1.0", hookData[0].ModuleChange.NewVersion)

		// ChangedFunctions should only contain Foo (changed)
		require.Len(t, hookData[0].ChangedFunctions, 1)
		assert.Equal(t, "Foo", hookData[0].ChangedFunctions[0].FunctionName)

		// Main return value should also only have changed functions
		require.Len(t, funcs, 1)
		assert.Equal(t, "Foo", funcs[0].FunctionName)
		require.Len(t, checked, 1)
		assert.Equal(t, modName, checked[0])
	})

	t.Run("hook_error_propagates", func(t *testing.T) {
		gomodcache := t.TempDir()
		projectDir := t.TempDir()
		const modName = "example.com/error"
		createModule := func(version, body string) {
			dir := filepath.Join(gomodcache, modName+"@"+version)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			modFile := "module " + modName + "\n\ngo 1.20\n"
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(modFile), 0o644))
			require.NoError(t, os.WriteFile(filepath.Join(dir, "test.go"), []byte(body), 0o644))
		}

		createModule("v1.0.0", "package error\n\nfunc Test() int { return 1 }\n")
		createModule("v1.1.0", "package error\n\nfunc Test() int { return 2 }\n")

		mods := []ModuleChange{{Name: modName, PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		_, _, err := AnalyzeModuleChanges(false, gomodcache, projectDir, mods, 0, func(data []ModuleAnalysisData) error {
			return errors.New("test hook error")
		})

		require.Error(t, err)
		assert.Contains(t, err.Error(), "post-module analysis hook failed")
		assert.Contains(t, err.Error(), "test hook error")
	})

	t.Run("multiple_modules_hook_data", func(t *testing.T) {
		gomodcache := t.TempDir()
		projectDir := t.TempDir()
		createModule := func(modName, version, body string) {
			dir := filepath.Join(gomodcache, modName+"@"+version)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			modFile := "module " + modName + "\n\ngo 1.20\n"
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(modFile), 0o644))
			require.NoError(t, os.WriteFile(filepath.Join(dir, "code.go"), []byte(body), 0o644))
		}

		// Module alpha
		createModule("example.com/alpha", "v1.0.0", "package alpha\n\nfunc A1() int { return 1 }\n")
		createModule("example.com/alpha", "v1.1.0", "package alpha\n\nfunc A1() int { return 2 }\nfunc A2() int { return 3 }\n")

		// Module beta
		createModule("example.com/beta", "v2.0.0", "package beta\n\nfunc B1() int { return 10 }\n")
		createModule("example.com/beta", "v2.1.0", "package beta\n\nfunc B1() int { return 20 }\n")

		var hookData []ModuleAnalysisData
		mods := []ModuleChange{
			{Name: "example.com/alpha", PriorVersion: "v1.0.0", NewVersion: "v1.1.0"},
			{Name: "example.com/beta", PriorVersion: "v2.0.0", NewVersion: "v2.1.0"},
		}

		funcs, checked, err := AnalyzeModuleChanges(false, gomodcache, projectDir, mods, 0, func(data []ModuleAnalysisData) error {
			hookData = data
			return nil
		})

		require.NoError(t, err)
		require.Len(t, hookData, 2)

		// Check module alpha data
		assert.Equal(t, "example.com/alpha", hookData[0].ModuleChange.Name)
		require.Len(t, hookData[0].ChangedFunctions, 1) // only A1 changed

		// Check module beta data
		assert.Equal(t, "example.com/beta", hookData[1].ModuleChange.Name)
		require.Len(t, hookData[1].ChangedFunctions, 1) // B1 changed

		// Main return should have 2 changed functions total
		require.Len(t, funcs, 2)
		require.Len(t, checked, 2)
	})

	t.Run("no_changes", func(t *testing.T) {
		gomodcache := t.TempDir()
		projectDir := t.TempDir()
		const modName = "example.com/nochange"

		createModule := func(version, body string) {
			dir := filepath.Join(gomodcache, modName+"@"+version)
			require.NoError(t, os.MkdirAll(dir, 0o755))
			modFile := "module " + modName + "\n\ngo 1.20\n"
			require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(modFile), 0o644))
			require.NoError(t, os.WriteFile(filepath.Join(dir, "code.go"), []byte(body), 0o644))
		}

		// Same code in both versions
		sameCode := "package nochange\n\nfunc Same() int { return 42 }\n"
		createModule("v1.0.0", sameCode)
		createModule("v1.1.0", sameCode)

		var hookData []ModuleAnalysisData
		mods := []ModuleChange{{Name: modName, PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}}
		funcs, checked, err := AnalyzeModuleChanges(false, gomodcache, projectDir, mods, 0, func(data []ModuleAnalysisData) error {
			hookData = data
			return nil
		})

		require.NoError(t, err)
		require.Len(t, hookData, 1)

		// ChangedFunctions should be empty (no changes)
		assert.Empty(t, hookData[0].ChangedFunctions)

		// Main return should have no changed functions
		assert.Empty(t, funcs)
		require.Len(t, checked, 1)
	})
}

func TestFindModuleVersionWorkspace(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(dir, "m"), 0o755))
	work := "go 1.23\nuse ./m\n"
	require.NoError(t, os.WriteFile(filepath.Join(dir, "go.work"), []byte(work), 0o644))
	mod := `module example.com/m

go 1.23

require (
    example.com/foo v1.2.3
    example.com/bar v0.4.0 // indirect
)`
	require.NoError(t, os.WriteFile(filepath.Join(dir, "m", "go.mod"), []byte(mod), 0o644))

	ver, ind, err := FindModuleVersion(dir, "example.com/foo")
	require.NoError(t, err)
	assert.Equal(t, "v1.2.3", ver)
	assert.False(t, ind)

	ver, ind, err = FindModuleVersion(dir, "example.com/bar")
	require.NoError(t, err)
	assert.Equal(t, "v0.4.0", ver)
	assert.True(t, ind)

	ver, ind, err = FindModuleVersion(dir, "missing")
	require.NoError(t, err)
	assert.Empty(t, ver)
	assert.False(t, ind)
}

func TestDiffModulesFromGoWorkFiles(t *testing.T) {
	t.Parallel()

	oldDir := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(oldDir, "m"), 0o755))
	work := "go 1.23\nuse ./m\n"
	require.NoError(t, os.WriteFile(filepath.Join(oldDir, "go.work"), []byte(work), 0o644))
	oldMod := `module example.com/m

go 1.23

require example.com/foo v1.0.0`
	require.NoError(t, os.WriteFile(filepath.Join(oldDir, "m", "go.mod"), []byte(oldMod), 0o644))

	newDir := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(newDir, "m"), 0o755))
	require.NoError(t, os.WriteFile(filepath.Join(newDir, "go.work"), []byte(work), 0o644))
	newMod := `module example.com/m

go 1.23

require example.com/foo v1.1.0`
	require.NoError(t, os.WriteFile(filepath.Join(newDir, "m", "go.mod"), []byte(newMod), 0o644))

	changes, err := DiffModulesFromGoWorkFiles(oldDir, filepath.Join(newDir, "go.work"))
	require.NoError(t, err)
	require.Len(t, changes, 1)
	assert.Equal(t, ModuleChange{Name: "example.com/foo", PriorVersion: "v1.0.0", NewVersion: "v1.1.0"}, changes[0])
}

func TestProjectPackagePatterns(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name    string
		rootMod string
		work    string
		modules map[string]string
		want    []string
	}{
		{
			name:    "root only",
			rootMod: "module example.com/root\n\ngo 1.20\n",
			want:    []string{"./..."},
		},
		{
			name: "workspace",
			work: "go 1.20\nuse (\n    ./a\n    ./b\n)\n",
			modules: map[string]string{
				"a": "module example.com/a\n\ngo 1.20\n",
				"b": "module example.com/b\n\ngo 1.20\n",
			},
			want: []string{"./a/...", "./b/..."},
		},
		{
			name:    "root and workspace",
			rootMod: "module example.com/root\n\ngo 1.20\n",
			work:    "go 1.20\nuse ./m\n",
			modules: map[string]string{
				"m": "module example.com/m\n\ngo 1.20\n",
			},
			want: []string{"./...", "./m/..."},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			dir := t.TempDir()

			if tt.rootMod != "" {
				require.NoError(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(tt.rootMod), 0o644))
			}
			if tt.work != "" {
				require.NoError(t, os.WriteFile(filepath.Join(dir, "go.work"), []byte(tt.work), 0o644))
			}
			for m, content := range tt.modules {
				modDir := filepath.Join(dir, m)
				require.NoError(t, os.MkdirAll(modDir, 0o755))
				require.NoError(t, os.WriteFile(filepath.Join(modDir, "go.mod"), []byte(content), 0o644))
			}

			got, err := ProjectPackagePatterns(dir)
			require.NoError(t, err)
			assert.ElementsMatch(t, tt.want, got)
		})
	}
}
