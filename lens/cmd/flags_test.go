package cmd

import (
	"flag"
	"go/build"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/PatchLens/go-update-lens/lens"
)

func TestParseFlags(t *testing.T) {
	t.Run("single_module", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "github.com/foo/bar@v1"}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(nil)
		require.NoError(t, err)

		assert.Equal(t, proj, cfg.ProjectDir)
		assert.Equal(t, "github.com/foo/bar@v1", cfg.ModuleVersionFlag)
		// AbsProjDir is set by Config.Prepare(), not ParseFlags
		assert.Empty(t, cfg.AbsProjDir)
	})

	t.Run("multi_module", func(t *testing.T) {
		proj := t.TempDir()
		mods := "a@v1,b@v2"
		args := []string{"-project", proj, "-modules", mods}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(nil)
		require.NoError(t, err)

		assert.Equal(t, mods, cfg.ModulesVersionFlag)
	})

	t.Run("gomod_path", func(t *testing.T) {
		proj := t.TempDir()
		gomod := filepath.Join(t.TempDir(), "go.mod")
		args := []string{"-project", proj, "-gomod", gomod}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(nil)
		require.NoError(t, err)

		assert.Equal(t, gomod, cfg.UpdatedGoModFile)
	})

	t.Run("gowork_path", func(t *testing.T) {
		proj := t.TempDir()
		gowork := filepath.Join(t.TempDir(), "go.work")
		args := []string{"-project", proj, "-gowork", gowork}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(nil)
		require.NoError(t, err)

		assert.Equal(t, gowork, cfg.UpdatedGoWorkFile)
	})

	t.Run("custom_flags", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "m@v1", "-str", "val", "-num", "2", "-ok"}
		cfs := []CustomFlag{
			{Name: "str", DefaultValue: "", Usage: "", Type: "string"},
			{Name: "num", DefaultValue: 0, Usage: "", Type: "int"},
			{Name: "ok", DefaultValue: false, Usage: "", Type: "bool"},
		}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(cfs)
		require.NoError(t, err)

		assert.Equal(t, "val", cfg.CustomFlags["str"])
		assert.Equal(t, "2", cfg.CustomFlags["num"])
		assert.Equal(t, "true", cfg.CustomFlags["ok"])
	})

	t.Run("missing_required", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		_, err := ParseFlags(nil)
		require.Error(t, err)
	})

	t.Run("gomod_gowork_conflict", func(t *testing.T) {
		proj := t.TempDir()
		gomod := filepath.Join(t.TempDir(), "go.mod")
		gowork := filepath.Join(t.TempDir(), "go.work")
		args := []string{"-project", proj, "-gomod", gomod, "-gowork", gowork}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		_, err := ParseFlags(nil)
		require.Error(t, err)
	})

	t.Run("custom_flags_with_defaults", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "m@v1"}
		cfs := []CustomFlag{
			{Name: "defaultstr", DefaultValue: "default", Usage: "test string", Type: "string"},
			{Name: "defaultnum", DefaultValue: 42, Usage: "test int", Type: "int"},
			{Name: "defaultbool", DefaultValue: true, Usage: "test bool", Type: "bool"},
		}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(cfs)
		require.NoError(t, err)

		assert.Equal(t, "default", cfg.CustomFlags["defaultstr"])
		assert.Equal(t, "42", cfg.CustomFlags["defaultnum"])
		assert.Equal(t, "true", cfg.CustomFlags["defaultbool"])
	})

	t.Run("custom_flags_overriding_defaults", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "m@v1", "-overridestr", "overridden", "-overridenum", "100", "-overridebool=false"}
		cfs := []CustomFlag{
			{Name: "overridestr", DefaultValue: "default", Usage: "test string", Type: "string"},
			{Name: "overridenum", DefaultValue: 42, Usage: "test int", Type: "int"},
			{Name: "overridebool", DefaultValue: true, Usage: "test bool", Type: "bool"},
		}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(cfs)
		require.NoError(t, err)

		assert.Equal(t, "overridden", cfg.CustomFlags["overridestr"])
		assert.Equal(t, "100", cfg.CustomFlags["overridenum"])
		assert.Equal(t, "false", cfg.CustomFlags["overridebool"])
	})

	t.Run("empty_custom_flags_slice", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "m@v1"}
		cfs := []CustomFlag{}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(cfs)
		require.NoError(t, err)

		assert.NotNil(t, cfg.CustomFlags)
		assert.Empty(t, cfg.CustomFlags)
	})

	t.Run("nil_custom_flags", func(t *testing.T) {
		proj := t.TempDir()
		args := []string{"-project", proj, "-module", "m@v1"}

		oldArgs := os.Args
		fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
		flag.CommandLine = fs
		os.Args = append([]string{os.Args[0]}, args...)

		oldGopath := build.Default.GOPATH
		build.Default.GOPATH = t.TempDir()
		oldGomod := os.Getenv("GOMODCACHE")
		require.NoError(t, os.Setenv("GOMODCACHE", t.TempDir()))
		defer func() {
			os.Args = oldArgs
			build.Default.GOPATH = oldGopath
			_ = os.Setenv("GOMODCACHE", oldGomod)
		}()

		cfg, err := ParseFlags(nil)
		require.NoError(t, err)

		assert.NotNil(t, cfg.CustomFlags)
		assert.Empty(t, cfg.CustomFlags)
	})
}

func TestConfigSetupEnvironment(t *testing.T) {
	tests := []struct {
		name          string
		useGomodcache bool
		useGopath     bool
		wantErr       bool
	}{
		{name: "gomodcache_env", useGomodcache: true, useGopath: true},
		{name: "gopath_only", useGopath: true},
		{name: "missing_both", wantErr: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := lens.Config{ProjectDir: t.TempDir()}

			var gomodcache, gopath string
			if tt.useGomodcache {
				gomodcache = t.TempDir()
				gopath = t.TempDir()
			} else if tt.useGopath {
				gopath = t.TempDir()
			}
			oldGomod := os.Getenv("GOMODCACHE")
			_ = os.Setenv("GOMODCACHE", gomodcache)
			oldGopath := build.Default.GOPATH
			build.Default.GOPATH = gopath
			defer func() {
				_ = os.Setenv("GOMODCACHE", oldGomod)
				build.Default.GOPATH = oldGopath
			}()

			err := setupEnvironment(&cfg)
			if tt.wantErr {
				require.Error(t, err)
				return
			}
			require.NoError(t, err)
			assert.Equal(t, gopath, cfg.Gopath)
			expected := ""
			if tt.useGomodcache {
				expected = gomodcache
			} else if tt.useGopath {
				expected = filepath.Join(gopath, "pkg", "mod")
			}
			assert.Equal(t, expected, cfg.Gomodcache)
		})
	}
}
