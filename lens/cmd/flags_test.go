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
	tests := []struct {
		name  string
		build func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool)
	}{
		{
			name: "single_module",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "github.com/foo/bar@v1"}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, proj, c.ProjectDir)
					assert.Equal(t, "github.com/foo/bar@v1", c.ModuleVersionFlag)
					// AbsProjDir is set by Config.Prepare(), not ParseFlags
					assert.Equal(t, "", c.AbsProjDir)
				}
				return args, nil, check, false
			},
		},
		{
			name: "multi_module",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				mods := "a@v1,b@v2"
				args := []string{"-project", proj, "-modules", mods}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, mods, c.ModulesVersionFlag)
				}
				return args, nil, check, false
			},
		},
		{
			name: "gomod_path",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				gomod := filepath.Join(t.TempDir(), "go.mod")
				args := []string{"-project", proj, "-gomod", gomod}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, gomod, c.UpdatedGoModFile)
				}
				return args, nil, check, false
			},
		},
		{
			name: "gowork_path",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				gowork := filepath.Join(t.TempDir(), "go.work")
				args := []string{"-project", proj, "-gowork", gowork}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, gowork, c.UpdatedGoWorkFile)
				}
				return args, nil, check, false
			},
		},
		{
			name: "custom_flags",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "m@v1", "-str", "val", "-num", "2", "-ok"}
				cfs := []CustomFlag{
					{Name: "str", DefaultValue: "", Usage: "", Type: "string"},
					{Name: "num", DefaultValue: 0, Usage: "", Type: "int"},
					{Name: "ok", DefaultValue: false, Usage: "", Type: "bool"},
				}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, "val", c.CustomFlags["str"])
					assert.Equal(t, "2", c.CustomFlags["num"])
					assert.Equal(t, "true", c.CustomFlags["ok"])
				}
				return args, cfs, check, false
			},
		},
		{
			name: "missing_required",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj}
				return args, nil, nil, true
			},
		},
		{
			name: "gomod_gowork_conflict",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				gomod := filepath.Join(t.TempDir(), "go.mod")
				gowork := filepath.Join(t.TempDir(), "go.work")
				args := []string{"-project", proj, "-gomod", gomod, "-gowork", gowork}
				return args, nil, nil, true
			},
		},
		{
			name: "custom_flags_with_defaults",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "m@v1"}
				cfs := []CustomFlag{
					{Name: "defaultstr", DefaultValue: "default", Usage: "test string", Type: "string"},
					{Name: "defaultnum", DefaultValue: 42, Usage: "test int", Type: "int"},
					{Name: "defaultbool", DefaultValue: true, Usage: "test bool", Type: "bool"},
				}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, "default", c.CustomFlags["defaultstr"])
					assert.Equal(t, "42", c.CustomFlags["defaultnum"])
					assert.Equal(t, "true", c.CustomFlags["defaultbool"])
				}
				return args, cfs, check, false
			},
		},
		{
			name: "custom_flags_overriding_defaults",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "m@v1", "-overridestr", "overridden", "-overridenum", "100", "-overridebool=false"}
				cfs := []CustomFlag{
					{Name: "overridestr", DefaultValue: "default", Usage: "test string", Type: "string"},
					{Name: "overridenum", DefaultValue: 42, Usage: "test int", Type: "int"},
					{Name: "overridebool", DefaultValue: true, Usage: "test bool", Type: "bool"},
				}
				check := func(t *testing.T, c *lens.Config) {
					assert.Equal(t, "overridden", c.CustomFlags["overridestr"])
					assert.Equal(t, "100", c.CustomFlags["overridenum"])
					assert.Equal(t, "false", c.CustomFlags["overridebool"])
				}
				return args, cfs, check, false
			},
		},
		{
			name: "empty_custom_flags_slice",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "m@v1"}
				cfs := []CustomFlag{}
				check := func(t *testing.T, c *lens.Config) {
					assert.NotNil(t, c.CustomFlags)
					assert.Empty(t, c.CustomFlags)
				}
				return args, cfs, check, false
			},
		},
		{
			name: "nil_custom_flags",
			build: func(t *testing.T) ([]string, []CustomFlag, func(*testing.T, *lens.Config), bool) {
				proj := t.TempDir()
				args := []string{"-project", proj, "-module", "m@v1"}
				check := func(t *testing.T, c *lens.Config) {
					assert.NotNil(t, c.CustomFlags)
					assert.Empty(t, c.CustomFlags)
				}
				return args, nil, check, false
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			args, cfs, check, wantErr := tt.build(t)

			oldArgs := os.Args
			fs := flag.NewFlagSet(os.Args[0], flag.ContinueOnError)
			flag.CommandLine = fs
			os.Args = append([]string{os.Args[0]}, args...)

			oldGopath := build.Default.GOPATH
			build.Default.GOPATH = t.TempDir()
			oldGomod := os.Getenv("GOMODCACHE")
			os.Setenv("GOMODCACHE", t.TempDir())
			defer func() {
				os.Args = oldArgs
				build.Default.GOPATH = oldGopath
				_ = os.Setenv("GOMODCACHE", oldGomod)
			}()

			cfg, err := ParseFlags(cfs)
			if wantErr {
				require.Error(t, err)
				return
			}
			require.NoError(t, err)
			if check != nil {
				check(t, cfg)
			}
		})
	}
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
