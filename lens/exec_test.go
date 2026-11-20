package lens

import (
	"io"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestMergeSafeEnv(t *testing.T) {
	// Setup requires environment changes, DO NOT RUN IN PARALLEL
	snapshot := os.Environ()
	t.Cleanup(func() {
		os.Clearenv()
		for _, kv := range snapshot {
			parts := strings.SplitN(kv, "=", 2)
			if len(parts) == 2 {
				require.NoError(t, os.Setenv(parts[0], parts[1]))
			}
		}
	})
	t.Setenv("FOO", "foo_os")
	t.Setenv("BAR", "bar_os")
	t.Setenv("LD_LIBRARY_PATH", "/lib/foo")

	testCases := []struct {
		name          string
		customEnv     []string
		expectPresent map[string]string // key=>value that must be in result
		expectAbsent  []string          // keys that must NOT be present in result
	}{
		{
			name:      "no_overrides_or_custom",
			customEnv: nil,
			expectPresent: map[string]string{
				"FOO": "foo_os",
				"BAR": "bar_os",
			},
			expectAbsent: []string{"LD_LIBRARY_PATH"},
		},
		{
			name:      "override_os_var",
			customEnv: []string{"FOO=foo_custom"},
			expectPresent: map[string]string{
				"FOO": "foo_custom", // must be custom value, not OS
				"BAR": "bar_os",
			},
			expectAbsent: []string{"LD_LIBRARY_PATH"},
		},
		{
			name:      "add_custom_var",
			customEnv: []string{"NEWVAR=newval"},
			expectPresent: map[string]string{
				"NEWVAR": "newval",
				"FOO":    "foo_os",
			},
			expectAbsent: []string{"LD_LIBRARY_PATH"},
		},
		{
			name:      "custom_var_with_unsafe_prefix_is_included",
			customEnv: []string{"LD_TEST=val"},
			expectPresent: map[string]string{
				"LD_TEST": "val",
			},
			expectAbsent: []string{"LD_LIBRARY_PATH"},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			merged := mergeSafeEnv(tc.customEnv)
			// Helper: convert to map for easy lookup
			resultMap := map[string]string{}
			for _, kv := range merged {
				if kv == "" || kv == "=" {
					continue
				}
				parts := strings.SplitN(kv, "=", 2)
				if len(parts) == 2 {
					resultMap[parts[0]] = parts[1]
				}
			}

			for key, val := range tc.expectPresent {
				got, ok := resultMap[key]
				assert.True(t, ok, "expected key %q present", key)
				if ok {
					assert.Equal(t, val, got, "expected value for %q", key)
				}
			}
			for _, key := range tc.expectAbsent {
				_, ok := resultMap[key]
				assert.False(t, ok, "expected key %q absent", key)
			}
		})
	}
}

func TestGoEnv(t *testing.T) {
	t.Parallel()

	assert.Empty(t, GoEnv("", ""))
	assert.Equal(t, []string{"GOPATH=/gp", "GOMODCACHE=/mod"}, GoEnv("/gp", "/mod"))
	assert.Equal(t, []string{"GOPATH=/gp"}, GoEnv("/gp", ""))
	assert.Equal(t, []string{"GOMODCACHE=/mod"}, GoEnv("", "/mod"))
}

func TestNewProjectExec(t *testing.T) {
	t.Setenv("FOO", "orig")

	dir := t.TempDir()
	cmd := NewProjectExec(dir, []string{"FOO=custom", "BAR=baz"}, "echo")
	assert.Equal(t, dir, cmd.Dir)
	env := strings.Join(cmd.Env, "\n")

	assert.Contains(t, env, "FOO=custom")
	assert.Contains(t, env, "BAR=baz")
	for _, e := range cmd.Env {
		if strings.HasPrefix(e, "FOO=") {
			assert.Equal(t, "FOO=custom", e)
		}
	}
}

func TestNewProjectLoggedExec(t *testing.T) {
	t.Setenv("FOO", "orig")

	dir := t.TempDir()
	cmd := NewProjectLoggedExec(dir, []string{"FOO=custom", "BAR=baz"}, "echo")
	assert.Equal(t, dir, cmd.Dir)
	env := strings.Join(cmd.Env, "\n")

	assert.Contains(t, env, "FOO=custom")
	assert.Contains(t, env, "BAR=baz")
	for _, e := range cmd.Env {
		if strings.HasPrefix(e, "FOO=") {
			assert.Equal(t, "FOO=custom", e)
		}
	}
}

func TestNewProjectCapturedOutputExec(t *testing.T) {
	t.Parallel()

	out, err := NewProjectCapturedOutputExec(".", nil, "sh", "-c", "echo stdout && echo stderr >&2")
	require.NoError(t, err)
	result := string(out)

	assert.Contains(t, result, "stdout")
	assert.Contains(t, result, "stderr")
}

func TestProcessKilledBySIGKILL(t *testing.T) {
	t.Parallel()

	runSh := func(script string) error {
		return exec.Command("sh", "-c", script).Run()
	}

	testCases := []struct {
		name         string
		err          error
		expectKilled bool
	}{
		{"nil_error", nil, false},
		{"sigkill_death", runSh("kill -9 $$"), true},
		{"normal_exit_137", runSh("exit 137"), false},
		{"normal_exit_one", runSh("exit 1"), false},
		{"command_not_found", exec.Command("lens-no-such-command").Run(), false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			assert.Equal(t, tc.expectKilled, processKilledBySIGKILL(tc.err))
		})
	}
}

func TestExecGoTestOOMWarning(t *testing.T) {
	// Mutates PATH and the global log writer, DO NOT RUN IN PARALLEL
	origLogWriter := log.Writer()
	t.Cleanup(func() { log.SetOutput(origLogWriter) })

	testCases := []struct {
		name          string
		script        string
		expectErr     require.ErrorAssertionFunc
		expectOOMWarn bool
	}{
		{
			name:          "sigkill_warns",
			script:        "#!/bin/sh\nkill -9 $$\n",
			expectErr:     require.Error,
			expectOOMWarn: true,
		},
		{
			name:      "exit_137_no_warning",
			script:    "#!/bin/sh\nexit 137\n",
			expectErr: require.Error,
		},
		{
			name:      "clean_exit_no_warning",
			script:    "#!/bin/sh\nexit 0\n",
			expectErr: require.NoError,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			binDir := t.TempDir()
			goBin := filepath.Join(binDir, "go")
			require.NoError(t, os.WriteFile(goBin, []byte(tc.script), 0o755))
			t.Setenv("PATH", binDir+string(os.PathListSeparator)+os.Getenv("PATH"))

			logBuf := newLockedBuffer()
			log.SetOutput(logBuf)

			tFunc := &TestFunction{Function: Function{FunctionName: "TestSomething"}}
			err := ExecGoTest(t.TempDir(), nil, io.Discard, tFunc)

			tc.expectErr(t, err)
			if tc.expectOOMWarn {
				assert.Contains(t, logBuf.String(), "killed by OOM")
			} else {
				assert.NotContains(t, logBuf.String(), "killed by OOM")
			}
		})
	}
}
