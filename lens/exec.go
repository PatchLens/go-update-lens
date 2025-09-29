package lens

import (
	"io"
	"os"
	"os/exec"
	"slices"
	"strings"

	"github.com/go-analyze/bulk"
)

// GoEnv returns environment entries for GOPATH and GOMODCACHE.
func GoEnv(gopath, gomodcache string) []string {
	env := make([]string, 0, 2)
	if gopath != "" {
		env = append(env, "GOPATH="+gopath)
	}
	if gomodcache != "" {
		env = append(env, "GOMODCACHE="+gomodcache)
	}
	return env
}

// NewProjectExec creates a command that runs in projectDir with env applied.
func NewProjectExec(projectDir string, env []string, name string, arg ...string) *exec.Cmd {
	cmd := exec.Command(name, arg...)
	cmd.Dir = projectDir
	cmd.Env = mergeSafeEnv(env)

	return cmd
}

func mergeSafeEnv(env []string) []string {
	envKeys := make([]string, len(env)) // check for os values we want to override
	for i, kv := range env {
		parts := strings.SplitN(kv, "=", 2)
		envKeys[i] = parts[0]
	}
	safeEnv := bulk.SliceFilterInPlace(func(envVar string) bool {
		if envVar == "" || envVar == "=" || strings.HasPrefix(envVar, "LD_") {
			return false // skip unsafe
		} else if parts := strings.SplitN(envVar, "=", 2); slices.Contains(envKeys, parts[0]) {
			return false // will be overridden by custom value
		}
		return true
	}, os.Environ())
	return append(safeEnv, env...)
}

// NewProjectLoggedExec runs a command in projectDir with env and logs output to stdout and stderr.
func NewProjectLoggedExec(projectDir string, env []string, name string, arg ...string) *exec.Cmd {
	cmd := NewProjectExec(projectDir, env, name, arg...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	return cmd
}

// NewProjectCapturedOutputExec runs a command in projectDir with env, streams output, and returns combined stdout and stderr.
func NewProjectCapturedOutputExec(projectDir string, env []string, name string, arg ...string) ([]byte, error) {
	cmd := NewProjectExec(projectDir, env, name, arg...)
	lb := newLockedBuffer()
	cmd.Stdout = &teeWriter{
		one: os.Stdout,
		two: lb,
	}
	cmd.Stderr = &teeWriter{
		one: os.Stderr,
		two: lb,
	}
	err := cmd.Run()
	return lb.Bytes(), err
}

// ExecGoTest runs go test for a single test function in the given directory.
func ExecGoTest(dir string, env []string, output io.Writer, tFunc *TestFunction) error {
	cmd := NewProjectExec(dir, env, "go", "test", "-timeout=30s", "-count=1", "-parallel=1",
		"-run", "^"+tFunc.FunctionName+"$")
	cmd.Stdout = output
	cmd.Stderr = output
	return cmd.Run()
}
