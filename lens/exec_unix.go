//go:build unix

package lens

import (
	"errors"
	"os/exec"
	"syscall"
)

// processKilledBySIGKILL reports whether err from an executed process indicates
// termination by SIGKILL, the typical out-of-memory kill signature.
func processKilledBySIGKILL(err error) bool {
	var exitErr *exec.ExitError
	if !errors.As(err, &exitErr) {
		return false
	}
	ws, ok := exitErr.Sys().(syscall.WaitStatus)
	return ok && ws.Signaled() && ws.Signal() == syscall.SIGKILL
}
