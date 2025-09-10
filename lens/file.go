package lens

import (
	"context"
	"errors"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"runtime"
	"strings"

	"golang.org/x/sync/errgroup"
)

// FileExists reports whether the named file exists.
func FileExists(filename string) bool {
	if _, err := os.Stat(filename); err != nil {
		return !os.IsNotExist(err)
	}
	return true
}

// fileWithinDir returns true if the provided filePath is within the given directory.
func fileWithinDir(filePath, dirPath string) (bool, error) {
	// Get absolute and cleaned paths
	absFile, err := filepath.Abs(filePath)
	if err != nil {
		return false, err
	}
	absDir, err := filepath.Abs(dirPath)
	if err != nil {
		return false, err
	}
	absFile = filepath.Clean(absFile)
	absDir = filepath.Clean(absDir)

	// Add separator to prevent false positives (/dir1 vs /dir)
	rel, err := filepath.Rel(absDir, absFile)
	if err != nil {
		return false, err
	}

	// If rel starts with "..", file is outside the directory
	if strings.HasPrefix(rel, "..") || strings.HasPrefix(filepath.ToSlash(rel), "../") {
		return false, nil
	}
	return true, nil
}

func replaceFile(source, destination string) error {
	if _, err := os.Stat(destination); err == nil {
		if err = os.Remove(destination); err != nil {
			return err
		}
	}

	// Rename the source to the destination (requires same filesystem)
	return os.Rename(source, destination)
}

// CopyFile copies src to dst. If src is a symlink, it recreates the symlink at dst pointing to the same target.
// Otherwise, it copies the file’s contents (using os.Create’s default mode).
func CopyFile(src, dst string) (err error) {
	if info, err := os.Lstat(src); err != nil {
		return err
	} else if info.Mode()&os.ModeSymlink != 0 {
		target, err := os.Readlink(src)
		if err != nil {
			return err
		}
		return os.Symlink(target, dst)
	}

	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer func() { _ = in.Close() }()

	out, err := os.Create(dst) // uses default file mode (0666 & umask)
	if err != nil {
		return err
	}
	defer func() {
		if cerr := out.Close(); err == nil {
			err = cerr
		}
	}()

	if _, err = io.Copy(out, in); err != nil {
		return err
	}
	return out.Sync()
}

// CopyDir recursively copies src directory contents into dst.
func CopyDir(ctx context.Context, src, dst string, progressNotify func(string, os.FileInfo)) error {
	eg, ctx := errgroup.WithContext(ctx)
	eg.SetLimit(runtime.NumCPU() * 4)
	err := filepath.Walk(src, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		select { // abort walk if any copy failed
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		rel, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}
		target := filepath.Join(dst, rel)
		if info.IsDir() {
			if progressNotify != nil {
				progressNotify(target, info)
			}
			return os.MkdirAll(target, 0755)
		} else {
			eg.Go(func() error { // copy operations may be slower, done async
				if progressNotify != nil {
					defer progressNotify(target, info)
				}
				return CopyFile(path, target)
			})
			return nil
		}
	})
	if err != nil {
		return err
	}
	return eg.Wait()
}

// WriteChmod adds write permissions for owner/group/others on every file and directory under root.
func WriteChmod(ctx context.Context, root string) error {
	return concurrentWalk(ctx, root, true, func(path string, info os.FileInfo) error {
		perm := info.Mode().Perm()
		newPerm := perm | 0o222 // add write for all
		if info.IsDir() {
			newPerm |= 0o111 // ensure exec bits so dirs stay traversable
		}
		if newPerm != perm {
			return os.Chmod(path, newPerm)
		}
		return nil
	})
}

func concurrentWalk(ctx context.Context, root string, skipSymlink bool, handler func(path string, info os.FileInfo) error) error {
	eg, ctx := errgroup.WithContext(ctx)
	eg.SetLimit(runtime.NumCPU() * 4)
	err1 := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		select { // abort walk if early failure
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		eg.Go(func() error {
			info, err := d.Info()
			if err != nil {
				return err
			} else if skipSymlink && info.Mode()&os.ModeSymlink != 0 {
				return nil // skip symlinks
			}
			return handler(path, info)
		})
		return nil
	})
	err2 := eg.Wait()
	return errors.Join(err1, err2)
}
