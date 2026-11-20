package lens

import (
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestFileExists(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()

	exists := FileExists(dir)
	assert.True(t, exists)

	file := filepath.Join(dir, "file.txt")
	exists = FileExists(file)
	assert.False(t, exists)

	_, err := os.Create(file)
	require.NoError(t, err)

	exists = FileExists(file)
	assert.True(t, exists)
}

func TestFileWithinDir(t *testing.T) {
	t.Parallel()

	root1 := filepath.Join("/tmp", "rootA")
	root2 := filepath.Join("/var", "other")

	tests := []struct {
		name     string
		filePath string
		dirPath  string
		want     bool
	}{
		{
			name:     "direct_child",
			filePath: filepath.Join(root1, "foo.txt"),
			dirPath:  root1,
			want:     true,
		},
		{
			name:     "nested_deeper",
			filePath: filepath.Join(root1, "sub", "dir", "bar.log"),
			dirPath:  root1,
			want:     true,
		},
		{
			name:     "directory_itself",
			filePath: root1,
			dirPath:  root1,
			want:     true,
		},
		{
			name:     "outside_sibling",
			filePath: filepath.Join(root2, "baz.md"),
			dirPath:  root1,
			want:     false,
		},
		{
			name:     "up_dir..",
			filePath: filepath.Join(root1, "..", "other", "file"),
			dirPath:  root1,
			want:     false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ok, err := fileWithinDir(tt.filePath, tt.dirPath)
			require.NoError(t, err)
			assert.Equal(t, tt.want, ok)
		})
	}
}

func TestCopyFile(t *testing.T) {
	t.Parallel()

	srcContent := "test data"
	src, err := os.CreateTemp("", "copyfile-test-*.txt")
	require.NoError(t, err)
	t.Cleanup(func() {
		_ = os.Remove(src.Name())
	})
	_, err = src.WriteString(srcContent)
	require.NoError(t, err)
	require.NoError(t, src.Close())

	dst, err := os.CreateTemp("", "copyfile-test-*.txt")
	require.NoError(t, err)
	t.Cleanup(func() {
		_ = os.Remove(dst.Name())
	})
	require.NoError(t, dst.Close())

	t.TempDir()
	err = CopyFile(src.Name(), dst.Name())
	require.NoError(t, err)
	dstContent, err := os.ReadFile(dst.Name())
	require.NoError(t, err)
	assert.Equal(t, srcContent, string(dstContent))
}

func TestCopyDir(t *testing.T) {
	t.Parallel()

	t.Run("success", func(t *testing.T) {
		srcDir := t.TempDir()
		dstDir := t.TempDir()

		require.NoError(t, os.MkdirAll(filepath.Join(srcDir, "dir1", "dir2"), 0755))
		files := map[string]string{
			"file1.txt":           "file1-test_content",
			"file2.txt":           "file2-test_content",
			"dir1/file1.txt":      "dir1/file1-test_content",
			"dir1/file2.txt":      "dir1/file2-test_content",
			"dir1/dir2/file1.txt": "dir1/dir2/file1-test_content",
			"dir1/dir2/file2.txt": "dir1/dir2/file2-test_content",
		}
		for name, content := range files {
			require.NoError(t, os.WriteFile(filepath.Join(srcDir, name), []byte(content), 0644))
		}

		require.NoError(t, CopyDir(t.Context(), srcDir, dstDir, nil))

		// every file lands at its relative path with matching content
		for name, want := range files {
			got, err := os.ReadFile(filepath.Join(dstDir, name))
			require.NoError(t, err)
			assert.Equal(t, want, string(got))
		}
	})

	t.Run("copy_error_surfaces", func(t *testing.T) {
		srcDir := t.TempDir()
		dstDir := t.TempDir()

		files := map[string]string{
			"a.txt": "a-test_content",
			"b.txt": "b-test_content",
			"c.txt": "c-test_content",
		}
		for name, content := range files {
			require.NoError(t, os.WriteFile(filepath.Join(srcDir, name), []byte(content), 0644))
		}
		// directory shadows a.txt so its copy fails on create
		require.NoError(t, os.MkdirAll(filepath.Join(dstDir, "a.txt"), 0755))

		err := CopyDir(t.Context(), srcDir, dstDir, nil)
		require.Error(t, err)
		// root cause must surface, not just the context cancel triggered by it
		assert.Contains(t, err.Error(), "a.txt")

		for name, content := range files {
			if name == "a.txt" {
				continue
			}
			got, readErr := os.ReadFile(filepath.Join(dstDir, name))
			if os.IsNotExist(readErr) { // walk may abort before launching every copy
				continue
			}
			require.NoError(t, readErr)
			assert.Equal(t, content, string(got))
		}

		info, err := os.Stat(filepath.Join(dstDir, "a.txt"))
		require.NoError(t, err)
		assert.True(t, info.IsDir())
	})

	t.Run("walk_error_mid_copy", func(t *testing.T) {
		srcDir := t.TempDir()
		dstDir := t.TempDir()

		// large enough that the b.txt copy is still running when the walk fails
		bigContent := strings.Repeat("abcdefgh", 1<<20)
		require.NoError(t, os.WriteFile(filepath.Join(srcDir, "b.txt"), []byte(bigContent), 0644))
		require.NoError(t, os.MkdirAll(filepath.Join(srcDir, "m"), 0755))
		xPath := filepath.Join(srcDir, "x.txt")
		require.NoError(t, os.WriteFile(xPath, []byte("x-test_content"), 0644))

		var completed atomic.Int64
		// remove x.txt when the walk reaches dir m so lstat fails after b.txt's copy launched
		removeX := func(target string, info os.FileInfo) {
			if target == filepath.Join(dstDir, "m") {
				require.NoError(t, os.Remove(xPath))
			} else if !info.IsDir() { // count settled file copies
				completed.Add(1)
			}
		}

		err := CopyDir(t.Context(), srcDir, dstDir, removeX)
		require.Error(t, err)
		require.ErrorIs(t, err, fs.ErrNotExist)

		// in-flight copy must settle before return
		assert.Equal(t, int64(1), completed.Load())

		entries, err := os.ReadDir(dstDir) // only entries walked before the failure appear
		require.NoError(t, err)
		require.Len(t, entries, 2)
		assert.Equal(t, "b.txt", entries[0].Name())
		assert.Equal(t, "m", entries[1].Name())

		// in-flight copy of b.txt must be fully written when CopyDir returns
		got, err := os.ReadFile(filepath.Join(dstDir, "b.txt"))
		require.NoError(t, err)
		assert.Equal(t, []byte(bigContent), got)
	})
}

func TestReplaceFile(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()

	src, err := os.CreateTemp(dir, "src-*.txt")
	require.NoError(t, err)
	_, err = src.WriteString("source data")
	require.NoError(t, err)
	require.NoError(t, src.Close())

	dest, err := os.CreateTemp(dir, "dest-*.txt")
	require.NoError(t, err)
	destPath := dest.Name()
	require.NoError(t, dest.Close())

	err = replaceFile(src.Name(), destPath)
	require.NoError(t, err)

	content, err := os.ReadFile(destPath)
	require.NoError(t, err)
	assert.Equal(t, "source data", string(content))

	_, err = os.Stat(src.Name())
	assert.True(t, os.IsNotExist(err))
}

func TestWriteChmod(t *testing.T) {
	t.Parallel()

	root := t.TempDir()
	// create nested directories and files
	sub1 := filepath.Join(root, "sub1")
	sub2 := filepath.Join(sub1, "sub2")
	require.NoError(t, os.MkdirAll(sub2, 0777))

	files := []string{
		filepath.Join(root, "file1.txt"),
		filepath.Join(sub1, "file2.txt"),
		filepath.Join(sub2, "file3.txt"),
	}
	for _, f := range files {
		require.NoError(t, os.WriteFile(f, []byte("content"), 0444))
	}

	// create a symlink which should be skipped
	link := filepath.Join(root, "link")
	require.NoError(t, os.Symlink(files[0], link))
	linkInfo, err := os.Lstat(link)
	require.NoError(t, err)

	// remove write access from root and sub after creation
	require.NoError(t, os.Chmod(sub1, 0555))
	require.NoError(t, os.Chmod(root, 0555))

	require.NoError(t, WriteChmod(t.Context(), root))

	err = filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		require.NoError(t, err)
		info, err := os.Lstat(path)
		require.NoError(t, err)
		if info.Mode()&os.ModeSymlink != 0 {
			assert.Equal(t, linkInfo.Mode(), info.Mode())
			return nil
		}
		perm := info.Mode().Perm()
		assert.NotZero(t, perm&0o222, path)
		if info.IsDir() {
			assert.NotZero(t, perm&0o111, path)
		}
		return nil
	})
	require.NoError(t, err)
}

func TestConcurrentWalk(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()

	// Create test file structure
	require.NoError(t, os.MkdirAll(filepath.Join(dir, "subdir1", "subdir2"), 0755))
	require.NoError(t, os.MkdirAll(filepath.Join(dir, "subdir3"), 0755))

	files := []string{
		filepath.Join(dir, "file1.txt"),
		filepath.Join(dir, "file2.txt"),
		filepath.Join(dir, "subdir1", "file3.txt"),
		filepath.Join(dir, "subdir1", "subdir2", "file4.txt"),
		filepath.Join(dir, "subdir3", "file5.txt"),
	}

	for _, f := range files {
		require.NoError(t, os.WriteFile(f, []byte("content"), 0644))
	}

	// Collect paths via concurrentWalk
	var mu sync.Mutex
	var collectedPaths []string

	walkFn := func(path string, info os.FileInfo) error {
		if !info.IsDir() {
			mu.Lock()
			collectedPaths = append(collectedPaths, path)
			mu.Unlock()
		}
		return nil
	}

	err := concurrentWalk(t.Context(), dir, false, walkFn)
	require.NoError(t, err)

	// Verify all files were found
	assert.Len(t, collectedPaths, len(files))
	for _, expectedFile := range files {
		assert.Contains(t, collectedPaths, expectedFile)
	}
}
