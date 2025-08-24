package lens

import (
	"context"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
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
	srcDir := t.TempDir()

	require.NoError(t, os.MkdirAll(filepath.Join(srcDir, "dir1", "dir2"), 0755))
	files := map[string]string{
		filepath.Join(srcDir, "file1.txt"):                 "file1-test_content",
		filepath.Join(srcDir, "file2.txt"):                 "file2-test_content",
		filepath.Join(srcDir, "dir1", "file1.txt"):         "dir1/file1-test_content",
		filepath.Join(srcDir, "dir1", "file2.txt"):         "dir1/file2-test_content",
		filepath.Join(srcDir, "dir1", "dir2", "file1.txt"): "dir1/dir2/file1-test_content",
		filepath.Join(srcDir, "dir1", "dir2", "file2.txt"): "dir1/dir2/file2-test_content",
	}
	for path, content := range files {
		require.NoError(t, os.WriteFile(path, []byte(content), 0644))
	}

	dstDir := t.TempDir()
	require.NoError(t, CopyDir(context.Background(), srcDir, dstDir, nil))

	// Helper function to collect file contents
	collectFiles := func(root string) (map[string]string, error) {
		filesMap := make(map[string]string)
		err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
			if err != nil {
				return err
			}
			if !info.IsDir() {
				content, err := os.ReadFile(path)
				if err != nil {
					return err
				}
				filesMap[path] = string(content)
			}
			return nil
		})
		return filesMap, err
	}

	dstFiles, err := collectFiles(dstDir)
	require.NoError(t, err)
	require.Len(t, dstFiles, len(files))
	dstContents := slices.Collect(maps.Values(dstFiles))
	for _, v := range files {
		assert.True(t, slices.Contains(dstContents, v))
	}
}

func TestContainsSymlinkOutsideDir(t *testing.T) {
	t.Parallel()

	t.Run("symlink_outside", func(t *testing.T) {
		dir := t.TempDir()

		insideFile := filepath.Join(dir, "file.txt")
		require.NoError(t, os.WriteFile(insideFile, []byte("data"), 0o644))

		outside, err := os.CreateTemp("", "outside-*.txt")
		require.NoError(t, err)
		t.Cleanup(func() { _ = os.Remove(outside.Name()) })
		require.NoError(t, outside.Close())

		link := filepath.Join(dir, "outside_link")
		require.NoError(t, os.Symlink(outside.Name(), link))

		err = ContainsSymlinkOutsideDir(dir)
		require.Error(t, err)
	})

	t.Run("symlink_inside", func(t *testing.T) {
		dir := t.TempDir()

		insideFile := filepath.Join(dir, "file.txt")
		require.NoError(t, os.WriteFile(insideFile, []byte("data"), 0o644))

		link := filepath.Join(dir, "inside_link")
		require.NoError(t, os.Symlink(insideFile, link))

		err := ContainsSymlinkOutsideDir(dir)
		require.NoError(t, err)
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

	require.NoError(t, WriteChmod(context.Background(), root))

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
