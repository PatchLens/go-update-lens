package lens

import (
	"crypto/sha1"
	"runtime"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewLimitingWaitGroup(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	limit := 3
	lwg := NewLimitingWaitGroup(limit)

	var mu sync.Mutex
	var running, maxRunning int
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			lwg.Take()

			mu.Lock()
			running++
			if running > maxRunning {
				maxRunning = running
			}
			mu.Unlock()

			time.Sleep(10 * time.Millisecond)

			mu.Lock()
			running--
			mu.Unlock()

			lwg.Release()
		}()
	}

	lwg.Join()

	mu.Lock()
	maxVal := maxRunning
	mu.Unlock()
	require.LessOrEqual(t, maxVal, limit)
}

func TestStripedMutexSameKeyExclusive(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	sm := newStripedMutex(8)

	var mu sync.Mutex
	var running, maxRunning int
	const goroutines = 20
	var wg sync.WaitGroup
	wg.Add(goroutines)
	for i := 0; i < goroutines; i++ {
		go func() {
			l := sm.Lock("key")

			mu.Lock()
			running++
			if running > maxRunning {
				maxRunning = running
			}
			mu.Unlock()

			time.Sleep(5 * time.Millisecond)

			mu.Lock()
			running--
			mu.Unlock()

			l.Unlock()
			wg.Done()
		}()
	}
	wg.Wait()

	require.Equal(t, 1, maxRunning)
}

func TestStripedMutexDifferentKeysConcurrent(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}
	t.Parallel()

	sm := newStripedMutex(8)

	var mu sync.Mutex
	var running, maxRunning int
	const goroutines = 20
	var wg sync.WaitGroup
	wg.Add(goroutines)
	for i := 0; i < goroutines; i++ {
		key := "a"
		if i%2 == 0 {
			key = "b"
		}
		go func(k string) {
			l := sm.Lock(k)

			mu.Lock()
			running++
			if running > maxRunning {
				maxRunning = running
			}
			mu.Unlock()

			time.Sleep(5 * time.Millisecond)

			mu.Lock()
			running--
			mu.Unlock()

			l.Unlock()
			wg.Done()
		}(key)
	}
	wg.Wait()

	require.Greater(t, maxRunning, 1)
}

func TestLimitStringLines(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name      string
		input     string
		lineCount int
		head      bool
		expected  string
	}{
		{
			name:      "no_truncation",
			input:     "line1\nline2\nline3",
			lineCount: 4,
			head:      true,
			expected:  "line1\nline2\nline3",
		},
		{
			name:      "truncate_from_head",
			input:     "a\nb\nc\nd",
			lineCount: 2,
			head:      true,
			expected:  "a\nb",
		},
		{
			name:      "truncate_from_tail",
			input:     "a\nb\nc\nd",
			lineCount: 2,
			head:      false,
			expected:  "c\nd",
		},
		{
			name:      "empty_string",
			input:     "",
			lineCount: 1,
			head:      true,
			expected:  "",
		},
		{
			name:      "single_line",
			input:     "single",
			lineCount: 1,
			head:      true,
			expected:  "single",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := limitStringLines(tt.input, tt.lineCount, tt.head)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestBytesKey(t *testing.T) {
	t.Run("short", func(t *testing.T) {
		t.Parallel()

		// strings of length <= 20 should be returned unchanged
		shorts := []string{
			"",                     // empty
			"hello",                // short ASCII
			"12345678901234567890", // exactly 20 bytes
		}
		for _, s := range shorts {
			got := bytesKey([]byte(s))
			assert.Equal(t, s, got)
		}
	})

	t.Run("long", func(t *testing.T) {
		// strings of length > 20 bytes should be hashed
		long := "123456789012345678901" // 21 bytes
		got := bytesKey([]byte(long))

		// compute expected raw SHA-1 sum
		sum := sha1.Sum([]byte(long))
		expected := string(sum[:])

		// ensure it's the raw SHA-1 bytes, not the original string
		assert.Equal(t, expected, got)
		assert.NotEqual(t, long, got)
	})

	t.Run("different", func(t *testing.T) {
		a := []byte("abcdefghijklmnopqrstuvwxyz")  // 26 bytes
		b := []byte("abcdefghijklmnopqrstuvwxyz0") // 27 bytes, differs by last byte
		c := []byte("abcdefghijklmnopqrstuvwxy0")  // 26 bytes, differs by last byte
		keyA := bytesKey(a)
		keyB := bytesKey(b)
		keyC := bytesKey(c)

		assert.NotEqual(t, keyA, keyB)
		assert.NotEqual(t, keyB, keyC)
		assert.NotEqual(t, keyA, keyC)
	})
}

func TestStringKey(t *testing.T) {
	t.Run("short", func(t *testing.T) {
		t.Parallel()

		// strings of length <= 20 should be returned unchanged
		shorts := []string{
			"",                     // empty
			"hello",                // short ASCII
			"12345678901234567890", // exactly 20 bytes
		}
		for _, s := range shorts {
			got := stringKey(s)
			assert.Equal(t, s, got)
		}
	})

	t.Run("long", func(t *testing.T) {
		// strings of length > 20 bytes should be hashed
		long := "123456789012345678901" // 21 bytes
		got := stringKey(long)

		// compute expected raw SHA-1 sum
		sum := sha1.Sum([]byte(long))
		expected := string(sum[:])

		// ensure it's the raw SHA-1 bytes, not the original string
		assert.Equal(t, expected, got)
		assert.NotEqual(t, long, got)
	})

	t.Run("different", func(t *testing.T) {
		a := "abcdefghijklmnopqrstuvwxyz"  // 26 bytes
		b := "abcdefghijklmnopqrstuvwxyz0" // 27 bytes, differs by last byte
		c := "abcdefghijklmnopqrstuvwxy0"  // 26 bytes, differs by last byte
		keyA := stringKey(a)
		keyB := stringKey(b)
		keyC := stringKey(c)

		assert.NotEqual(t, keyA, keyB)
		assert.NotEqual(t, keyB, keyC)
		assert.NotEqual(t, keyA, keyC)
	})
}
