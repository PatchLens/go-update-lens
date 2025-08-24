package lens

import (
	"bytes"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"github.com/vmihailenco/msgpack/v5"
)

func TestStorageCommon(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name  string
		store Storage
	}{
		{
			name:  "mem",
			store: NewMemStorage(),
		},
		{
			name:  "prefix",
			store: KeyPrefixStorage(NewMemStorage(), "prefix"),
		},
	}

	if !testing.Short() {
		dir := filepath.Join(t.TempDir(), "badger")
		badgerStorage, err := NewBadgerStorage(dir, 200)
		require.NoError(t, err)
		t.Cleanup(func() { badgerStorage.Close() })

		tests = append(tests, struct {
			name  string
			store Storage
		}{
			name:  "badger",
			store: badgerStorage,
		})
	}

	for _, tc := range tests {
		t.Run(tc.name+"_save_clear", func(t *testing.T) {
			data := []byte{1, 2, 3}

			require.NoError(t, tc.store.SaveState("t1", data))
			require.NoError(t, tc.store.Clear())

			keys, err := tc.store.ListKeys()
			require.NoError(t, err)
			assert.Empty(t, keys)
		})

		t.Run(tc.name+"_save_load_delete", func(t *testing.T) {
			require.NoError(t, tc.store.Clear()) // ensure storage is reset
			data := []byte{1, 2, 3}

			require.NoError(t, tc.store.SaveState("t1", data))
			got, ok, err := tc.store.LoadState("t1")
			require.NoError(t, err)
			require.True(t, ok)
			assert.Equal(t, data, got)
			require.NoError(t, tc.store.DeleteState("t1"))
			_, ok, err = tc.store.LoadState("t1")
			require.NoError(t, err)
			assert.False(t, ok)
		})

		t.Run(tc.name+"_list_keys", func(t *testing.T) {
			require.NoError(t, tc.store.Clear()) // ensure storage is reset

			require.NoError(t, tc.store.SaveState("a1", []byte{1}))
			require.NoError(t, tc.store.SaveState("a2", []byte{2}))
			require.NoError(t, tc.store.SaveState("b1", []byte{3}))

			keys, err := tc.store.ListKeys()
			require.NoError(t, err)
			assert.ElementsMatch(t, []string{"a1", "a2", "b1"}, keys)

			keys, err = tc.store.ListKeysPrefix("a")
			require.NoError(t, err)
			assert.ElementsMatch(t, []string{"a1", "a2"}, keys)
		})

		t.Run(tc.name+"_null_byte_truncate", func(t *testing.T) {
			require.NoError(t, tc.store.Clear()) // ensure storage is reset
			// data slice contains an embedded NUL at index 2
			data := []byte{1, 2, 0, 4, 5}

			require.NoError(t, tc.store.SaveState("nullTest", data))
			got, ok, err := tc.store.LoadState("nullTest")
			require.NoError(t, err)
			require.True(t, ok)
			assert.Equal(t, data, got)
		})

		t.Run(tc.name+"_blob_liveness", func(t *testing.T) {
			require.NoError(t, tc.store.Clear()) // ensure storage is reset
			// write some non-trivial content
			want := make([]byte, 1024)
			for i := range want {
				want[i] = byte(i % 251) // deterministic
			}
			require.NoError(t, tc.store.SaveState("live", want))

			// read it back
			got, ok, err := tc.store.LoadState("live")
			require.NoError(t, err)
			require.True(t, ok)

			// trigger another update to confirm buffer remains valid
			_ = tc.store.SaveState("dummy", []byte{1})

			assert.Equal(t, want, got)
		})

		t.Run(tc.name+"_concurrent", func(t *testing.T) {
			require.NoError(t, tc.store.Clear()) // ensure storage is reset

			type payload struct {
				N int
				S string
			}
			makeBlob := func(n int) []byte {
				b, _ := msgpack.Marshal(payload{N: n, S: strings.Repeat("x", 4096)})
				return b
			}

			// the record we will read over and over
			require.NoError(t, tc.store.SaveState("target", makeBlob(42)))

			// writer goroutine: churn the database while we read
			done := make(chan struct{})
			go func() {
				var i int
				for {
					select {
					case <-done:
						return
					default:
					}
					_ = tc.store.SaveState("w"+strconv.Itoa(i%8), makeBlob(i))
					i++
				}
			}()

			// repeatedly load and unmarshal
			for i := 0; i < 1_000; i++ {
				got, ok, err := tc.store.LoadState("target")
				require.NoError(t, err)
				require.True(t, ok)

				var out payload
				require.NoError(t, msgpack.Unmarshal(got, &out))
				require.Equal(t, 42, out.N)
			}

			close(done)
		})
	}
}

func TestBadgerStorage(t *testing.T) {
	t.Run("SaveLoadDelete", func(t *testing.T) { // additional file validation after store
		if testing.Short() {
			t.Skip("skip in short mode")
		}
		t.Parallel()

		path := filepath.Join(t.TempDir(), "db")
		store, err := NewBadgerStorage(path, 50)
		require.NoError(t, err)
		defer store.Close()

		data := []byte{1, 2, 3}
		require.NoError(t, store.SaveState("t1", data))
		got, ok, err := store.LoadState("t1")
		require.NoError(t, err)
		require.True(t, ok)
		assert.Equal(t, data, got)
		require.NoError(t, store.DeleteState("t1"))
		_, ok, err = store.LoadState("t1")
		require.NoError(t, err)
		assert.False(t, ok)

		entries, err := os.ReadDir(path)
		require.NoError(t, err)
		assert.NotEmpty(t, entries)
	})

	t.Run("LargeBlobs", func(t *testing.T) {
		if testing.Short() {
			t.Skip("skip in short mode")
		}

		const insertCount = 4
		path := filepath.Join(t.TempDir(), "blob")
		store, err := NewBadgerStorage(path, 50)
		require.NoError(t, err)
		defer store.Close()
		oldLimit := badgerSplitLimit
		badgerSplitLimit = 2 * 1024 * 1024
		t.Cleanup(func() { badgerSplitLimit = oldLimit })

		data := make([][]byte, insertCount)
		for i := 0; i < insertCount; i++ {
			size := int(float64(i+1) * 1.2 * 1024 * 1024)
			data[i] = bytes.Repeat([]byte{byte(i + 1)}, size)
			require.NoError(t, store.SaveState("big-"+strconv.Itoa(i), data[i]))
		}
		for i := 0; i < insertCount; i++ {
			got, ok, err := store.LoadState("big-" + strconv.Itoa(i))
			require.NoError(t, err)
			require.True(t, ok)
			require.Len(t, got, len(data[i]))
			assert.Equal(t, data[i], got)
		}

		entries, err := os.ReadDir(path)
		require.NoError(t, err)
		assert.NotEmpty(t, entries)
	})
}

func TestMemStorage(t *testing.T) {
	// Currently all memStorage checks are covered by TestStorageCommon
}

func TestKeyPrefixStorage(t *testing.T) {
	tests := []struct {
		name   string
		prefix string
		keys   []string
		filter string
		expect []string
	}{
		{
			name:   "simple",
			prefix: "p",
			keys:   []string{"k1", "sub/k2"},
			filter: "k",
			expect: []string{"k1"},
		},
		{
			name:   "nested",
			prefix: "dir/sub",
			keys:   []string{"a", "sub/a1"},
			filter: "sub",
			expect: []string{"sub/a1"},
		},
	}

	for _, tc := range tests {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()

			base := NewMemStorage()
			store := KeyPrefixStorage(base, tc.prefix)

			for _, k := range tc.keys {
				require.NoError(t, store.SaveState(k, []byte(k)))
				got, ok, err := store.LoadState(k)
				require.NoError(t, err)
				require.True(t, ok)
				assert.Equal(t, []byte(k), got)
			}

			var wantBase []string
			for _, k := range tc.keys {
				wantBase = append(wantBase, tc.prefix+";"+k)
			}
			keys, err := base.ListKeys()
			require.NoError(t, err)
			assert.ElementsMatch(t, wantBase, keys)
			keys, err = store.ListKeys()
			require.NoError(t, err)
			assert.ElementsMatch(t, tc.keys, keys)
			keys, err = store.ListKeysPrefix(tc.filter)
			require.NoError(t, err)
			assert.ElementsMatch(t, tc.expect, keys)

			for _, k := range tc.keys {
				require.NoError(t, store.DeleteState(k))
			}
			keys, err = base.ListKeys()
			require.NoError(t, err)
			assert.Empty(t, keys)
			keys, err = store.ListKeys()
			require.NoError(t, err)
			assert.Empty(t, keys)
		})
	}

	t.Run("empty", func(t *testing.T) {
		t.Parallel()

		base := NewMemStorage()
		wrapped := KeyPrefixStorage(base, "")
		assert.Equal(t, base, wrapped)
	})
}
