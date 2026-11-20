package lens

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/dgraph-io/badger/v4"
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

			// writer goroutine: churn the database while we read, also rewriting the target key so
			// same-key save/load interleaving is exercised, not just other-key traffic
			done := make(chan struct{})
			var wg sync.WaitGroup
			wg.Add(1)
			go func() {
				defer wg.Done()
				var i int
				for {
					select {
					case <-done:
						return
					default:
					}
					_ = tc.store.SaveState("w"+strconv.Itoa(i%8), makeBlob(i))
					if i%4 == 0 { // rewrite the key under test with an alternating payload
						_ = tc.store.SaveState("target", makeBlob(42+(i/4)%2))
					}
					i++
				}
			}()

			// repeatedly load and unmarshal, accepting either payload written to the key
			for i := 0; i < 1_000; i++ {
				got, ok, err := tc.store.LoadState("target")
				require.NoError(t, err)
				require.True(t, ok)

				var out payload
				require.NoError(t, msgpack.Unmarshal(got, &out))
				assert.Contains(t, []int{42, 43}, out.N)
			}

			close(done)
			wg.Wait()
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

// splitMarkerValue rebuilds a main key marker matching the SaveState format.
func splitMarkerValue(parts int, compressedSize int, origLen int) []byte {
	return []byte(fmt.Sprintf("%s%d:%d:%d", splitPrefixString, parts, compressedSize, origLen))
}

func TestBadgerStorageSplitValues(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}

	oldLimit := badgerSplitLimit
	badgerSplitLimit = 16 * 1024
	t.Cleanup(func() { badgerSplitLimit = oldLimit })

	path := filepath.Join(t.TempDir(), "split")
	store, err := NewBadgerStorage(path, 50)
	require.NoError(t, err)
	t.Cleanup(store.Close)
	bs := store.(*badgerStorage)

	// two full parts plus a remainder splits into exactly three parts
	blobLen := 2*badgerSplitLimit + 100
	data := make([]byte, blobLen)
	for i := range data {
		data[i] = byte(i % 251) // deterministic
	}

	markerOf := func(key string) (parts int, size int) {
		var raw []byte
		require.NoError(t, bs.db.View(func(txn *badger.Txn) error {
			item, err := txn.Get([]byte(key))
			if err != nil {
				return err
			}
			return item.Value(func(v []byte) error {
				raw = append([]byte(nil), v...)
				return nil
			})
		}))
		m := splitRe.FindSubmatch(raw)
		require.NotNil(t, m, "expected %s to be stored as a split value", key)
		parts, _ = strconv.Atoi(string(m[1]))
		size, _ = strconv.Atoi(string(m[2]))
		return parts, size
	}

	setRaw := func(key string, val []byte) {
		require.NoError(t, bs.db.Update(func(txn *badger.Txn) error {
			return txn.Set([]byte(key), val)
		}))
	}

	// each case rewrites the main key marker to mirror a torn or corrupt state that
	// concurrent writes could previously produce between the two load views
	tests := []struct {
		name    string
		marker  func(parts int, size int) []byte
		wantErr string
	}{
		{ // old code failed with a missing part error only by luck of the shape
			name: "marker_claims_missing_part",
			marker: func(parts int, size int) []byte {
				return splitMarkerValue(parts+1, size, blobLen)
			},
			wantErr: "large value failure on part 3",
		},
		{ // old code panicked with a slice bounds error when parts outgrew the marker sized buffer
			name: "part_overruns_marker_buffer",
			marker: func(parts int, size int) []byte {
				return splitMarkerValue(parts, 8, blobLen)
			},
			wantErr: "split value length mismatch",
		},
		{ // old code silently returned trailing zeros when the marker overclaimed
			name: "marker_exceeds_parts_total",
			marker: func(parts int, size int) []byte {
				return splitMarkerValue(parts, size+5, blobLen)
			},
			wantErr: "split value length mismatch",
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			key := "corrupt-" + tc.name
			require.NoError(t, store.SaveState(key, data))

			parts, size := markerOf(key)
			require.Equal(t, 3, parts) // blobLen guarantees exactly three parts
			require.Positive(t, size)

			// baseline reassembly must be intact before simulating a corrupt state
			got, ok, err := store.LoadState(key)
			require.NoError(t, err)
			require.True(t, ok)
			assert.Equal(t, data, got)

			setRaw(key, tc.marker(parts, size))

			got, ok, err = store.LoadState(key)
			require.ErrorContains(t, err, tc.wantErr)
			assert.False(t, ok)
			assert.Nil(t, got)
		})
	}
}

func TestBadgerStorageSplitChurn(t *testing.T) {
	if testing.Short() {
		t.Skip("skip in short mode")
	}

	oldLimit := badgerSplitLimit
	badgerSplitLimit = 32 * 1024
	t.Cleanup(func() { badgerSplitLimit = oldLimit })

	path := filepath.Join(t.TempDir(), "churn")
	store, err := NewBadgerStorage(path, 50)
	require.NoError(t, err)
	t.Cleanup(store.Close)

	// two distinct multi-part blobs with different part counts plus a whole value,
	// any torn read would mix bytes or lengths and fail the exact equality checks
	splitA := make([]byte, 2*badgerSplitLimit+100) // three parts
	splitB := make([]byte, 3*badgerSplitLimit+50)  // four parts
	whole := []byte("small whole value")
	for i := range splitA {
		splitA[i] = byte(i % 251)
	}
	for i := range splitB {
		splitB[i] = byte(255 - i%247)
	}

	const key = "target"
	require.NoError(t, store.SaveState(key, splitA))

	done := make(chan struct{})
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := 0; ; i++ {
			select {
			case <-done:
				return
			default:
			}
			switch i % 4 {
			case 0:
				_ = store.SaveState(key, whole)
			case 1:
				_ = store.SaveState(key, splitB)
			case 2:
				_ = store.SaveState(key, splitA)
			case 3:
				_ = store.DeleteState(key)
			}
		}
	}()

	found := 0
	for i := 0; i < 500; i++ {
		got, ok, err := store.LoadState(key)
		require.NoError(t, err) // inconsistent snapshots must never surface as errors
		if !ok {
			continue // deleted between writer operations
		}
		assert.True(t, bytes.Equal(got, splitA) || bytes.Equal(got, splitB) || bytes.Equal(got, whole))
		found++
	}

	close(done)
	wg.Wait()

	// after writers stop the key must load exactly as saved
	require.NoError(t, store.SaveState(key, splitB))
	got, ok, err := store.LoadState(key)
	require.NoError(t, err)
	require.True(t, ok)
	assert.Equal(t, splitB, got)
	require.Positive(t, found) // reads must have observed values mid-churn
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

			wantBase := make([]string, len(tc.keys))
			for i, k := range tc.keys {
				wantBase[i] = tc.prefix + ";" + k
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
