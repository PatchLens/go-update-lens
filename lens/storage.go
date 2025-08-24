package lens

import (
	"errors"
	"fmt"
	"log"
	"os"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/dgraph-io/badger/v4"
	"github.com/dgraph-io/badger/v4/options"
	"github.com/dgraph-io/ristretto/v2"
)

const debugStorage = false

// Storage defines persistence methods for call frame blobs.
type Storage interface {
	SaveState(key string, blob []byte) error
	LoadState(key string) ([]byte, bool, error)
	DeleteState(key string) error
	// ListKeysPrefix returns all keys in the store that begin with the given prefix.
	ListKeysPrefix(prefix string) ([]string, error)
	// ListKeys returns all keys in the store.
	ListKeys() ([]string, error)
	Clear() error
	Close()
}

// KeyPrefixStorage wraps another Storage, prepending a fixed prefix to all keys.
// Its ListKeys and ListKeysPrefix methods strip the prefix before returning.
func KeyPrefixStorage(s Storage, prefix string) Storage {
	if prefix == "" {
		return s
	}
	return &prefixStorage{
		store:  s,
		prefix: prefix + ";",
	}
}

type prefixStorage struct {
	store  Storage
	prefix string
}

func (p *prefixStorage) SaveState(key string, blob []byte) error {
	return p.store.SaveState(p.prefix+key, blob)
}

func (p *prefixStorage) LoadState(key string) ([]byte, bool, error) {
	return p.store.LoadState(p.prefix + key)
}

func (p *prefixStorage) DeleteState(key string) error {
	return p.store.DeleteState(p.prefix + key)
}

func (p *prefixStorage) ListKeysPrefix(prefix string) ([]string, error) {
	underlying, err := p.store.ListKeysPrefix(p.prefix + prefix)
	if err != nil {
		return nil, err
	}
	stripped := make([]string, len(underlying))
	for i, k := range underlying {
		stripped[i] = strings.TrimPrefix(k, p.prefix)
	}
	return stripped, nil
}

func (p *prefixStorage) ListKeys() ([]string, error) {
	return p.ListKeysPrefix("")
}

func (p *prefixStorage) Clear() error {
	keys, err := p.ListKeys()
	if err != nil {
		return err
	}
	for _, key := range keys {
		if err := p.DeleteState(key); err != nil {
			return err
		}
	}
	return nil
}

func (p *prefixStorage) Close() {
	p.store.Close()
}

type memStorage struct {
	mu   sync.Mutex
	data map[string][]byte
}

// NewMemStorage returns an in-memory Storage implementation.
func NewMemStorage() Storage {
	return &memStorage{data: make(map[string][]byte)}
}

func (m *memStorage) SaveState(key string, blob []byte) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.data[key] = append([]byte(nil), blob...) // copy the blob to avoid external mutation
	return nil
}

func (m *memStorage) LoadState(key string) ([]byte, bool, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	blob, ok := m.data[key]
	if !ok {
		return nil, false, nil
	}
	return append([]byte(nil), blob...), true, nil
}

func (m *memStorage) DeleteState(key string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	delete(m.data, key)
	return nil
}

func (m *memStorage) ListKeysPrefix(prefix string) ([]string, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	var keys []string
	for k := range m.data {
		if strings.HasPrefix(k, prefix) {
			keys = append(keys, k)
		}
	}
	return keys, nil
}

func (m *memStorage) ListKeys() ([]string, error) {
	return m.ListKeysPrefix("")
}

func (m *memStorage) Clear() error {
	m.mu.Lock()
	defer m.mu.Unlock()

	clear(m.data)
	return nil
}

func (m *memStorage) Close() {
	// no resources to free
}

const badgerSplitBuffer = 16         // small extra buffer to avoid ever hitting the max anywhere
const badgerSplitLogFileBuffer = 240 // extra log file space compared to max value size
const splitPrefixString = "badger_split:"
const badgerCompression = options.ZSTD // disabling db compression results in less splitting, but benchmarks are worse

// badgerSplitLimit is max size before value split, updated by tests to reduce test overhead.
var badgerSplitLimit = (1 << 30) - badgerSplitBuffer - badgerSplitLogFileBuffer

var splitRe = regexp.MustCompile(`^` + splitPrefixString + `(\d+):(\d+):(\d+)$`)

type badgerStorage struct {
	path string
	db   *badger.DB
}

// NewBadgerStorage opens a Badger‐backed Storage.
func NewBadgerStorage(path string, maxMemMB int) (Storage, error) {
	// ensure directory exists
	if err := os.MkdirAll(path, 0755); err != nil {
		return nil, fmt.Errorf("create storage dir failed: %w", err)
	}

	clamp := func(val, lo, high int64) int64 {
		return min(max(val, lo), high)
	}
	var blockCacheSize int64 // blockCache should only be enabled if compression or encryption are enabled
	if badgerCompression != options.None {
		blockCacheSize = clamp(int64(maxMemMB/8), 2, 128) << 20
	}

	memTableSize := clamp(int64(maxMemMB/4), 8, 64) << 20
	// TotalRAM ≃ (NumMemtables × MemTableSize) + BlockCacheSize  + IndexCacheSize
	opts := badger.DefaultOptions(path).
		WithInMemory(false).
		WithDetectConflicts(true).
		WithChecksumVerificationMode(options.NoVerification).
		WithCompression(badgerCompression).
		WithZSTDCompressionLevel(8).
		WithNumMemtables(2).
		WithMemTableSize(memTableSize).
		WithBaseTableSize(memTableSize). // equal to mem table size gives one SST per flush, fewest compaction jobs
		WithBlockSize(1024 * 128).       // bigger blocks for better compression and fewer index entries
		WithBlockCacheSize(blockCacheSize).
		WithIndexCacheSize(clamp(int64(maxMemMB/4), 16, 128) << 20).
		WithValueLogFileSize(max(1024*1024*128, int64(badgerSplitLimit)+badgerSplitLogFileBuffer))

	if !debugStorage {
		opts = opts.
			WithLoggingLevel(badger.ERROR).
			WithMetricsEnabled(false)
	}

	db, err := badger.Open(opts)
	if err != nil {
		return nil, fmt.Errorf("open storage db failed: %w", err)
	}
	if debugStorage {
		go func() {
			for {
				time.Sleep(60 * time.Second)
				if db.IsClosed() {
					return
				}
				logMetrics := func(name string, metrics *ristretto.Metrics) {
					if metrics.Hits() != 0 || metrics.Misses() != 0 {
						log.Println(name + ": " + metrics.String())
					}
					metrics.Clear()
				}

				logMetrics("block", db.BlockCacheMetrics())
				logMetrics("index", db.IndexCacheMetrics())
			}
		}()
	}
	return &badgerStorage{path: path, db: db}, nil
}

func (b *badgerStorage) SaveState(key string, blob []byte) error {
	storeBlob := blob
	if badgerCompression == options.None { // manual compression allows us to better avoid split logic
		storeBlob = ZstdCompress(nil, blob)
	}

	return b.db.Update(func(txn *badger.Txn) error {
		mainKey := []byte(key)

		// wipe any old split‐parts if this key was previously split
		if item, err := txn.Get(mainKey); err == nil {
			_ = item.Value(func(val []byte) error {
				if m := splitRe.FindSubmatch(val); m != nil {
					oldCount, _ := strconv.Atoi(string(m[1]))
					for i := 0; i < oldCount; i++ {
						_ = txn.Delete([]byte(fmt.Sprintf("%s%s-%d", splitPrefixString, key, i)))
					}
				}
				return nil
			})
		} else if !errors.Is(err, badger.ErrKeyNotFound) {
			return err
		}

		// if small enough, write in one piece
		if len(storeBlob) <= badgerSplitLimit {
			return txn.Set(mainKey, storeBlob)
		}

		// else, split into roughly equal parts
		parts := len(storeBlob) / badgerSplitLimit
		if len(storeBlob)%badgerSplitLimit != 0 {
			parts++
		}
		base := len(storeBlob) / parts
		rem := len(storeBlob) % parts
		var off int
		for i := 0; i < parts; i++ {
			sz := base
			if i < rem {
				sz++
			}
			partKey := []byte(fmt.Sprintf("%s%s-%d", splitPrefixString, key, i))
			if err := txn.Set(partKey, storeBlob[off:off+sz]); err != nil {
				return err
			}
			off += sz
		}
		// store a marker of the form "badger_split:<parts>:<compressLen>:<origLen>"
		return txn.Set(mainKey, []byte(fmt.Sprintf("%s%d:%d:%d", splitPrefixString, parts, len(storeBlob), len(blob))))
	})
}

func (b *badgerStorage) LoadState(key string) ([]byte, bool, error) {
	var raw []byte
	err := b.db.View(func(txn *badger.Txn) error {
		item, err := txn.Get([]byte(key))
		if err != nil {
			if errors.Is(err, badger.ErrKeyNotFound) {
				return nil
			}
			return err
		}
		return item.Value(func(v []byte) error {
			raw = append([]byte(nil), v...)
			return nil
		})
	})
	if err != nil {
		return nil, false, err
	} else if raw == nil {
		return nil, false, nil
	}

	var stored []byte
	var decompressedBuffer []byte
	if m := splitRe.FindSubmatch(raw); m == nil {
		stored = raw // it was stored whole
	} else { // reassemble split value
		count, err := strconv.Atoi(string(m[1]))
		if err != nil {
			return nil, false, fmt.Errorf("failed to parse value count: %w", err)
		}
		compressedSize, err := strconv.Atoi(string(m[2]))
		if err != nil {
			return nil, false, fmt.Errorf("failed to parse compressed size: %w", err)
		}
		decompressedSize, err := strconv.Atoi(string(m[3]))
		if err != nil {
			return nil, false, fmt.Errorf("failed to parse decompressed size: %w", err)
		}
		stored = make([]byte, compressedSize)
		decompressedBuffer = make([]byte, decompressedSize) // prepare buffer since we know the exact size
		var off int
		if err := b.db.View(func(txn *badger.Txn) error {
			for i := 0; i < count; i++ {
				item, err := txn.Get([]byte(fmt.Sprintf("%s%s-%d", splitPrefixString, key, i)))
				if err != nil {
					return fmt.Errorf("large value failure on part %d: %w", i, err)
				} else if err := item.Value(func(v []byte) error {
					copy(stored[off:], v)
					off += len(v)
					return nil
				}); err != nil {
					return err
				}
			}
			return nil
		}); err != nil {
			return nil, false, err
		}
	}

	if badgerCompression == options.None { // manually decompress
		decompressed, err := ZstdDecompress(decompressedBuffer, stored)
		return decompressed, true, err
	} else {
		return stored, true, nil
	}
}

func (b *badgerStorage) DeleteState(key string) error {
	return b.db.Update(func(txn *badger.Txn) error {
		mainKey := []byte(key)
		item, err := txn.Get(mainKey)
		if err != nil {
			if errors.Is(err, badger.ErrKeyNotFound) {
				return nil
			}
			return err
		}
		// capture the marker/value
		var raw []byte
		_ = item.Value(func(v []byte) error {
			raw = append([]byte(nil), v...)
			return nil
		})
		// if it’s split, delete each part
		if m := splitRe.FindSubmatch(raw); m != nil {
			count, _ := strconv.Atoi(string(m[1]))
			for i := 0; i < count; i++ {
				if err := txn.Delete([]byte(fmt.Sprintf("%s%s-%d", splitPrefixString, key, i))); err != nil {
					return err
				}
			}
		}
		// delete the main key
		return txn.Delete(mainKey)
	})
}

func (b *badgerStorage) ListKeysPrefix(prefix string) ([]string, error) {
	var keys []string
	err := b.db.View(func(txn *badger.Txn) error {
		it := txn.NewIterator(badger.DefaultIteratorOptions)
		defer it.Close()
		for it.Seek([]byte(prefix)); it.ValidForPrefix([]byte(prefix)); it.Next() {
			k := string(it.Item().Key())
			// skip any split‐part keys
			if strings.HasPrefix(k, splitPrefixString) {
				continue
			}
			keys = append(keys, k)
		}
		return nil
	})
	return keys, err
}

func (b *badgerStorage) ListKeys() ([]string, error) {
	return b.ListKeysPrefix("")
}

func (b *badgerStorage) Clear() error {
	// Drop everything, including split parts
	return b.db.DropPrefix([]byte{})
}

func (b *badgerStorage) Close() {
	_ = b.db.Close()
	_ = os.RemoveAll(b.path)
}
