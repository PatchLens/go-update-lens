package lens

import (
	"crypto/sha1"
	"hash"
	"hash/fnv"
	"runtime"
	"strings"
	"sync"

	"golang.org/x/sync/errgroup"
)

const ErrorLogPrefix = "!! "

// ErrGroupLimitCPU returns an errgroup limited to NumCPU.
func ErrGroupLimitCPU() *errgroup.Group {
	errGroup := &errgroup.Group{}
	errGroup.SetLimit(runtime.NumCPU())
	return errGroup
}

type limitingWaitGroup struct {
	limit int
	c     chan bool
}

func (l *limitingWaitGroup) Take() {
	<-l.c
}

func (l *limitingWaitGroup) Release() {
	l.c <- true
}

func (l *limitingWaitGroup) Join() {
	for i := 0; i < l.limit; i++ {
		l.Take() // take all capacity to ensure all have joined
	}
}

// LimitingWaitGroup restricts concurrent work and waits for completion.
type LimitingWaitGroup interface {
	// Take blocks until the wait group has capacity.
	Take()
	// Release should be invoked (typically in defer) to indicate the activity following Take() has completed.
	Release()
	// Join will block until all activities have completed. This implementation expects that once Join() is invoked, Take() will NOT be invoked again.
	Join()
}

// NewLimitingWaitGroup creates a LimitingWaitGroup with the given limit.
func NewLimitingWaitGroup(concurrencyLimit int) LimitingWaitGroup {
	c := make(chan bool, concurrencyLimit)
	for i := 0; i < concurrencyLimit; i++ {
		c <- true
	}
	return &limitingWaitGroup{
		limit: concurrencyLimit,
		c:     c,
	}
}

func limitStringLines(s string, count int, head bool) string {
	lines := strings.Split(s, "\n")
	if len(lines) > count {
		if head {
			lines = lines[:count]
		} else {
			lines = lines[len(lines)-count:]
		}
		return strings.Join(lines, "\n")
	} else {
		return s
	}
}

func newDefaultStripedMutex() *stripedMutex {
	return newStripedMutex(8081) // prime number provides better distributions
}

// newStripedMutex creates a new mutex with the given concurrency.
func newStripedMutex(stripes uint) *stripedMutex {
	m := &stripedMutex{
		make([]*sync.Mutex, stripes),
		&sync.Pool{New: func() interface{} { return fnv.New64() }},
	}
	for i := range m.locks {
		m.locks[i] = &sync.Mutex{}
	}

	return m
}

type stripedMutex struct {
	locks []*sync.Mutex
	pool  *sync.Pool
}

// Lock acquire lock for a given key, returning the mutex for an easy unlock.
func (m *stripedMutex) Lock(key string) *sync.Mutex {
	l := m.getLock(key)
	l.Lock()
	return l
}

// GetLock retrieve a lock for a given key.
func (m *stripedMutex) getLock(key string) *sync.Mutex {
	h := m.pool.Get().(hash.Hash64)
	defer m.pool.Put(h)
	h.Reset()
	_, _ = h.Write([]byte(key))
	return m.locks[h.Sum64()%uint64(len(m.locks))]
}

// stringKey provides a minimum string to be used for internal logic as a key. The string is NOT valid UTF-8, expected
// to only be used for internal comparisons and never provided externally.
func stringKey(str string) string {
	if len(str) <= 20 { // 20 is the byte size of sha1, if at or below that just use the raw string
		return str
	}
	return bytesKey([]byte(str))
}

// bytesKey provides a minimum string to be used for internal logic as a key. The string is NOT valid UTF-8, expected
// to only be used for internal comparisons and never provided externally.
func bytesKey(b []byte) string {
	if len(b) <= 20 { // 20 is the byte size of sha1, if at or below that just use the raw string
		return string(b)
	}
	sha := sha1.Sum(b)
	return string(sha[:])
}
