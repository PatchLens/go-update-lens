package lens

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"sync"
)

type teeWriter struct {
	one io.Writer
	two io.Writer
}

// TeeWriter duplicates writes across chained writers.
func TeeWriter(writers ...io.Writer) io.WriteCloser {
	var last io.Writer
	for _, w := range writers {
		if w != nil {
			if last == nil {
				last = w
			} else {
				last = &teeWriter{
					one: last,
					two: w,
				}
			}
		}
	}

	if wc, ok := last.(io.WriteCloser); ok {
		return wc
	} else { // wrap in teeWriter to get close interface
		return &teeWriter{
			one: last,
			two: io.Discard,
		}
	}
}

func (w *teeWriter) Write(p []byte) (int, error) {
	n1, err1 := w.one.Write(p)
	n2, err2 := w.two.Write(p)
	if err1 == nil && err2 == nil && n1 != n2 {
		return 0, fmt.Errorf("uneven write %d != %d", n1, n2)
	}
	return n1, errors.Join(err1, err2)
}

func (w *teeWriter) Close() error {
	var err1, err2 error
	if v, ok := w.one.(io.WriteCloser); ok {
		err1 = v.Close()
	}
	if v, ok := w.two.(io.WriteCloser); ok {
		err2 = v.Close()
	}
	return errors.Join(err1, err2)
}

func newLimitedRollingBufferWriter(buf *bytes.Buffer, sizeLimit int) io.Writer {
	return &limitedRollingBuffer{
		buf:      buf,
		maxBytes: sizeLimit,
	}
}

type limitedRollingBuffer struct {
	buf      *bytes.Buffer
	maxBytes int
}

func (lb *limitedRollingBuffer) Write(p []byte) (n int, err error) {
	lb.buf.Write(p)
	if lb.buf.Len() > lb.maxBytes {
		current := lb.buf.Bytes()
		trimmed := current[len(current)-(lb.maxBytes/2):]
		lb.buf.Reset()
		lb.buf.WriteString("...")
		lb.buf.Write(trimmed)
	}
	return len(p), nil
}

type lockedBuffer struct {
	mu  sync.Mutex
	buf *bytes.Buffer
}

// NewLockedBuffer returns a mutex-protected buffer.
func NewLockedBuffer() *lockedBuffer {
	return &lockedBuffer{
		buf: &bytes.Buffer{},
	}
}

func (lb *lockedBuffer) Write(p []byte) (int, error) {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	return lb.buf.Write(p)
}

func (lb *lockedBuffer) Bytes() []byte {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	b := lb.buf.Bytes()
	out := make([]byte, len(b))
	copy(out, b)
	return out
}

func (lb *lockedBuffer) String() string {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	return lb.buf.String()
}

func (lb *lockedBuffer) Len() int {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	return lb.buf.Len()
}

func (lb *lockedBuffer) Reset() {
	lb.mu.Lock()
	defer lb.mu.Unlock()

	lb.buf.Reset()
}
