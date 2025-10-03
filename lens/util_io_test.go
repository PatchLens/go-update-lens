package lens

import (
	"bytes"
	"errors"
	"io"
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

type mockWriter struct {
	data       []byte
	writeCount int
	err        error
}

func (m *mockWriter) Write(p []byte) (int, error) {
	if m.err != nil {
		return 0, m.err
	} else if m.writeCount > 0 && len(p) > m.writeCount {
		p = p[:m.writeCount]
	}
	m.data = append(m.data, p...)
	return len(p), nil
}

type mockCloser struct {
	closed bool
	err    error
}

func (m *mockCloser) Write(p []byte) (int, error) {
	return len(p), nil
}

func (m *mockCloser) Close() error {
	m.closed = true
	return m.err
}

func TestTeeWriterWrite(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name    string
		writers []io.Writer
		data    []byte
		wantN   int
		wantErr bool
	}{
		{
			name: "all_success",
			writers: func() []io.Writer {
				return []io.Writer{&mockWriter{}, &mockWriter{}}
			}(),
			data:  []byte("test"),
			wantN: 4,
		},
		{
			name: "different_counts",
			writers: func() []io.Writer {
				m1 := &mockWriter{}
				m2 := &mockWriter{writeCount: 3}
				return []io.Writer{m1, m2}
			}(),
			data:    []byte("test"),
			wantN:   0,
			wantErr: true,
		},
		{
			name: "one_error",
			writers: func() []io.Writer {
				m1 := &mockWriter{err: errors.New("error1")}
				m2 := &mockWriter{}
				return []io.Writer{m1, m2}
			}(),
			data:    []byte("test"),
			wantN:   0,
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			writer := TeeWriter(tt.writers...)
			n, err := writer.Write(tt.data)
			assert.Equal(t, tt.wantN, n)
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)

				if len(tt.writers) > 1 {
					for _, w := range tt.writers {
						if mw, ok := w.(*mockWriter); ok {
							assert.True(t, bytes.HasSuffix(mw.data, tt.data))
						} else if bb, ok := w.(*bytes.Buffer); ok {
							assert.True(t, bytes.HasSuffix(bb.Bytes(), tt.data))
						}
					}
				}
			}
		})
	}
}

func TestTeeWriterClose(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name    string
		writers []io.Writer
		wantErr bool
	}{
		{
			name:    "no_closers",
			writers: []io.Writer{bytes.NewBuffer(nil), bytes.NewBuffer(nil)},
		},
		{
			name: "one_writer_success",
			writers: func() []io.Writer {
				return []io.Writer{io.Discard}
			}(),
		},
		{
			name: "one_closer_success",
			writers: func() []io.Writer {
				return []io.Writer{&mockCloser{}, bytes.NewBuffer(nil)}
			}(),
		},
		{
			name: "two_closers_success",
			writers: func() []io.Writer {
				return []io.Writer{&mockCloser{}, &mockCloser{}}
			}(),
		},
		{
			name: "one_closer_error",
			writers: func() []io.Writer {
				mc := &mockCloser{err: errors.New("error")}
				return []io.Writer{mc, bytes.NewBuffer(nil)}
			}(),
			wantErr: true,
		},
		{
			name: "two_closers_error",
			writers: func() []io.Writer {
				mc1 := &mockCloser{err: errors.New("error1")}
				mc2 := &mockCloser{err: errors.New("error2")}
				return []io.Writer{mc1, mc2}
			}(),
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			writer := TeeWriter(tt.writers...)
			err := writer.Close()
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
			for _, w := range tt.writers {
				if mc, ok := w.(*mockCloser); ok {
					assert.True(t, mc.closed)
				}
			}
		})
	}
}

func TestLimitedRollingBufferWriter(t *testing.T) {
	t.Parallel()

	type step struct {
		data            []byte
		expectedContent string
		expectedLength  int
	}

	tests := []struct {
		name      string
		sizeLimit int
		steps     []step
	}{
		{
			name:      "single_write_no_truncate",
			sizeLimit: 10,
			steps: []step{{
				data:            []byte("hello"),
				expectedContent: "hello",
				expectedLength:  5,
			}},
		},
		{
			name:      "multiple_writes_with_truncations",
			sizeLimit: 8,
			steps: []step{
				{
					data:            []byte("12345"),
					expectedContent: "12345",
					expectedLength:  5,
				},
				{
					data:            []byte("67890"),
					expectedContent: "...7890",
					expectedLength:  7,
				},
				{
					data:            []byte("abc"),
					expectedContent: "...0abc",
					expectedLength:  7,
				},
				{
					data:            []byte("def"),
					expectedContent: "...cdef",
					expectedLength:  7,
				},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf := new(bytes.Buffer)
			writer := newLimitedRollingBufferWriter(buf, tt.sizeLimit)

			for _, step := range tt.steps {
				n, err := writer.Write(step.data)
				require.NoError(t, err)
				assert.Equal(t, len(step.data), n)
				assert.Equal(t, step.expectedContent, buf.String())
				assert.Equal(t, step.expectedLength, buf.Len())
			}
		})
	}
}

func TestLockedBufferConcurrentWrite(t *testing.T) {
	t.Parallel()

	lb := newLockedBuffer()
	var wg sync.WaitGroup
	const workers = 10
	const loops = 100
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < loops; j++ {
				_, _ = lb.Write([]byte("a"))
			}
		}()
	}
	wg.Wait()
	assert.Equal(t, workers*loops, lb.Len())
}
