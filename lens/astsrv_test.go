package lens

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"net"
	"net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

type mockPointHandler struct {
	pointCalls int32
	stateCalls int32
	panicCalls int32
}

func (m *mockPointHandler) HandleFuncPoint(LensMonitorMessagePoint) {
	atomic.AddInt32(&m.pointCalls, 1)
}

func (m *mockPointHandler) HandleFuncPointState(LensMonitorMessagePointState) {
	atomic.AddInt32(&m.stateCalls, 1)
}

func (m *mockPointHandler) HandleFuncPointPanic(LensMonitorMessagePointPanic) {
	atomic.AddInt32(&m.panicCalls, 1)
}

func newASTMux(h *mockPointHandler) *http.ServeMux {
	var iface astPointHandler = h
	srv := &astServer{maxFieldLen: 1024}
	srv.pointHandler.Store(&iface)
	mux := http.NewServeMux()
	mux.HandleFunc(lensMonitorEndpointPathError, srv.handleEventError)
	mux.HandleFunc(lensMonitorEndpointPathPoint, srv.handlePoint)
	mux.HandleFunc(lensMonitorEndpointPathState, srv.handlePointState)
	mux.HandleFunc(lensMonitorEndpointPathPanic, srv.handlePointPanic)
	return mux
}

var invalidMethods = []string{
	http.MethodGet, http.MethodHead, http.MethodPut,
	http.MethodPatch, http.MethodDelete, http.MethodConnect,
	http.MethodOptions, http.MethodTrace,
}

func TestAstExecServerStart(t *testing.T) {
	t.Parallel()

	t.Run("port_conflict", func(t *testing.T) {
		// hold a bound listener so the second bind on the same port fails
		holder, err := net.Listen("tcp", "127.0.0.1:0")
		require.NoError(t, err)
		t.Cleanup(func() { _ = holder.Close() })
		port := holder.Addr().(*net.TCPAddr).Port

		srv, err := astExecServerStart("127.0.0.1", port, nil, 1024)
		require.Error(t, err)
		assert.Nil(t, srv)
	})

	t.Run("serves_and_stops", func(t *testing.T) {
		port := freePort(t)
		handler := &mockPointHandler{}
		srv, err := astExecServerStart("127.0.0.1", port, handler, 1024)
		require.NoError(t, err)
		assert.Equal(t, port, srv.Port())

		var buf bytes.Buffer
		lensEncodeMessagePoint(&buf, 1, 12345, []lensMonitorStackFrame{})
		url := fmt.Sprintf("http://127.0.0.1:%d%s", port, lensMonitorEndpointPathPoint)
		// handlers run before the response is written, so the round trip guarantees delivery
		resp, err := http.Post(url, "application/octet-stream", &buf)
		require.NoError(t, err)
		require.NoError(t, resp.Body.Close())
		assert.Equal(t, http.StatusOK, resp.StatusCode)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.pointCalls))

		err = srv.Stop(context.Background())
		assert.NoError(t, err) // ErrServerClosed from Serve must not surface
	})
}

func TestASTServerHandlePoint(t *testing.T) {
	t.Parallel()

	handler := &mockPointHandler{}
	mux := newASTMux(handler)

	t.Run("valid", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePoint(&buf, 1, 12345, []lensMonitorStackFrame{})
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPoint, &buf)
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.pointCalls))
	})

	t.Run("invalid_binary", func(t *testing.T) {
		// Send truncated/invalid binary data
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPoint, bytes.NewBufferString("\x01"))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusBadRequest, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.pointCalls))
	})

	t.Run("method_not_allowed", func(t *testing.T) {
		for _, method := range invalidMethods {
			req := httptest.NewRequest(method, lensMonitorEndpointPathPoint, nil)
			w := httptest.NewRecorder()
			mux.ServeHTTP(w, req)
			assert.Equal(t, http.StatusMethodNotAllowed, w.Code)
		}
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.pointCalls))
	})
}

func TestASTServerHandlePointState(t *testing.T) {
	t.Parallel()

	handler := &mockPointHandler{}
	mux := newASTMux(handler)

	t.Run("valid", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePointState(&buf, 1, 12345, []lensMonitorStackFrame{}, nil)
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathState, &buf)
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.stateCalls))
	})

	t.Run("invalid_binary", func(t *testing.T) {
		// Send truncated/invalid binary data
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathState, bytes.NewBufferString("\x01"))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusBadRequest, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.stateCalls))
	})

	t.Run("method_not_allowed", func(t *testing.T) {
		for _, method := range invalidMethods {
			req := httptest.NewRequest(method, lensMonitorEndpointPathState, nil)
			w := httptest.NewRecorder()
			mux.ServeHTTP(w, req)
			assert.Equal(t, http.StatusMethodNotAllowed, w.Code)
		}
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.stateCalls))
	})
}

func TestASTServerHandlePointPanic(t *testing.T) {
	t.Parallel()

	handler := &mockPointHandler{}
	mux := newASTMux(handler)

	t.Run("valid", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessagePointPanic(&buf, 1, 12345, "test panic")
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPanic, &buf)
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.panicCalls))
	})

	t.Run("invalid_binary", func(t *testing.T) {
		// Send truncated/invalid binary data
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPanic, bytes.NewBufferString("\x01"))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusBadRequest, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.panicCalls))
	})

	t.Run("method_not_allowed", func(t *testing.T) {
		for _, method := range invalidMethods {
			req := httptest.NewRequest(method, lensMonitorEndpointPathPanic, nil)
			w := httptest.NewRecorder()
			mux.ServeHTTP(w, req)
			assert.Equal(t, http.StatusMethodNotAllowed, w.Code)
		}
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.panicCalls))
	})
}

func TestASTServerHandleEventError(t *testing.T) {
	t.Parallel()

	handler := &mockPointHandler{}
	mux := newASTMux(handler)

	t.Run("valid", func(t *testing.T) {
		var buf bytes.Buffer
		lensEncodeMessageError(&buf, 1, errors.New("test error"), []lensMonitorStackFrame{})
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathError, &buf)
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
	})

	t.Run("invalid_binary", func(t *testing.T) {
		// Send truncated/invalid binary data
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathError, bytes.NewBufferString("\x01"))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusBadRequest, w.Code)
	})

	t.Run("method_not_allowed", func(t *testing.T) {
		for _, method := range invalidMethods {
			req := httptest.NewRequest(method, lensMonitorEndpointPathError, nil)
			w := httptest.NewRecorder()
			mux.ServeHTTP(w, req)
			assert.Equal(t, http.StatusMethodNotAllowed, w.Code)
		}
	})
}
