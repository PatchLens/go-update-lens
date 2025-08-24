package lens

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/assert"
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
	srv := &astServer{}
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

func TestASTServerHandlePoint(t *testing.T) {
	t.Parallel()

	handler := &mockPointHandler{}
	mux := newASTMux(handler)

	t.Run("valid", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPoint, bytes.NewBufferString(`{"id":1}`))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.pointCalls))
	})

	t.Run("invalid_json", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPoint, bytes.NewBufferString("{"))
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
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathState, bytes.NewBufferString(`{"id":1}`))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.stateCalls))
	})

	t.Run("invalid_json", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathState, bytes.NewBufferString("{"))
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
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPanic, bytes.NewBufferString(`{"id":1}`))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
		assert.Equal(t, int32(1), atomic.LoadInt32(&handler.panicCalls))
	})

	t.Run("invalid_json", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathPanic, bytes.NewBufferString("{"))
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
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathError, bytes.NewBufferString(`{"id":1,"msg":"foo"}`))
		w := httptest.NewRecorder()
		mux.ServeHTTP(w, req)
		assert.Equal(t, http.StatusOK, w.Code)
	})

	t.Run("invalid_json", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodPost, lensMonitorEndpointPathError, bytes.NewBufferString("{"))
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
