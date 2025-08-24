package lens

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"log"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

// astServer wraps the HTTP server for receiving client messages.
type astServer struct {
	server       *http.Server
	err          atomic.Pointer[error]
	pointHandler atomic.Value
}

func (s *astServer) Port() int {
	_, portStr, _ := strings.Cut(s.server.Addr, ":")
	port, _ := strconv.Atoi(portStr)
	return port
}

type astPointHandler interface {
	HandleFuncPoint(LensMonitorMessagePoint)
	HandleFuncPointState(LensMonitorMessagePointState)
	HandleFuncPointPanic(LensMonitorMessagePointPanic)
}

// astExecServerStart constructs a astServer listening on host:port. Message handler functions are provided so that
// AST events can be evaluated as they occurs rather than needing to retain everything for later analysis.
func astExecServerStart(host string, port int, pointHandler astPointHandler) (*astServer, error) {
	addr := fmt.Sprintf("%s:%d", host, port)
	mux := http.NewServeMux()
	s := &astServer{}
	s.pointHandler.Store(&pointHandler)
	mux.HandleFunc(lensMonitorEndpointPathError, s.handleEventError)
	mux.HandleFunc(lensMonitorEndpointPathPoint, s.handlePoint)
	mux.HandleFunc(lensMonitorEndpointPathState, s.handlePointState)
	mux.HandleFunc(lensMonitorEndpointPathPanic, s.handlePointPanic)
	s.server = &http.Server{Addr: addr, Handler: mux}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		wg.Done()
		if err := s.server.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			s.err.Store(&err)
			log.Printf("%sAST Monitor Server error: %v", ErrorLogPrefix, err)
		}
	}()
	wg.Wait()
	time.Sleep(100 * time.Millisecond) // short wait to ensure error is communicated

	log.Printf("Test Execution Monitor started on %s", addr)
	return s, s.errCheck()
}

func (s *astServer) errCheck() error {
	errPtr := s.err.Load()
	if errPtr != nil {
		return *errPtr
	}
	return nil
}

// SetPointHandler sets the handlers to be used for future incoming function point calls.
func (s *astServer) SetPointHandler(pointHandler astPointHandler) error {
	s.pointHandler.Store(&pointHandler)
	return s.errCheck()
}

// StopOnProcessOrTimeout waits for the given process to exit (up to timeout)
// then shuts down the server and returns
func (s *astServer) StopOnProcessOrTimeout(pid int, timeout time.Duration) error {
	ticker := time.NewTicker(200 * time.Millisecond)
	defer ticker.Stop()
	deadline := time.Now().Add(timeout)
	var pollErr error
	for {
		if timeout > 0 && time.Now().After(deadline) {
			pollErr = fmt.Errorf("timeout waiting for process %d", pid)
			break // don't return, still stop server
		}

		// signal 0 checks for existence without sending a real signal
		err := syscall.Kill(pid, 0)
		if err != nil {
			if errors.Is(err, syscall.ESRCH) {
				break // the process has exited
			}
			pollErr = err
			break // don't return, still stop server
		}

		<-ticker.C
	}

	// graceful shutdown with context timeout
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	return errors.Join(pollErr, s.Stop(ctx), s.errCheck())
}

// Stop gracefully shuts down the server.
func (s *astServer) Stop(ctx context.Context) error {
	err1 := s.server.Shutdown(ctx)
	return errors.Join(err1, s.errCheck())
}

func (s *astServer) handlePoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	defer r.Body.Close()
	var msg LensMonitorMessagePoint
	if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
		log.Printf("%sFailed to decode LensMonitorMessagePoint: %v", ErrorLogPrefix, err)
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	handler := s.pointHandler.Load().(*astPointHandler)
	(*handler).HandleFuncPoint(msg)

	w.WriteHeader(http.StatusOK)
}

func (s *astServer) handlePointState(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	defer r.Body.Close()
	var msg LensMonitorMessagePointState
	if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
		log.Printf("%sFailed to decode LensMonitorMessagePointState: %v", ErrorLogPrefix, err)
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	handler := s.pointHandler.Load().(*astPointHandler)
	(*handler).HandleFuncPointState(msg)

	w.WriteHeader(http.StatusOK)
}

func (s *astServer) handlePointPanic(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	defer r.Body.Close()
	var msg LensMonitorMessagePointPanic
	if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
		log.Printf("%sFailed to decode LensMonitorMessagePointPanic: %v", ErrorLogPrefix, err)
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	handler := s.pointHandler.Load().(*astPointHandler)
	(*handler).HandleFuncPointPanic(msg)

	w.WriteHeader(http.StatusOK)
}

func (s *astServer) handleEventError(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	defer r.Body.Close()
	var msg LensMonitorMessageError
	if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
		log.Printf("%sFailed to decode LensMonitorMessageError: %v", ErrorLogPrefix, err)
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	log.Printf("%sAST error on point %d: %v", ErrorLogPrefix, msg.PointID, msg.Message)

	w.WriteHeader(http.StatusOK)
}
