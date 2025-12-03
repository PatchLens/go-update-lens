package lens

import (
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"
)

type astPointHandler interface {
	HandleFuncPoint(LensMonitorMessagePoint)
	HandleFuncPointState(LensMonitorMessagePointState)
	HandleFuncPointPanic(LensMonitorMessagePointPanic)
}

// LensMonitorMessageError is sent when an unexpected error occurs to assist with debugging.
type LensMonitorMessageError struct {
	PointID uint32 // instrumented point id (provided to client from AST)
	Message string
	Stack   []LensMonitorStackFrame // call stack frames
}

// LensMonitorMessagePointPanic is sent when a function has an unrecovered panic.
type LensMonitorMessagePointPanic struct {
	PointID uint32 // instrumented point id (provided to client from AST)
	TimeNS  int64  // nanoseconds since the process start
	Message string // value from the panic recovery
}

// LensMonitorMessagePoint is sent at a specific point within the function (determined by the point id when added).
type LensMonitorMessagePoint struct {
	PointID uint32                  // instrumented point id (provided to client from AST)
	TimeNS  int64                   // nanoseconds since the process start
	Stack   []LensMonitorStackFrame // call stack frames
}

// LensMonitorMessagePointState is sent when you want the full field snapshot at a point within a function.
type LensMonitorMessagePointState struct {
	PointID uint32                  // instrumented point id (provided to client from AST)
	TimeNS  int64                   // nanoseconds since the process start
	Stack   []LensMonitorStackFrame // call stack frames
	Fields  []LensMonitorField      // variables reachable within the function scope (parameters, local values, etc)
}

// LensMonitorField represents a named value or nested composite.
type LensMonitorField struct {
	Name     string // field name or path
	Type     string // Go type specific
	Value    interface{}
	Children []LensMonitorField // nested fields for structs, maps, etc
}

// astServer wraps the HTTP server for receiving client messages.
type astServer struct {
	server       *http.Server
	err          atomic.Pointer[error]
	pointHandler atomic.Value
	maxFieldLen  int // maximum length for strings and slices during decode
}

func (s *astServer) Port() int {
	_, portStr, _ := strings.Cut(s.server.Addr, ":")
	port, _ := strconv.Atoi(portStr)
	return port
}

// astExecServerStart constructs a astServer listening on host:port. Message handler functions are provided so that
// AST events can be evaluated as they occur rather than needing to retain everything for later analysis.
// The maxFieldLen parameter limits the maximum length of strings and slices during message decoding.
func astExecServerStart(host string, port int, pointHandler astPointHandler, maxFieldLen int) (*astServer, error) {
	addr := fmt.Sprintf("%s:%d", host, port)
	mux := http.NewServeMux()
	s := &astServer{maxFieldLen: maxFieldLen}
	s.pointHandler.Store(&pointHandler)
	mux.HandleFunc(lensMonitorEndpointPathError, s.handleEventError)
	mux.HandleFunc(lensMonitorEndpointPathPoint, s.handlePoint)
	mux.HandleFunc(lensMonitorEndpointPathState, s.handlePointState)
	mux.HandleFunc(lensMonitorEndpointPathPanic, s.handlePointPanic)
	s.server = &http.Server{Addr: addr, Handler: mux}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		wg.Done() // signal that routine has started
		if err := s.server.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			s.err.Store(&err)
			log.Printf("%sAST Monitor Server error: %v", ErrorLogPrefix, err)
		}
	}()
	wg.Wait()
	time.Sleep(100 * time.Millisecond) // short wait to ensure error is communicated

	return s, s.errCheck()
}

func (s *astServer) errCheck() error {
	if errPtr := s.err.Load(); errPtr != nil {
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
	defer func() { _ = r.Body.Close() }()

	msg, err := newLensReader(r.Body, s.maxFieldLen).decodeMessagePoint()
	if err != nil {
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
	defer func() { _ = r.Body.Close() }()

	msg, err := newLensReader(r.Body, s.maxFieldLen).decodeMessagePointState()
	if err != nil {
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
	defer func() { _ = r.Body.Close() }()

	msg, err := newLensReader(r.Body, s.maxFieldLen).decodeMessagePointPanic()
	if err != nil {
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
	defer func() { _ = r.Body.Close() }()

	msg, err := newLensReader(r.Body, s.maxFieldLen).decodeMessageError()
	if err != nil {
		log.Printf("%sFailed to decode LensMonitorMessageError: %v", ErrorLogPrefix, err)
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	log.Printf("%sAST error on point %d: %v", ErrorLogPrefix, msg.PointID, msg.Message)

	w.WriteHeader(http.StatusOK)
}

type lensReader struct {
	r           io.Reader
	buf         [8]byte // reused for all primitive reads
	maxFieldLen int     // maximum length for strings and slices
}

func newLensReader(r io.Reader, maxFieldLen int) *lensReader {
	return &lensReader{r: r, maxFieldLen: maxFieldLen}
}

func (lr *lensReader) decodeMessagePoint() (LensMonitorMessagePoint, error) {
	msg := LensMonitorMessagePoint{}
	point, err := lr.readVarint()
	if err != nil {
		return msg, err
	}
	msg.PointID = uint32(point)
	if msg.TimeNS, err = lr.readInt64(); err != nil {
		return msg, err
	} else if msg.Stack, err = lr.readStackFrames(); err != nil {
		return msg, err
	}
	return msg, nil
}

func (lr *lensReader) decodeMessagePointState() (LensMonitorMessagePointState, error) {
	msg := LensMonitorMessagePointState{}
	point, err := lr.readVarint()
	if err != nil {
		return msg, err
	}
	msg.PointID = uint32(point)
	if msg.TimeNS, err = lr.readInt64(); err != nil {
		return msg, err
	} else if msg.Stack, err = lr.readStackFrames(); err != nil {
		return msg, err
	} else if msg.Fields, err = lr.readFields(); err != nil {
		return msg, err
	}
	return msg, nil
}

func (lr *lensReader) decodeMessagePointPanic() (LensMonitorMessagePointPanic, error) {
	msg := LensMonitorMessagePointPanic{}
	point, err := lr.readVarint()
	if err != nil {
		return msg, err
	}
	msg.PointID = uint32(point)
	if msg.TimeNS, err = lr.readInt64(); err != nil {
		return msg, err
	} else if msg.Message, err = lr.readString(); err != nil {
		return msg, err
	}
	return msg, nil
}

func (lr *lensReader) decodeMessageError() (LensMonitorMessageError, error) {
	msg := LensMonitorMessageError{}
	point, err := lr.readVarint()
	if err != nil {
		return msg, err
	}
	msg.PointID = uint32(point)
	if msg.Message, err = lr.readString(); err != nil {
		return msg, err
	} else if msg.Stack, err = lr.readStackFrames(); err != nil {
		return msg, err
	}
	return msg, nil
}

func (lr *lensReader) readStackFrames() ([]LensMonitorStackFrame, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lensMonitorMaxStackFrames) {
		return nil, fmt.Errorf("stack frame count %d exceeds maximum %d", count, lensMonitorMaxStackFrames)
	} else if count == 0 {
		return nil, nil
	}

	// Read string table
	tableSize, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if tableSize > count*2 {
		return nil, fmt.Errorf("string table size %d exceeds maximum %d", tableSize, count*2)
	}
	stringTable := make([]string, tableSize)
	for i := uint64(0); i < tableSize; i++ {
		if stringTable[i], err = lr.readStringUnbounded(); err != nil {
			return nil, err
		}
	}

	// Read frames using string indices
	frames := make([]LensMonitorStackFrame, count)
	for i := uint64(0); i < count; i++ {
		fileIdx, err := lr.readVarint()
		if err != nil {
			return nil, err
		} else if fileIdx >= tableSize {
			return nil, fmt.Errorf("file index %d out of range", fileIdx)
		}
		funcIdx, err := lr.readVarint()
		if err != nil {
			return nil, err
		} else if funcIdx >= tableSize {
			return nil, fmt.Errorf("function index %d out of range", funcIdx)
		}
		line, err := lr.readVarint()
		if err != nil {
			return nil, err
		}
		frames[i].File = stringTable[fileIdx]
		frames[i].Function = stringTable[funcIdx]
		frames[i].Line = uint(line)
	}
	return frames, nil
}

func (lr *lensReader) readFields() ([]LensMonitorField, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > math.MaxUint32 {
		return nil, fmt.Errorf("field count %d exceeds maximum", count)
	}
	fields := make([]LensMonitorField, count)
	for i := uint64(0); i < count; i++ {
		if err := lr.readField(&fields[i]); err != nil {
			return nil, err
		}
	}
	return fields, nil
}

func (lr *lensReader) readField(f *LensMonitorField) error {
	var err error
	if f.Name, err = lr.readString(); err != nil {
		return err
	} else if f.Type, err = lr.readString(); err != nil {
		return err
	} else if f.Value, f.Children, err = lr.readValue(); err != nil {
		return err
	}
	return nil
}

// readValue reads a typed value from the stream.
// Returns (value, nil, nil) for primitives/slices, or (nil, children, nil) for containers.
func (lr *lensReader) readValue() (interface{}, []LensMonitorField, error) {
	tag, err := lr.readByte()
	if err != nil {
		return nil, nil, err
	}

	switch tag {
	case lensTypeTagNil:
		return nil, nil, nil
	case lensTypeTagBool:
		b, err := lr.readByte()
		if err != nil {
			return nil, nil, err
		}
		return b != 0, nil, nil
	case lensTypeTagInt32:
		v, err := lr.readSignedVarint()
		return int32(v), nil, err
	case lensTypeTagInt64:
		v, err := lr.readSignedVarint()
		return v, nil, err
	case lensTypeTagUint32:
		v, err := lr.readVarint()
		return uint32(v), nil, err
	case lensTypeTagUint64:
		v, err := lr.readVarint()
		return v, nil, err
	case lensTypeTagFloat32:
		v, err := lr.readFloat32()
		return v, nil, err
	case lensTypeTagFloat64:
		v, err := lr.readFloat64()
		return v, nil, err
	case lensTypeTagComplex128:
		re, err := lr.readFloat64()
		if err != nil {
			return nil, nil, err
		}
		im, err := lr.readFloat64()
		if err != nil {
			return nil, nil, err
		}
		return complex(re, im), nil, nil
	case lensTypeTagString:
		v, err := lr.readString()
		return v, nil, err
	case lensTypeTagBoolSlice:
		v, err := lr.readBoolSlice()
		return v, nil, err
	case lensTypeTagBytes:
		v, err := lr.readBytes()
		return v, nil, err
	case lensTypeTagInt32Slice:
		v, err := lr.readInt32Slice()
		return v, nil, err
	case lensTypeTagInt64Slice:
		v, err := lr.readInt64Slice()
		return v, nil, err
	case lensTypeTagUint32Slice:
		v, err := lr.readUint32Slice()
		return v, nil, err
	case lensTypeTagUint64Slice:
		v, err := lr.readUint64Slice()
		return v, nil, err
	case lensTypeTagFloat32Slice:
		v, err := lr.readFloat32Slice()
		return v, nil, err
	case lensTypeTagFloat64Slice:
		v, err := lr.readFloat64Slice()
		return v, nil, err
	case lensTypeTagStringSlice:
		v, err := lr.readStringSlice()
		return v, nil, err
	case lensTypeTagSlice, lensTypeTagMap, lensTypeTagStruct:
		count, err := lr.readVarint()
		if err != nil {
			return nil, nil, err
		} else if count > uint64(lr.maxFieldLen) {
			return nil, nil, fmt.Errorf("container field count %d exceeds maximum %d", count, lr.maxFieldLen)
		}
		children := make([]LensMonitorField, count)
		for i := uint64(0); i < count; i++ {
			if err := lr.readField(&children[i]); err != nil {
				return nil, nil, err
			}
		}
		return nil, children, nil
	default:
		return nil, nil, fmt.Errorf("unknown value tag: %d (0x%02x)", tag, tag)
	}
}

// Primitive read methods using shared buffer
func (lr *lensReader) readByte() (byte, error) {
	if _, err := io.ReadFull(lr.r, lr.buf[:1]); err != nil {
		return 0, err
	}
	return lr.buf[0], nil
}

func (lr *lensReader) readInt64() (int64, error) {
	b := lr.buf[:8]
	if _, err := io.ReadFull(lr.r, b); err != nil {
		return 0, err
	}
	return int64(binary.LittleEndian.Uint64(b)), nil
}

// readVarint reads a variable-length encoded uint64 (7 bits per byte, high bit = continuation).
func (lr *lensReader) readVarint() (uint64, error) {
	var v uint64
	var shift uint
	for {
		b, err := lr.readByte()
		if err != nil {
			return 0, err
		}
		v |= uint64(b&0x7F) << shift
		if b < 0x80 {
			break
		}
		shift += 7
		if shift >= 64 {
			return 0, errors.New("varint overflow")
		}
	}
	return v, nil
}

// readSignedVarint reads a zigzag-encoded signed int64.
func (lr *lensReader) readSignedVarint() (int64, error) {
	v, err := lr.readVarint()
	if err != nil {
		return 0, err
	}
	// Zigzag decode: (v >> 1) ^ -(v & 1)
	return int64(v>>1) ^ -int64(v&1), nil
}

func (lr *lensReader) readFloat32() (float32, error) {
	b := lr.buf[:4]
	if _, err := io.ReadFull(lr.r, b); err != nil {
		return 0, err
	}
	return math.Float32frombits(binary.LittleEndian.Uint32(b)), nil
}

func (lr *lensReader) readFloat64() (float64, error) {
	b := lr.buf[:8]
	if _, err := io.ReadFull(lr.r, b); err != nil {
		return 0, err
	}
	return math.Float64frombits(binary.LittleEndian.Uint64(b)), nil
}

func (lr *lensReader) readString() (string, error) {
	length, err := lr.readVarint()
	if err != nil || length == 0 {
		return "", err
	} else if length > uint64(lr.maxFieldLen) {
		return "", fmt.Errorf("string length %d exceeds maximum %d", length, lr.maxFieldLen)
	}
	buf := make([]byte, length)
	if _, err := io.ReadFull(lr.r, buf); err != nil {
		return "", err
	}
	// Zero-copy string conversion - safe because buf is not reused after this
	return unsafe.String(&buf[0], len(buf)), nil
}

func (lr *lensReader) readStringUnbounded() (string, error) {
	length, err := lr.readVarint()
	if err != nil || length == 0 {
		return "", err
	} else if length > math.MaxUint32 {
		return "", fmt.Errorf("string length %d exceeds maximum", length)
	}
	buf := make([]byte, length)
	if _, err := io.ReadFull(lr.r, buf); err != nil {
		return "", err
	}
	return unsafe.String(&buf[0], len(buf)), nil
}

func (lr *lensReader) readBytes() ([]byte, error) {
	length, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if length == 0 {
		return []byte{}, nil
	} else if length > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("bytes length %d exceeds maximum %d", length, lr.maxFieldLen)
	}
	buf := make([]byte, length)
	if _, err := io.ReadFull(lr.r, buf); err != nil {
		return nil, err
	}
	return buf, nil
}

func (lr *lensReader) readBoolSlice() ([]bool, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("bool slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	} else if count == 0 {
		return []bool{}, nil
	}
	slice := make([]bool, count)
	// packed 8 bool per byte
	byteCount := (count + 7) / 8
	for byteIdx := uint64(0); byteIdx < byteCount; byteIdx++ {
		b, err := lr.readByte()
		if err != nil {
			return nil, err
		}
		for bitIdx := uint64(0); bitIdx < 8 && byteIdx*8+bitIdx < count; bitIdx++ {
			slice[byteIdx*8+bitIdx] = (b & (1 << bitIdx)) != 0
		}
	}
	return slice, nil
}

func (lr *lensReader) readInt32Slice() ([]int32, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("int32 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	} else if count == 0 {
		return []int32{}, nil
	}
	slice := make([]int32, count)
	for i := uint64(0); i < count; i++ {
		v, err := lr.readSignedVarint()
		if err != nil {
			return nil, err
		}
		slice[i] = int32(v)
	}
	return slice, nil
}

func (lr *lensReader) readInt64Slice() ([]int64, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count == 0 {
		return []int64{}, nil
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("int64 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	}
	slice := make([]int64, count)
	for i := uint64(0); i < count; i++ {
		if slice[i], err = lr.readSignedVarint(); err != nil {
			return nil, err
		}
	}
	return slice, nil
}

func (lr *lensReader) readUint32Slice() ([]uint32, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("uint32 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	} else if count == 0 {
		return []uint32{}, nil
	}
	slice := make([]uint32, count)
	for i := uint64(0); i < count; i++ {
		v, err := lr.readVarint()
		if err != nil {
			return nil, err
		}
		slice[i] = uint32(v)
	}
	return slice, nil
}

func (lr *lensReader) readUint64Slice() ([]uint64, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("uint64 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	} else if count == 0 {
		return []uint64{}, nil
	}
	slice := make([]uint64, count)
	for i := uint64(0); i < count; i++ {
		if slice[i], err = lr.readVarint(); err != nil {
			return nil, err
		}
	}
	return slice, nil
}

func (lr *lensReader) readFloat32Slice() ([]float32, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("float32 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	} else if count == 0 {
		return []float32{}, nil
	}
	slice := make([]float32, count)
	for i := uint64(0); i < count; i++ {
		if slice[i], err = lr.readFloat32(); err != nil {
			return nil, err
		}
	}
	return slice, nil
}

func (lr *lensReader) readFloat64Slice() ([]float64, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count == 0 {
		return []float64{}, nil
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("float64 slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	}
	slice := make([]float64, count)
	for i := uint64(0); i < count; i++ {
		if slice[i], err = lr.readFloat64(); err != nil {
			return nil, err
		}
	}
	return slice, nil
}

func (lr *lensReader) readStringSlice() ([]string, error) {
	count, err := lr.readVarint()
	if err != nil {
		return nil, err
	} else if count == 0 {
		return []string{}, nil
	} else if count > uint64(lr.maxFieldLen) {
		return nil, fmt.Errorf("string slice length %d exceeds maximum %d", count, lr.maxFieldLen)
	}
	slice := make([]string, count)
	for i := uint64(0); i < count; i++ {
		if slice[i], err = lr.readString(); err != nil {
			return nil, err
		}
	}
	return slice, nil
}
