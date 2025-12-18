package lens

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math"
	"net/http"
	"os"
	"reflect"
	"runtime"
	"sort"
	"strconv"
	"time"
	"unicode/utf8"
	"unsafe"
)

// constants for backend server address, these values will be filled in via AST injection.
const (
	lensMonitorServerHost      = "127.0.0.1"
	lensMonitorServerPort      = 8448
	lensMonitorFieldMaxRecurse = 100
	lensMonitorFieldMaxLen     = 1024
)

var (
	lensClientStartTime = time.Now()
	lensHttpClient      = &http.Client{
		Transport: http.DefaultTransport,
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			return errors.New("redirect not allowed")
		},
		Timeout: 10 * time.Second,
	}
	lensMonitorEndpointError string
	lensMonitorEndpointPoint string
	lensMonitorEndpointState string
	lensMonitorEndpointPanic string
)

func init() {
	port := lensMonitorServerPort
	if portOverride := os.Getenv("LENS_MONITOR_PORT"); portOverride != "" {
		parsedPort, err := strconv.Atoi(portOverride)
		if err != nil {
			panic("Invalid port in env: " + err.Error())
		}
		port = parsedPort
	}
	// serverURL is the base URL for messaging endpoints
	serverURL := fmt.Sprintf("http://%s:%d", lensMonitorServerHost, port)
	lensMonitorEndpointError = serverURL + lensMonitorEndpointPathError
	lensMonitorEndpointPoint = serverURL + lensMonitorEndpointPathPoint
	lensMonitorEndpointState = serverURL + lensMonitorEndpointPathState
	lensMonitorEndpointPanic = serverURL + lensMonitorEndpointPathPanic
}

// sendLensPointMessage sends a LensMonitorMessagePoint to the backend.
func sendLensPointMessage(id uint32) {
	stack := captureLensMonitorStack(3) // skip runtime.Callers, captureLensMonitorStack, this func

	var buf bytes.Buffer
	lensEncodeMessagePoint(&buf, id, time.Since(lensClientStartTime).Nanoseconds(), stack)
	postLensMonitorMessage(lensMonitorEndpointPoint, id, &buf)
}

func lensEncodeMessagePoint(w io.Writer, id uint32, timestamp int64, stack []lensMonitorStackFrame) {
	lw := &lensMsgEncoder{w: w}
	lw.writeVarint(uint64(id))
	lw.writeInt64(timestamp)
	lw.writeStackFrames(stack)
}

// lensMonitorFieldSnapshot is the only thing the injector needs to build for each
// visible identifier.  It purposely keeps metadata tiny and uses `any` for
// the value so the client owns all heavy work (reflection, truncation, etc.).
type lensMonitorFieldSnapshot struct {
	Name string      // field identifier or synthetic name ("ret0", "rec0", ...)
	Val  interface{} // the live value
}

// sendLensPointStateMessage sends a LensMonitorMessagePointState to the backend.
func sendLensPointStateMessage(id uint32, snaps ...lensMonitorFieldSnapshot) {
	// Filter nil snapshots first to get accurate count
	validSnaps := make([]lensMonitorFieldSnapshot, 0, len(snaps))
	for _, s := range snaps {
		if s.Name != "nil" {
			validSnaps = append(validSnaps, s)
		}
	}
	stack := captureLensMonitorStack(3) // skip runtime.Callers, captureLensMonitorStack, this func

	var buf bytes.Buffer
	lensEncodeMessagePointState(&buf, id,
		time.Since(lensClientStartTime).Nanoseconds(), stack, validSnaps)
	postLensMonitorMessage(lensMonitorEndpointState, id, &buf)
}

func lensEncodeMessagePointState(w io.Writer, id uint32, timestamp int64, stack []lensMonitorStackFrame, snaps []lensMonitorFieldSnapshot) {
	lw := &lensMsgEncoder{w: w}
	lw.writeVarint(uint64(id))
	lw.writeInt64(timestamp)
	lw.writeStackFrames(stack)
	lw.writeVarint(uint64(len(snaps)))
	for _, s := range snaps {
		lw.streamField(s.Name, reflect.ValueOf(s.Val), 0, nil, "")
	}
}

func limitLensMonitorStringSize(s string) string {
	if len(s) > lensMonitorFieldMaxLen {
		s = s[:lensMonitorFieldMaxLen] + "…(" + strconv.Itoa(len(s)-lensMonitorFieldMaxLen) + " more)"
	}
	return s
}

// sendLensPointRecoveryMessage sends a LensMonitorMessagePointPanic to the backend.
func sendLensPointRecoveryMessage(id uint32, r interface{}) {
	if r == nil {
		return
	}

	var buf bytes.Buffer
	lensEncodeMessagePointPanic(&buf, id, time.Since(lensClientStartTime).Nanoseconds(), r)
	postLensMonitorMessage(lensMonitorEndpointPanic, id, &buf)
}

func lensEncodeMessagePointPanic(w io.Writer, id uint32, timestamp int64, r interface{}) {
	lw := &lensMsgEncoder{w: w}
	lw.writeVarint(uint64(id))
	lw.writeInt64(timestamp)
	lw.writeString(fmt.Sprintf("%v", r))
}

func captureLensMonitorStack(skip int) []lensMonitorStackFrame {
	pcs := make([]uintptr, lensMonitorMaxStackFrames)
	n := runtime.Callers(skip, pcs)
	frames := runtime.CallersFrames(pcs[:n])
	stack := make([]lensMonitorStackFrame, 0, n)
	for {
		f, more := frames.Next()
		stack = append(stack, lensMonitorStackFrame{
			File:     f.File,
			Function: f.Function,
			Line:     uint(f.Line), // TODO - FUTURE - the line number may be unexpected due to AST modifications, before reporting to user we should update to reference the original positions
		})
		if !more {
			break
		}
	}
	return stack
}

// postLensMonitorMessage POSTs encoded binary data to endpoint, handling errors.
func postLensMonitorMessage(endpoint string, id uint32, body io.Reader) {
	r, err := lensHttpClient.Post(endpoint, "application/octet-stream", body)
	if err != nil {
		sendLensError(id, fmt.Errorf("POST to %s failed: %w", endpoint, err))
		return
	}
	defer func() { _ = r.Body.Close() }()
	if r.StatusCode >= 300 {
		sendLensError(id, fmt.Errorf("%s returned status %d", endpoint, r.StatusCode))
	}
}

// sendLensError sends an Error notification to the backend.
func sendLensError(id uint32, origErr error) {
	if origErr == nil {
		return
	}
	stack := captureLensMonitorStack(3) // skip runtime.Callers, captureLensMonitorStack, this func

	var buf bytes.Buffer
	lensEncodeMessageError(&buf, id, origErr, stack)

	// Note: cannot use postLensMonitorMessage to avoid infinite recursion on POST failure
	resp, err := lensHttpClient.Post(lensMonitorEndpointError, "application/octet-stream", &buf)
	if err != nil {
		fmt.Printf("POST LensMonitorMessageError failed: %v, original error: %v\n", err, origErr)
	} else {
		defer func() { _ = resp.Body.Close() }()
		if resp.StatusCode >= 300 {
			fmt.Printf("error endpoint returned status %d, original error: %v\n", resp.StatusCode, origErr)
		}
	}
}

func lensEncodeMessageError(w io.Writer, id uint32, origErr error, stack []lensMonitorStackFrame) {
	lw := &lensMsgEncoder{w: w}
	lw.writeVarint(uint64(id))
	lw.writeString(origErr.Error())
	lw.writeStackFrames(stack)
}

type lensMsgEncoder struct {
	w   io.Writer
	buf [10]byte // reused for all primitive writes
}

func (lw *lensMsgEncoder) writeStackFrames(frames []lensMonitorStackFrame) {
	lw.writeVarint(uint64(len(frames)))
	if len(frames) == 0 {
		return
	}

	// Build string table for file paths and function names
	stringTable := make([]string, 0, len(frames)*2)
	stringIndex := make(map[string]uint32, len(frames)*2)
	for i := range frames {
		if _, ok := stringIndex[frames[i].File]; !ok {
			stringIndex[frames[i].File] = uint32(len(stringTable))
			stringTable = append(stringTable, frames[i].File)
		}
		if _, ok := stringIndex[frames[i].Function]; !ok {
			stringIndex[frames[i].Function] = uint32(len(stringTable))
			stringTable = append(stringTable, frames[i].Function)
		}
	}

	// Write string table
	lw.writeVarint(uint64(len(stringTable)))
	for _, s := range stringTable {
		lw.writeString(s)
	}

	// Write frames using string indices
	for i := range frames {
		lw.writeVarint(uint64(stringIndex[frames[i].File]))
		lw.writeVarint(uint64(stringIndex[frames[i].Function]))
		lw.writeVarint(uint64(frames[i].Line))
	}
}

func (lw *lensMsgEncoder) streamField(name string, v reflect.Value, depth int, visited map[uintptr]string, parentPath string) {
	var valuePath string
	if parentPath == "" {
		valuePath = name
	} else {
		valuePath = parentPath + "." + name
	}

	// Write name first (always needed)
	lw.writeString(name)

	// Cycle detection for pointers BEFORE unwrapping
	// This catches self-referential pointers like n.Next = n
	if v.IsValid() && v.Kind() == reflect.Pointer && !v.IsNil() {
		if visited == nil {
			visited = make(map[uintptr]string)
		}
		addr := v.Pointer()
		if cycleName, ok := visited[addr]; ok {
			lw.writeString(v.Type().String())
			lw.writeByte(lensTypeTagString)
			lw.writeString("<cycle:" + cycleName + ">")
			return
		}
		visited[addr] = valuePath
	}

	// Unwrap interfaces and pointers
	for v.IsValid() && (v.Kind() == reflect.Interface || v.Kind() == reflect.Pointer) {
		if v.IsNil() {
			lw.writeString(v.Type().String())
			lw.writeByte(lensTypeTagNil)
			return
		}
		v = v.Elem()
	}
	if !v.IsValid() {
		lw.writeString("invalid")
		lw.writeByte(lensTypeTagNil)
		return
	} else if depth >= lensMonitorFieldMaxRecurse {
		lw.writeString(v.Type().String())
		lw.writeByte(lensTypeTagString)
		lw.writeString("<max-depth>")
		return
	}

	vKind := v.Kind()
	vType := v.Type()

	// Handle nil for pointer-like types
	if vKind == reflect.Pointer || vKind == reflect.Map || vKind == reflect.Slice ||
		vKind == reflect.Func || vKind == reflect.Chan || vKind == reflect.Interface {
		if v.IsNil() {
			lw.writeString(vType.String())
			lw.writeByte(lensTypeTagNil)
			return
		}
	}

	// Cycle detection
	if vKind == reflect.Pointer || vKind == reflect.Map || vKind == reflect.Slice ||
		vKind == reflect.Func || vKind == reflect.Chan {
		if visited == nil {
			visited = make(map[uintptr]string)
		}
		addr := v.Pointer()
		if cycleName, ok := visited[addr]; ok {
			lw.writeString(vType.String())
			lw.writeByte(lensTypeTagString)
			lw.writeString("<cycle:" + cycleName + ">")
			return
		}
		visited[addr] = valuePath
	}

	lw.writeString(vType.String())

	switch vKind {
	case reflect.Bool:
		lw.writeByte(lensTypeTagBool)
		if v.Bool() {
			lw.writeByte(1)
		} else {
			lw.writeByte(0)
		}

	case reflect.Int8, reflect.Int16, reflect.Int32:
		lw.writeByte(lensTypeTagInt32)
		lw.writeSignedVarint(v.Int())

	case reflect.Int, reflect.Int64:
		lw.writeByte(lensTypeTagInt64)
		lw.writeSignedVarint(v.Int())

	case reflect.Uint8, reflect.Uint16, reflect.Uint32:
		lw.writeByte(lensTypeTagUint32)
		lw.writeVarint(v.Uint())

	case reflect.Uint, reflect.Uint64, reflect.Uintptr:
		lw.writeByte(lensTypeTagUint64)
		lw.writeVarint(v.Uint())

	case reflect.Float32:
		lw.writeByte(lensTypeTagFloat32)
		lw.writeFloat32(float32(v.Float()))

	case reflect.Float64:
		lw.writeByte(lensTypeTagFloat64)
		lw.writeFloat64(v.Float())

	case reflect.Complex64, reflect.Complex128:
		lw.writeByte(lensTypeTagComplex128)
		c := v.Complex()
		lw.writeFloat64(real(c))
		lw.writeFloat64(imag(c))

	case reflect.String:
		lw.writeByte(lensTypeTagString)
		lw.writeString(limitLensMonitorStringSize(v.String()))

	case reflect.Slice, reflect.Array:
		lw.streamValueSlice(v, vType, depth, visited, valuePath)

	case reflect.Map:
		lw.writeByte(lensTypeTagMap)
		keys := v.MapKeys()
		if len(keys) <= lensMonitorFieldMaxLen {
			// Fast path, size within limit, use undeterministic iteration order
			lw.writeVarint(uint64(len(keys)))
			for _, k := range keys {
				lw.streamField(fmt.Sprint(k.Interface()), v.MapIndex(k), depth+1, visited, valuePath)
			}
		} else { // Too many entries, sort keys for deterministic subset (similar to slices)
			sort.Slice(keys, func(i, j int) bool { return lensCompareReflectValue(keys[i], keys[j]) < 0 })
			lw.writeVarint(uint64(lensMonitorFieldMaxLen))
			for i := 0; i < lensMonitorFieldMaxLen; i++ {
				k := keys[i]
				lw.streamField(fmt.Sprint(k.Interface()), v.MapIndex(k), depth+1, visited, valuePath)
			}
		}

	case reflect.Struct:
		// Make addressable if needed for unexported field access
		if !v.CanAddr() {
			tmp := reflect.New(vType).Elem()
			tmp.Set(v)
			v = tmp
		}
		numFields := v.NumField()
		lw.writeByte(lensTypeTagStruct)
		lw.writeVarint(uint64(numFields))
		for i := 0; i < numFields; i++ {
			sf := vType.Field(i)
			fv := v.Field(i)
			if !fv.CanInterface() {
				fv = reflect.NewAt(fv.Type(), unsafe.Pointer(fv.UnsafeAddr())).Elem()
			}
			lw.streamField(sf.Name, fv, depth+1, visited, valuePath)
		}

	case reflect.Func:
		lw.writeByte(lensTypeTagString)
		lw.writeString("<func>")

	case reflect.Chan:
		lw.writeByte(lensTypeTagString)
		lw.writeString("<chan>")

	default:
		lw.writeByte(lensTypeTagString)
		lw.writeString(limitLensMonitorStringSize(fmt.Sprint(v.Interface())))
	}
}

// streamValueSlice handles slice/array encoding with optimized paths for primitive element types.
func (lw *lensMsgEncoder) streamValueSlice(v reflect.Value, vType reflect.Type, depth int, visited map[uintptr]string, valuePath string) {
	length := v.Len()
	if length > lensMonitorFieldMaxLen {
		length = lensMonitorFieldMaxLen
	}

	elemKind := vType.Elem().Kind()

	switch elemKind {
	case reflect.Bool:
		vals := make([]bool, length)
		for i := 0; i < length; i++ {
			vals[i] = v.Index(i).Bool()
		}
		lw.writeByte(lensTypeTagBoolSlice)
		lw.writeVarint(uint64(len(vals)))
		for i := 0; i < len(vals); i += 8 {
			var b byte
			for j := 0; j < 8 && i+j < len(vals); j++ {
				if vals[i+j] {
					b |= 1 << j
				}
			}
			lw.writeByte(b)
		}

	case reflect.Int8, reflect.Int16, reflect.Int32:
		lw.writeByte(lensTypeTagInt32Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeSignedVarint(v.Index(i).Int())
		}

	case reflect.Int, reflect.Int64:
		lw.writeByte(lensTypeTagInt64Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeSignedVarint(v.Index(i).Int())
		}

	case reflect.Uint8:
		var data []byte
		if v.Kind() == reflect.Slice {
			data = v.Bytes()
			if len(data) > lensMonitorFieldMaxLen {
				data = data[:lensMonitorFieldMaxLen]
			}
		} else {
			data = make([]byte, length)
			for i := 0; i < length; i++ {
				data[i] = byte(v.Index(i).Uint())
			}
		}
		if utf8.Valid(data) {
			lw.writeByte(lensTypeTagString)
			lw.writeString(limitLensMonitorStringSize(string(data)))
		} else {
			lw.writeByte(lensTypeTagBytes)
			lw.writeVarint(uint64(len(data)))
			_, _ = lw.w.Write(data)
		}

	case reflect.Uint16, reflect.Uint32:
		lw.writeByte(lensTypeTagUint32Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeVarint(v.Index(i).Uint())
		}

	case reflect.Uint, reflect.Uint64, reflect.Uintptr:
		lw.writeByte(lensTypeTagUint64Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeVarint(v.Index(i).Uint())
		}

	case reflect.Float32:
		lw.writeByte(lensTypeTagFloat32Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeFloat32(float32(v.Index(i).Float()))
		}

	case reflect.Float64:
		lw.writeByte(lensTypeTagFloat64Slice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeFloat64(v.Index(i).Float())
		}

	case reflect.String:
		lw.writeByte(lensTypeTagStringSlice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.writeString(limitLensMonitorStringSize(v.Index(i).String()))
		}

	default:
		lw.writeByte(lensTypeTagSlice)
		lw.writeVarint(uint64(length))
		for i := 0; i < length; i++ {
			lw.streamField("["+strconv.Itoa(i)+"]", v.Index(i), depth+1, visited, valuePath)
		}
	}
}

// lensCompareReflectValue compares two reflect.Value keys for sorting.
// Keys in a map are guaranteed to be the same type, so we switch on kind once.
func lensCompareReflectValue(a, b reflect.Value) int {
	switch a.Kind() {
	case reflect.String:
		as, bs := a.String(), b.String()
		if as < bs {
			return -1
		} else if as > bs {
			return 1
		}
		return 0
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		ai, bi := a.Int(), b.Int()
		if ai < bi {
			return -1
		} else if ai > bi {
			return 1
		}
		return 0
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		au, bu := a.Uint(), b.Uint()
		if au < bu {
			return -1
		} else if au > bu {
			return 1
		}
		return 0
	case reflect.Float32, reflect.Float64:
		af, bf := a.Float(), b.Float()
		if af < bf {
			return -1
		} else if af > bf {
			return 1
		}
		return 0
	case reflect.Bool:
		// false < true
		if a.Bool() == b.Bool() {
			return 0
		} else if b.Bool() {
			return -1
		}
		return 1
	case reflect.Complex64, reflect.Complex128:
		// Compare real part first, then imaginary
		ac, bc := a.Complex(), b.Complex()
		ar, br := real(ac), real(bc)
		if ar < br {
			return -1
		} else if ar > br {
			return 1
		}
		ai, bi := imag(ac), imag(bc)
		if ai < bi {
			return -1
		} else if ai > bi {
			return 1
		}
		return 0
	case reflect.Pointer, reflect.UnsafePointer:
		ap, bp := a.Pointer(), b.Pointer()
		if ap < bp {
			return -1
		} else if ap > bp {
			return 1
		}
		return 0
	case reflect.Array:
		// Compare element by element
		for i := 0; i < a.Len(); i++ {
			if c := lensCompareReflectValue(a.Index(i), b.Index(i)); c != 0 {
				return c
			}
		}
		return 0
	case reflect.Struct:
		// Compare field by field
		for i := 0; i < a.NumField(); i++ {
			if c := lensCompareReflectValue(a.Field(i), b.Field(i)); c != 0 {
				return c
			}
		}
		return 0
	case reflect.Interface:
		// Unwrap and compare underlying values
		if a.IsNil() && b.IsNil() {
			return 0
		} else if a.IsNil() {
			return -1
		} else if b.IsNil() {
			return 1
		}
		// Different underlying types: compare by type name for consistent ordering
		if a.Elem().Type() != b.Elem().Type() {
			at, bt := a.Elem().Type().String(), b.Elem().Type().String()
			if at < bt {
				return -1
			} else if at > bt {
				return 1
			}
			return 0
		}
		return lensCompareReflectValue(a.Elem(), b.Elem())
	case reflect.Chan:
		ap, bp := a.Pointer(), b.Pointer()
		if ap < bp {
			return -1
		} else if ap > bp {
			return 1
		}
		return 0
	default:
		// Fallback for any remaining types: compare string representation
		as, bs := fmt.Sprint(a.Interface()), fmt.Sprint(b.Interface())
		if as < bs {
			return -1
		} else if as > bs {
			return 1
		}
		return 0
	}
}

func (lw *lensMsgEncoder) writeByte(b byte) {
	lw.buf[0] = b
	_, _ = lw.w.Write(lw.buf[:1])
}

func (lw *lensMsgEncoder) writeInt64(v int64) {
	b := lw.buf[:8]
	binary.LittleEndian.PutUint64(b, uint64(v))
	_, _ = lw.w.Write(b)
}

// writeVarint writes a uint64 using variable-length encoding (7 bits per byte, high bit = continuation)
func (lw *lensMsgEncoder) writeVarint(v uint64) {
	var i int
	for v >= 0x80 {
		lw.buf[i] = byte(v) | 0x80
		v >>= 7
		i++
	}
	lw.buf[i] = byte(v)
	_, _ = lw.w.Write(lw.buf[:i+1])
}

// writeSignedVarint writes a signed int64 using zigzag encoding then varint.
func (lw *lensMsgEncoder) writeSignedVarint(v int64) {
	// Zigzag encode: map signed to unsigned (0, -1, 1, -2, 2, ... -> 0, 1, 2, 3, 4, ...)
	lw.writeVarint(uint64(v<<1) ^ uint64(v>>63))
}

func (lw *lensMsgEncoder) writeFloat32(v float32) {
	b := lw.buf[:4]
	binary.LittleEndian.PutUint32(b, math.Float32bits(v))
	_, _ = lw.w.Write(b)
}

func (lw *lensMsgEncoder) writeFloat64(v float64) {
	b := lw.buf[:8]
	binary.LittleEndian.PutUint64(b, math.Float64bits(v))
	_, _ = lw.w.Write(b)
}

func (lw *lensMsgEncoder) writeString(s string) {
	lw.writeVarint(uint64(len(s)))
	_, _ = io.WriteString(lw.w, s)
}
