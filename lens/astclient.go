package lens

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"net/http"
	"os"
	"reflect"
	"runtime"
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

// Special float value representations for JSON marshaling
const (
	floatValueNaN  = "NaN"
	floatValuePInf = "+Inf"
	floatValueNInf = "-Inf"
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

// SendLensPointMessage sends a LensMonitorMessagePoint to the backend.
func SendLensPointMessage(id int) {
	em := LensMonitorMessagePoint{
		PointID: id,
		TimeNS:  time.Since(lensClientStartTime).Nanoseconds(),
	}
	em.Stack = captureLensMonitorStack(3) // skip runtime.Callers, captureLensMonitorStack, and SendEntryMessage

	postLensMonitorMessage(lensMonitorEndpointPoint, id, em)
}

// LensMonitorFieldSnapshot is the only thing the injector needs to build for each
// visible identifier.  It purposely keeps metadata tiny and uses `any` for
// the value so the client owns all heavy work (reflection, truncation, etc.).
type LensMonitorFieldSnapshot struct {
	Name string      // field identifier or synthetic name ("ret0", "rec0", ...)
	Val  interface{} // the live value
}

// SendLensPointStateMessage sends a LensMonitorMessagePointState to the backend.
func SendLensPointStateMessage(id int, snaps ...LensMonitorFieldSnapshot) {
	sm := LensMonitorMessagePointState{
		PointID: id,
		TimeNS:  time.Since(lensClientStartTime).Nanoseconds(),
		Stack:   captureLensMonitorStack(3), // skip Callers, captureLensMonitorStack, SendLensPointStateMessage
	}

	for _, s := range snaps {
		if s.Name == "nil" {
			continue
		}
		sf := LensMonitorField{
			Name: s.Name,
		}
		buildLensMonitorField("", &sf, reflect.ValueOf(s.Val), 0, make(map[uintptr]string))
		sm.Fields = append(sm.Fields, sf)
	}

	postLensMonitorMessage(lensMonitorEndpointState, id, sm)
}

func buildLensMonitorField(parentPath string, dst *LensMonitorField, v reflect.Value, depth int, visited map[uintptr]string) {
	var valuePath string
	if parentPath == "" {
		valuePath = dst.Name
	} else {
		valuePath = parentPath + "." + dst.Name
	}
	// unwrap and handle nil interface{} if discovered
	for v.IsValid() && (v.Kind() == reflect.Interface || v.Kind() == reflect.Pointer) {
		if v.IsNil() {
			// a nil interface: record its interface type, leave Value=nil
			dst.Type = v.Type().String()
			return
		}
		v = v.Elem() // otherwise unwrap one layer to the concrete value
	}
	if !v.IsValid() {
		dst.Type = "invalid"
		return
	} else if depth >= lensMonitorFieldMaxRecurse {
		dst.Type = v.Type().String()
		dst.Value = "<max-depth>"
		return
	}

	// handle explicit nils for remaining types
	vKind := v.Kind()
	vType := v.Type()
	if vKind == reflect.Pointer || vKind == reflect.Map || vKind == reflect.Slice ||
		vKind == reflect.Func || vKind == reflect.Chan || vKind == reflect.Interface {
		if v.IsNil() {
			dst.Type = vType.String()
			return
		}
	}

	// cycle detection: only for kinds that expose an addressable backing ptr
	if vKind == reflect.Pointer || vKind == reflect.Map || vKind == reflect.Slice ||
		vKind == reflect.Func || vKind == reflect.Chan {
		addr := v.Pointer()
		if name, ok := visited[addr]; ok {
			dst.Type = vType.String()
			dst.Value = fmt.Sprintf("<cycle:%s>", name)
			return
		}
		visited[addr] = valuePath
	}

	dst.Type = vType.String()

	// leaf / composite handling
	switch v.Kind() {
	case reflect.Bool:
		dst.Value = v.Bool()
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		dst.Value = v.Int()
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		dst.Value = v.Uint()
	case reflect.Float32, reflect.Float64:
		// JSON doesn't support NaN or Inf, convert to strings
		f := v.Float()
		if math.IsNaN(f) {
			dst.Value = floatValueNaN
		} else if math.IsInf(f, 1) {
			dst.Value = floatValuePInf
		} else if math.IsInf(f, -1) {
			dst.Value = floatValueNInf
		} else {
			dst.Value = f
		}
	case reflect.String:
		dst.Value = limitLensMonitorStringSize(v.String())
	case reflect.Slice, reflect.Array:
		length := v.Len()
		if length > lensMonitorFieldMaxLen {
			length = lensMonitorFieldMaxLen
		}

		switch elemKind := vType.Elem().Kind(); elemKind {
		// for basic‐typed slices/arrays, emit a single concise value
		case reflect.Bool,
			reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
			reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
			reflect.Float32, reflect.Float64:
			if elemKind == reflect.Uint8 {
				if data := v.Bytes(); utf8.Valid(data) {
					// treat this as a string
					dst.Value = limitLensMonitorStringSize(string(data))
					return
				}
			}

			vals := make([]interface{}, length)
			for i := 0; i < length; i++ {
				val := v.Index(i).Interface()
				// Handle NaN/Inf in float slices to prevent JSON marshal errors
				if elemKind == reflect.Float32 || elemKind == reflect.Float64 {
					if f, ok := val.(float64); ok {
						if math.IsNaN(f) {
							val = floatValueNaN
						} else if math.IsInf(f, 1) {
							val = floatValuePInf
						} else if math.IsInf(f, -1) {
							val = floatValueNInf
						}
					} else if f32, ok := val.(float32); ok {
						f := float64(f32)
						if math.IsNaN(f) {
							val = floatValueNaN
						} else if math.IsInf(f, 1) {
							val = floatValuePInf
						} else if math.IsInf(f, -1) {
							val = floatValueNInf
						}
					}
				}
				vals[i] = val
			}
			dst.Value = vals
		case reflect.String:
			// Strings contain enough information that we are better to create children for each field
			for i := 0; i < length; i++ {
				child := LensMonitorField{
					Name:  "[" + strconv.Itoa(i) + "]",
					Type:  "string",
					Value: limitLensMonitorStringSize(v.Index(i).String()),
				}
				dst.Children = append(dst.Children, child)
			}
		default:
			// fallback: recurse into each element
			for i := 0; i < length; i++ {
				child := LensMonitorField{Name: "[" + strconv.Itoa(i) + "]"}
				buildLensMonitorField(valuePath, &child, v.Index(i), depth+1, visited)
				dst.Children = append(dst.Children, child)
			}
		}
	case reflect.Map:
		for _, k := range v.MapKeys() {
			child := LensMonitorField{Name: fmt.Sprint(k.Interface())}
			buildLensMonitorField(valuePath, &child, v.MapIndex(k), depth+1, visited)
			dst.Children = append(dst.Children, child)
		}
	case reflect.Struct:
		// if v itself is not addressable, copy it into an addressable temp
		if !v.CanAddr() {
			tmp := reflect.New(vType).Elem() // addressable zero of the same type
			tmp.Set(v)                       // copy the real value in
			v = tmp                          // now use tmp for all field work
		}

		for i := 0; i < v.NumField(); i++ {
			sf := vType.Field(i)
			child := LensMonitorField{Name: sf.Name}

			fv := v.Field(i)
			// if the field is unexported, break the barrier
			if !fv.CanInterface() {
				// get a pointer at the field's address and dereference
				fv = reflect.NewAt(fv.Type(), unsafe.Pointer(fv.UnsafeAddr())).Elem()
			}

			buildLensMonitorField(valuePath, &child, fv, depth+1, visited)
			dst.Children = append(dst.Children, child)
		}
		if len(dst.Children) == 0 { // if no children at all, fallback to fmt
			dst.Value = fmt.Sprint(v.Interface())
		}
	case reflect.Func:
		dst.Value = "<func>" // formatted function pointer is not valuable
	case reflect.Chan:
		dst.Value = "<chan>" // channel pointer is not useful
	default:
		// Fallback to fmt for anything else (complex, unsafe pointer)
		dst.Value = fmt.Sprint(v.Interface())
	}
}

func limitLensMonitorStringSize(s string) string {
	if len(s) > lensMonitorFieldMaxLen {
		s = s[:lensMonitorFieldMaxLen] + "…(" + strconv.Itoa(len(s)-lensMonitorFieldMaxLen) + " more)"
	}
	return s
}

// SendLensPointRecoveryMessage sends a LensMonitorMessagePointPanic to the backend.
func SendLensPointRecoveryMessage(id int, r interface{}) {
	if r == nil {
		return
	}
	sm := LensMonitorMessagePointPanic{
		PointID: id,
		TimeNS:  time.Since(lensClientStartTime).Nanoseconds(),
	}
	sm.Message = fmt.Sprintf("%v", r)

	postLensMonitorMessage(lensMonitorEndpointPanic, id, sm)
}

func captureLensMonitorStack(skip int) []LensMonitorStackFrame {
	pcs := make([]uintptr, 2048)
	n := runtime.Callers(skip, pcs)
	frames := runtime.CallersFrames(pcs[:n])
	var stack []LensMonitorStackFrame
	for {
		f, more := frames.Next()
		stack = append(stack, LensMonitorStackFrame{
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

// postLensMonitorMessage marshals payload and POSTs to endpoint, handling errors.
func postLensMonitorMessage(endpoint string, id int, payload interface{}) {
	data, err := json.Marshal(payload)
	if err != nil {
		SendLensError(id, fmt.Errorf("marshal %T failed: %w", payload, err))
		return
	}
	r, err := lensHttpClient.Post(endpoint, "application/json", bytes.NewReader(data))
	if err != nil {
		SendLensError(id, fmt.Errorf("POST %T failed: %w", payload, err))
		return
	}
	defer func() { _ = r.Body.Close() }()
	if r.StatusCode >= 300 {
		SendLensError(id, fmt.Errorf("%s returned status %d", endpoint, r.StatusCode))
	}
}

// SendLensError sends an Error notification to the backend.
func SendLensError(id int, origErr error) {
	if origErr == nil {
		return
	}

	data, err := json.Marshal(LensMonitorMessageError{
		PointID: id,
		Message: origErr.Error(),
		Stack:   captureLensMonitorStack(3), // skip runtime.Callers, captureLensMonitorStack, this func
	})
	if err != nil {
		fmt.Printf("marshal LensMonitorMessageError failed: %v, original error: %v\n", err, origErr)
	}
	resp, err := lensHttpClient.Post(lensMonitorEndpointError, "application/json", bytes.NewReader(data))
	if err != nil {
		fmt.Printf("POST LensMonitorMessageError failed: %v, original error: %v\n", err, origErr)
	} else {
		defer func() { _ = resp.Body.Close() }()
		if resp.StatusCode >= 300 {
			fmt.Printf("error endpoint returned status %d, original error: %v\n", resp.StatusCode, origErr)
		}
	}
}
