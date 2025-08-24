package lens

const (
	lensMonitorEndpointPathError = "/ast.0/event/error"
	lensMonitorEndpointPathPoint = "/ast.0/point/point"
	lensMonitorEndpointPathState = "/ast.0/point/state"
	lensMonitorEndpointPathPanic = "/ast.0/point/panic"
)

// LensMonitorMessageError is sent when an unexpected error occurs to assist with debugging.
type LensMonitorMessageError struct {
	PointID int                     `json:"id,omitempty"` // instrumented point id (provided to client from AST)
	Message string                  `json:"msg"`
	Stack   []LensMonitorStackFrame `json:"stack"` // call stack frames
}

// LensMonitorMessagePointPanic is sent when a function has an unrecovered panic.
type LensMonitorMessagePointPanic struct {
	PointID int    `json:"id,omitempty"` // instrumented point id (provided to client from AST)
	TimeNS  int64  `json:"time"`         // nanoseconds since the process start
	Message string `json:"msg"`          // value from the panic recovery
}

// LensMonitorMessagePoint is sent at a specific point within the function (determined by the point id when added).
type LensMonitorMessagePoint struct {
	PointID int                     `json:"id"`    // instrumented point id (provided to client from AST)
	TimeNS  int64                   `json:"time"`  // nanoseconds since the process start
	Stack   []LensMonitorStackFrame `json:"stack"` // call stack frames
}

// LensMonitorMessagePointState is sent when you want the full field snapshot at a point within a function.
type LensMonitorMessagePointState struct {
	PointID int                     `json:"id"`     // instrumented point id (provided to client from AST)
	TimeNS  int64                   `json:"time"`   // nanoseconds since the process start
	Stack   []LensMonitorStackFrame `json:"stack"`  // call stack frames
	Fields  []LensMonitorField      `json:"fields"` // variables reachable within the function scope (parameters, local values, etc)
}

// LensMonitorStackFrame holds a single frame in the call stack.
type LensMonitorStackFrame struct {
	File     string `json:"fi"` // source file path
	Function string `json:"fu"` // function name
	Line     uint   `json:"l"`  // line number
}

// LensMonitorField represents a named value or nested composite.
type LensMonitorField struct {
	Name     string             `json:"n"` // field name or path
	Type     string             `json:"t"` // Go type specific
	Value    interface{}        `json:"v,omitempty"`
	Children []LensMonitorField `json:"c,omitempty"` // nested fields for structs, maps, etc
}
