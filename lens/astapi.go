package lens

const (
	lensMonitorEndpointPathError = "/ast.0/event/error"
	lensMonitorEndpointPathPoint = "/ast.0/point/point"
	lensMonitorEndpointPathState = "/ast.0/point/state"
	lensMonitorEndpointPathPanic = "/ast.0/point/panic"
)

// lensMonitorMaxStackFrames is the maximum number of stack frames captured by the client
// and accepted by the server. This is a safety limit to prevent OOM from malformed data.
const lensMonitorMaxStackFrames = 2048

// LensMonitorStackFrame holds a single frame in the call stack.
type LensMonitorStackFrame struct {
	File     string // source file path
	Function string // function name
	Line     uint
}

// Binary encoding type tags for wire protocol.
// The Value field in LensMonitorField can only contain these normalized types.
const (
	// Primitives (0x00-0x1F) - value only, no children
	lensTagNil        byte = 0x00 // nothing follows
	lensTagBool       byte = 0x01 // 1 byte: 0=false, 1=true
	lensTagInt32      byte = 0x02 // zigzag varint
	lensTagInt64      byte = 0x03 // zigzag varint
	lensTagUint32     byte = 0x04 // varint
	lensTagUint64     byte = 0x05 // varint
	lensTagFloat32    byte = 0x06 // 4 bytes little-endian IEEE 754
	lensTagFloat64    byte = 0x07 // 8 bytes little-endian IEEE 754
	lensTagComplex128 byte = 0x08 // 16 bytes: real (float64) + imag (float64)
	lensTagString     byte = 0x09 // varint length + UTF-8 bytes

	// Slices (0x20-0x3F) - length + inline data, no children
	lensTagBoolSlice    byte = 0x20 // varint count + bool bytes
	lensTagBytes        byte = 0x21 // varint length + raw bytes
	lensTagInt32Slice   byte = 0x22 // varint count + zigzag varints
	lensTagInt64Slice   byte = 0x23 // varint count + zigzag varints
	lensTagUint32Slice  byte = 0x24 // varint count + varints
	lensTagUint64Slice  byte = 0x25 // varint count + varints
	lensTagFloat32Slice byte = 0x26 // varint count + float32s
	lensTagFloat64Slice byte = 0x27 // varint count + float64s
	lensTagStringSlice  byte = 0x28 // varint count + length-prefixed strings

	// Containers (0x40-0x5F) - children count + child fields
	lensTagMap    byte = 0x40 // varint count + child fields (key as name)
	lensTagStruct byte = 0x41 // varint count + child fields
	lensTagSlice  byte = 0x42 // varint count + child fields (index as name, for complex element types)
)
