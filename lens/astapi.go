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
	lensTypeTagNil        byte = 0x00 // nothing follows
	lensTypeTagBool       byte = 0x01 // 1 byte: 0=false, 1=true
	lensTypeTagInt32      byte = 0x02 // zigzag varint
	lensTypeTagInt64      byte = 0x03 // zigzag varint
	lensTypeTagUint32     byte = 0x04 // varint
	lensTypeTagUint64     byte = 0x05 // varint
	lensTypeTagFloat32    byte = 0x06 // 4 bytes little-endian IEEE 754
	lensTypeTagFloat64    byte = 0x07 // 8 bytes little-endian IEEE 754
	lensTypeTagComplex128 byte = 0x08 // 16 bytes: real (float64) + imag (float64)
	lensTypeTagString     byte = 0x09 // varint length + UTF-8 bytes

	// Slices (0x20-0x3F) - length + inline data, no children
	lensTypeTagBoolSlice    byte = 0x20 // varint count + bool bytes
	lensTypeTagBytes        byte = 0x21 // varint length + raw bytes
	lensTypeTagInt32Slice   byte = 0x22 // varint count + zigzag varints
	lensTypeTagInt64Slice   byte = 0x23 // varint count + zigzag varints
	lensTypeTagUint32Slice  byte = 0x24 // varint count + varints
	lensTypeTagUint64Slice  byte = 0x25 // varint count + varints
	lensTypeTagFloat32Slice byte = 0x26 // varint count + float32s
	lensTypeTagFloat64Slice byte = 0x27 // varint count + float64s
	lensTypeTagStringSlice  byte = 0x28 // varint count + length-prefixed strings

	// Containers (0x40-0x5F) - children count + child fields
	lensTypeTagMap    byte = 0x40 // varint count + child fields (key as name)
	lensTypeTagStruct byte = 0x41 // varint count + child fields
	lensTypeTagSlice  byte = 0x42 // varint count + child fields (index as name, for complex element types)
)
