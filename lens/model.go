package lens

import (
	"bytes"
	"crypto/sha1"
	"fmt"
	"maps"
	"slices"
	"sort"
	"strconv"
	"strings"

	"github.com/vmihailenco/msgpack/v5"
)

// GeneratedTestFunctionPrefix is the prefix used for generated test functions
const GeneratedTestFunctionPrefix = "TestGen_"
const GeneratedTestFileSuffix = "_modlensgen_test.go"

// ModuleChange describes a Go module upgrade.
type ModuleChange struct {
	// Name is the module name.
	Name string
	// PriorVersion is the version before update.
	PriorVersion string
	// NewVersion is the version after update.
	NewVersion string
	// Indirect indicates the module is an indirect dependency.
	Indirect bool
}

// Function holds info about a function after static analysis.
type Function struct {
	// FilePath is the full path to the source file.
	FilePath string
	// PackageName is the package containing the function.
	PackageName string
	// FunctionIdent is the fully qualified identifier.
	FunctionIdent string
	// FunctionName is the short function name.
	FunctionName string
	// EntryLineNumber is the entry line.
	EntryLineNumber uint32
	// ReturnPoints lists source return locations.
	ReturnPoints []FunctionReturn
	// ReturnPanic reports if the function always panics.
	ReturnPanic bool
}

// FunctionReturn holds the return line and call count.
type FunctionReturn struct {
	// Line is the return line number.
	Line uint32
	// CallCount is the number of call expressions returned.
	CallCount uint32
}

// ShortIdent returns the function identifier without path.
func (f Function) ShortIdent() string {
	index := strings.LastIndex(f.FunctionIdent, "/")
	if index > 0 {
		return f.FunctionIdent[index+1:]
	}
	return f.FunctionIdent
}

// ModuleFunction represents the definition of a changed module function.
type ModuleFunction struct {
	Function

	// Definition contains the function's source code.
	Definition string
	// LineChangeBitmap marks changed lines starting at funcStart.
	LineChangeBitmap []bool
}

// ReachableModuleChange maps function identifiers to changed functions
type ReachableModuleChange map[string]*ModuleFunction

// CallerFunction ties a caller in the project to a changed function.
type CallerFunction struct {
	Function

	// ChangeFunctions lists changed functions invoked by this caller.
	ChangeFunctions []*ModuleFunction
}

// ChangeFunctionIdents returns short idents of invoked changes.
func (f CallerFunction) ChangeFunctionIdents() string {
	var sb strings.Builder
	for i := range f.ChangeFunctions {
		if i > 0 {
			sb.WriteString(", ")
		}
		sb.WriteString(f.ChangeFunctions[i].ShortIdent())
	}
	return sb.String()
}

// TestFunction ties a test function to a caller in the project to a changed function.
type TestFunction struct {
	Function

	// Targets lists callers tested by this function.
	Targets []*CallerFunction
}

// TargetFunctionIdents returns short idents of target callers.
func (f TestFunction) TargetFunctionIdents() string {
	var sb strings.Builder
	for i := range f.Targets {
		if i > 0 {
			sb.WriteString(", ")
		}
		sb.WriteString(f.Targets[i].ShortIdent())
	}
	return sb.String()
}

// Minimum returns the minimal test function info.
func (f TestFunction) Minimum() MinimumTestFunction {
	return MinimumTestFunction{
		FunctionIdent: f.FunctionIdent,
		FunctionName:  f.FunctionName,
	}
}

// MinimumTestFunction provides the minimum information about a test function to associate to the TestResult.
type MinimumTestFunction struct {
	// FunctionIdent is the fully qualified identifier.
	FunctionIdent string
	// FunctionName is the short name.
	FunctionName string
}

// TestResult represents the recorded field values per test function.
type TestResult struct {
	// TestFunction identifies the test.
	TestFunction MinimumTestFunction `msgpack:"tf"`
	// CallerResults maps callers to captured field values.
	CallerResults map[string][]CallFrame `msgpack:"cr"`
	// ProjectPanics records panic messages from project functions.
	ProjectPanics map[string][]string `msgpack:"pp"`
	// ModulePanics records panic messages from module functions.
	ModulePanics map[string][]string `msgpack:"mp"`
	// ModuleChangesHit counts the changed functions hit.
	ModuleChangesHit int `msgpack:"mh"`
	// TestFailure reports if the test failed.
	TestFailure bool `msgpack:"fail"`
}

// structs and code below to encode TestResult into a minimal (de-duplicated) encoding

type encFieldValue struct {
	Ni  *int           `msgpack:"ni,omitempty"` // -> FVNodeDict (if duplicate node)
	V   string         `msgpack:"v,omitempty"`  // scalar value
	Ci  *int           `msgpack:"ci,omitempty"` // -> FVDict   (if duplicate map)
	Cvl encFieldValues `msgpack:"c,omitempty"`  // inline children (if unique)
}
type encFieldValues map[string]encFieldValue

type encCallFrame struct {
	FVi *int           `msgpack:"fi,omitempty"` // -> FVDict
	FV  encFieldValues `msgpack:"f,omitempty"`  // inline FV map
	Si  *int           `msgpack:"si,omitempty"` // -> STDict
	St  []StackFrame   `msgpack:"s,omitempty"`  // inline stack
	T   uint32         `msgpack:"t"`            // time in milliseconds
}

type encTestResult struct {
	TestFunction     MinimumTestFunction       `msgpack:"tf"`
	CallerResults    map[string][]encCallFrame `msgpack:"cr"`
	ProjectPanics    map[string][]string       `msgpack:"pp,omitempty"`
	ModulePanics     map[string][]string       `msgpack:"mp,omitempty"`
	ModuleChangesHit int                       `msgpack:"mh"`
	TestFailure      bool                      `msgpack:"fail"`

	// ─── our two dictionaries ───
	FVDict     []encFieldValues `msgpack:"fh,omitempty"` // for repeated FieldValues maps
	FVNodeDict []encFieldValue  `msgpack:"nh,omitempty"` // for repeated FieldValue nodes
	STDict     [][]StackFrame   `msgpack:"sh,omitempty"` // for repeated stacks
}

func hasDup(freq map[string]int) bool {
	for _, n := range freq {
		if n > 1 {
			return true
		}
	}
	return false
}

func anyKey(a any) string {
	b, err := msgpack.Marshal(a)
	if err != nil {
		panic(err)
	}
	return bytesKey(b)
}

func (tr *TestResult) MarshalMsgpack() ([]byte, error) {
	enc := msgpack.GetEncoder()
	defer msgpack.PutEncoder(enc)
	return tr.marshalMsgpack(enc, &bytes.Buffer{})
}

func (tr *TestResult) marshalMsgpack(enc *msgpack.Encoder, buf *bytes.Buffer) ([]byte, error) {
	// count occurrences
	fvCount := make(map[string]int)  // FieldValues-map hashes
	fvnCount := make(map[string]int) // FieldValue-node hashes
	stCount := make(map[string]int)  // []StackFrame hashes
	var walkNode func(*FieldValue)
	walkFV := func(fv FieldValues) {
		fvCount[fv.ID()]++
		for _, v := range fv {
			walkNode(v)
		}
	}
	walkNode = func(n *FieldValue) {
		// Skip optimization for very small values with no children
		// The overhead of a dictionary reference (4-8 bytes) vs inline (len(value) + metadata)
		// becomes beneficial around 10+ bytes of value or any children
		if len(n.Children) == 0 && len(n.Value) <= 4 {
			return // value too small to optimize
		}
		fvnCount[n.ID()]++
		if len(n.Children) > 0 {
			walkFV(n.Children)
		}
	}
	for _, frames := range tr.CallerResults {
		for _, cf := range frames {
			walkFV(cf.FieldValues)
			stCount[anyKey(cf.Stack)]++
		}
	}

	// build dictionaries and encode
	var fvIndex, fvnIndex, stIndex map[string]int
	// map-level dictionary state
	if hasDup(fvCount) {
		fvIndex = make(map[string]int)
	}
	var fvDict []encFieldValues
	// node-level dictionary state
	if hasDup(fvnCount) {
		fvnIndex = make(map[string]int)
	}
	var fvnDict []encFieldValue
	// stack-level dictionary state
	if hasDup(stCount) {
		stIndex = make(map[string]int)
	}
	var stDict [][]StackFrame
	// encode a single FieldValue *node*, returning either:
	//   – an inline encFieldValue, or
	//   – an encFieldValue{Ni: &idx} pointing into fvnDict
	var encodeNode func(*FieldValue) (encFieldValue, *int)
	encodeFV := func(src FieldValues) (encFieldValues, *int) {
		if src == nil {
			return nil, nil
		}
		key := src.ID()
		// map-level dictionary?
		if fvIndex != nil && fvCount[key] > 1 {
			if pos, ok := fvIndex[key]; ok {
				return nil, &pos
			}
			pos := len(fvDict)
			fvIndex[key] = pos
			// Reserve the slot immediately to prevent conflicts
			fvDict = append(fvDict, nil)

			encMap := make(encFieldValues, len(src))
			for k, v := range src {
				ef, _ := encodeNode(v) // node-dict or inline
				encMap[k] = ef
			}
			// Fill the reserved slot
			fvDict[pos] = encMap
			return nil, &pos
		}

		// inline map
		out := make(encFieldValues, len(src))
		for k, v := range src {
			ef, _ := encodeNode(v)
			out[k] = ef
		}
		return out, nil
	}
	encodeNode = func(n *FieldValue) (encFieldValue, *int) {
		if n == nil {
			return encFieldValue{}, nil
		}
		key := n.ID()
		// should we dictionary this node?
		if fvnIndex != nil && fvnCount[key] > 1 {
			if pos, ok := fvnIndex[key]; ok {
				return encFieldValue{Ni: &pos}, &pos
			}
			// first time, build a dict entry
			pos := len(fvnDict)
			fvnIndex[key] = pos
			// Reserve the slot immediately to prevent conflicts
			fvnDict = append(fvnDict, encFieldValue{})

			// inline-encode its contents for the dictionary
			ef := encFieldValue{V: n.Value}
			if len(n.Children) > 0 {
				childrenEnc, childrenIdx := encodeFV(n.Children)
				if childrenIdx != nil {
					ef.Ci = childrenIdx
				} else {
					ef.Cvl = childrenEnc
				}
			}
			// Fill the reserved slot
			fvnDict[pos] = ef
			return encFieldValue{Ni: &pos}, &pos
		}

		// inline directly
		ef := encFieldValue{V: n.Value}
		if len(n.Children) > 0 {
			childrenEnc, childrenIdx := encodeFV(n.Children)
			if childrenIdx != nil {
				ef.Ci = childrenIdx
			} else {
				ef.Cvl = childrenEnc
			}
		}
		return ef, nil
	}

	// build CallerResults
	encCR := make(map[string][]encCallFrame, len(tr.CallerResults))
	for caller, frames := range tr.CallerResults {
		row := make([]encCallFrame, len(frames))
		for i, cf := range frames {
			eCF := encCallFrame{
				T: cf.TimeMillis,
			}

			// FieldValues
			fvInline, fvIdx := encodeFV(cf.FieldValues)
			if fvIdx != nil {
				eCF.FVi = fvIdx
			} else {
				eCF.FV = fvInline
			}

			// StackFrame
			key := anyKey(cf.Stack)
			if stIndex != nil && stCount[key] > 1 {
				if pos, ok := stIndex[key]; ok {
					eCF.Si = &pos
				} else {
					pos := len(stDict)
					stIndex[key] = pos
					stDict = append(stDict, cf.Stack)
					eCF.Si = &pos
				}
			} else {
				eCF.St = cf.Stack
			}

			row[i] = eCF
		}
		encCR[caller] = row
	}

	buf.Reset()
	enc.Reset(buf)
	err := enc.Encode(encTestResult{
		TestFunction:     tr.TestFunction,
		CallerResults:    encCR,
		ProjectPanics:    tr.ProjectPanics,
		ModulePanics:     tr.ModulePanics,
		ModuleChangesHit: tr.ModuleChangesHit,
		TestFailure:      tr.TestFailure,
		FVDict:           fvDict,
		FVNodeDict:       fvnDict,
		STDict:           stDict,
	})
	return buf.Bytes(), err
}

func (tr *TestResult) UnmarshalMsgpack(data []byte) error {
	var enc encTestResult
	if err := msgpack.Unmarshal(data, &enc); err != nil {
		return err
	}

	// Decode the fields
	tr.TestFunction = enc.TestFunction
	tr.ProjectPanics = enc.ProjectPanics
	tr.ModulePanics = enc.ModulePanics
	tr.ModuleChangesHit = enc.ModuleChangesHit
	tr.TestFailure = enc.TestFailure

	// Decode CallFrames with dictionary support
	tr.CallerResults = make(map[string][]CallFrame, len(enc.CallerResults))

	var decodeNode func(ef encFieldValue) (*FieldValue, error)
	var decodeFV func(efv encFieldValues, idx *int) (FieldValues, error)
	decodeNode = func(ef encFieldValue) (*FieldValue, error) {
		if ef.Ni != nil {
			// Reference to node dictionary
			if *ef.Ni >= 0 && *ef.Ni < len(enc.FVNodeDict) {
				dictEntry := enc.FVNodeDict[*ef.Ni]
				return decodeNode(dictEntry)
			}
			return nil, fmt.Errorf("invalid encoded node index: %d", *ef.Ni)
		}

		fv := &FieldValue{Value: ef.V}
		var err error
		if ef.Ci != nil { // Reference to children dictionary
			fv.Children, err = decodeFV(nil, ef.Ci)
		} else if ef.Cvl != nil { // Inline children
			fv.Children, err = decodeFV(ef.Cvl, nil)
		}
		return fv, err
	}

	decodeFV = func(efv encFieldValues, idx *int) (FieldValues, error) {
		if idx != nil {
			// Reference to FieldValues dictionary
			if *idx >= 0 && *idx < len(enc.FVDict) {
				efv = enc.FVDict[*idx]
			} else {
				return nil, fmt.Errorf("invalid encoded fv index: %d", *idx)
			}
		}
		if efv == nil {
			return nil, nil
		}

		result := make(FieldValues, len(efv))
		for k, v := range efv {
			fv, err := decodeNode(v)
			if err != nil {
				return nil, err
			}
			result[k] = fv
		}
		return result, nil
	}

	for caller, encFrames := range enc.CallerResults {
		frames := make([]CallFrame, len(encFrames))
		for i, encFrame := range encFrames {
			// Decode FieldValues
			fv, err := decodeFV(encFrame.FV, encFrame.FVi)
			if err != nil {
				return err
			}
			cf := CallFrame{
				FieldValues: fv,
				TimeMillis:  encFrame.T,
			}

			if encFrame.Si != nil { // Decode Stack from dictionary
				if *encFrame.Si >= 0 && *encFrame.Si < len(enc.STDict) {
					cf.Stack = enc.STDict[*encFrame.Si]
				} else {
					return fmt.Errorf("invalid encoded stack index: %d", *encFrame.Si)
				}
			} else {
				cf.Stack = encFrame.St
			}

			frames[i] = cf
		}
		tr.CallerResults[caller] = frames
	}

	return nil
}

// CallFrame records field values for a single call and its stack
type CallFrame struct {
	// FieldValues records the captured state.
	FieldValues FieldValues `msgpack:"f"`
	// Stack holds the call stack.
	Stack []StackFrame `msgpack:"s"`
	// TimeMillis is the execution time in milliseconds since process start.
	TimeMillis uint32 `msgpack:"t"`
}

// FieldValues is a map of field names to FieldValue
type FieldValues map[string]*FieldValue

// FieldValue represents a value and optional nested children
type FieldValue struct {
	// Value holds the string representation.
	Value string `msgpack:"v"`
	// Children contains nested field values.
	Children FieldValues `msgpack:"c,omitempty"`
}

// ID returns a key for the value and children.
func (fv *FieldValue) ID() string {
	if fv == nil {
		return ""
	}
	return stringKey(fv.Value + "|" + fv.Children.ID())
}

// StackFrame represents one frame in a call stack
type StackFrame struct {
	// File is the source file path.
	File string `msgpack:"fi"`
	// Line is the line number.
	Line uint32 `msgpack:"li"`
	// Function is the function identifier.
	Function string `msgpack:"fu"`
}

// ID returns a key for the stack frame.
func (sf *StackFrame) ID() string {
	if sf == nil {
		return ""
	}
	return stringKey(sf.File + strconv.Itoa(int(sf.Line)) + sf.Function)
}

// Equal reports whether frames match.
func (sf *StackFrame) Equal(other *StackFrame) bool {
	if sf == other {
		return true // shortcut
	}
	return sf.File == other.File && sf.Line == other.Line && sf.Function == other.Function
}

// FlattenFieldValues converts the hierarchical FieldValues tree back into the
// flat dot-separated key => value form.
func (fv FieldValues) FlattenFieldValues() map[string]string {
	flat := make(map[string]string)
	var walk func(prefix string, cur FieldValues)
	walk = func(prefix string, cur FieldValues) {
		for name, fv := range cur {
			key := name
			if prefix != "" {
				key = prefix + "." + name
			}

			if len(fv.Children) == 0 { // leaf
				flat[key] = fv.Value
				continue
			}
			// else, recurse
			walk(key, fv.Children)
		}
	}

	walk("", fv)
	return flat
}

// ID returns the hash of field values.
func (fv FieldValues) ID() string {
	if fv == nil {
		return ""
	} else if len(fv) == 0 {
		return "empty"
	}
	hash := sha1.New()
	var walk func(cur FieldValues)
	walk = func(cur FieldValues) {
		sortedKeys := slices.Collect(maps.Keys(cur))
		sort.Strings(sortedKeys)
		for _, key := range sortedKeys {
			hash.Write([]byte(key))
			fv := cur[key]
			if len(fv.Children) == 0 {
				hash.Write([]byte(fv.Value))
			} else {
				walk(fv.Children)
			}
		}
	}
	walk(fv)
	return string(hash.Sum(nil))
}

// MutationResult summarizes mutation testing results
type MutationResult struct {
	// MutationCount is the total mutations executed.
	MutationCount int
	// SquashedCount is the number of deduplicated mutations.
	SquashedCount int
}
