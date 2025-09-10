package lens

import (
	"errors"
	"fmt"
	"go/ast"
	"go/build"
	"go/token"
	"go/types"
	"maps"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"sync"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
)

const debugCallChain = "" // Set to function name to log call chains with function

// CallerStaticAnalysis performs static analysis to determine which project functions call
// the provided moduleChanges. Returned are the functions in the project that may delegate
// to the updated module functions.
func CallerStaticAnalysis(moduleChanges []*ModuleFunction, projectDir string) ([]*CallerFunction, ReachableModuleChange, error) {
	// Load all non-test packages in the project and build SSA and call-graph using CHA (class hierarchy analysis)
	cg, err := loadProjectPackageCallGraph(projectDir, false)
	if err != nil || cg == nil {
		return nil, nil, err
	}

	// Match changed Functions -> *ssa.Function nodes for quick comparison
	cgNodeFunctions := make(map[string]*ssa.Function)
	// Identify any root callgraph.Nodes (package main, func main) to limit calls above the roots
	rootNodes := make(map[*callgraph.Node]bool)
	for fn, node := range cg.Nodes {
		ident, _ := makeSSAFunctionIdent(fn) // ignore supported here, try to capture all
		cgNodeFunctions[ident] = fn
		if isMainFunction(fn) || isInitFunction(fn) {
			rootNodes[node] = true
		}
	}
	changedSSAFunctions := make(map[*ssa.Function]*ModuleFunction, len(moduleChanges))
	for _, ch := range moduleChanges {
		if ssaFn := cgNodeFunctions[ch.FunctionIdent]; ssaFn != nil {
			changedSSAFunctions[ssaFn] = ch
		}
	}

	eg := ErrGroupLimitCPU()
	var callerFuncMux sync.Mutex
	callerFuncMap := make(map[string]*CallerFunction)
	for changedSSA, changedFunc := range changedSSAFunctions {
		eg.Go(func() error {
			return reverseDFS(cg.Nodes[changedSSA], rootNodes, func(chain []*callgraph.Node) error {
				callerNode := chain[len(chain)-1]
				fn := callerNode.Func
				if fn == nil || fn == changedSSA || fn.Package() == nil || fn.Package().Pkg == nil {
					return nil
				} else if rootNodes[callerNode] {
					return nil // don't include root nodes as part of the analysis, they will confuse testing
				}

				fnFile := filePathForSSAFunc(fn)
				// Only consider functions that belong to the user’s project, skip while traversing any module changes
				if contained, err := fileWithinDir(fnFile, projectDir); !contained || err != nil {
					return nil
				} else if IsGeneratedFile(fnFile) {
					return nil
				} else if compiled, err := compilesForBuildContext(fnFile); !compiled || err != nil {
					return err
				}

				ident, supported := makeSSAFunctionIdent(fn)
				if !supported {
					return nil // don't record functions we can't inject or call into
				}
				callerFuncMux.Lock()
				defer callerFuncMux.Unlock()
				if callerFunc, exists := callerFuncMap[ident]; exists {
					// add change function
					if !slices.ContainsFunc(callerFunc.ChangeFunctions, func(f *ModuleFunction) bool {
						return f.FunctionIdent == changedFunc.FunctionIdent
					}) {
						callerFunc.ChangeFunctions = append(callerFunc.ChangeFunctions, changedFunc)
					}
				} else { // add to map
					entryLineNumber, returnPoints, endsInPanic := analyzeSSAFunctionReturnPoints(fn)
					callerFuncMap[ident] = &CallerFunction{
						Function: Function{
							FilePath:        fnFile,
							PackageName:     fn.Package().Pkg.Path(),
							FunctionIdent:   ident,
							FunctionName:    fn.Name(),
							EntryLineNumber: entryLineNumber,
							ReturnPoints:    returnPoints,
							ReturnPanic:     endsInPanic,
						},
						ChangeFunctions: []*ModuleFunction{changedFunc},
					}
				}
				return nil
			})
		})
	}
	if err := eg.Wait(); err != nil {
		return nil, nil, err
	}

	result := slices.Collect(maps.Values(callerFuncMap))
	// build a map for module functions which are actually reachable
	reachableModuleChanges := make(ReachableModuleChange)
	for _, cf := range result {
		for _, f := range cf.ChangeFunctions {
			reachableModuleChanges[f.FunctionIdent] = f
		}
	}
	return result, reachableModuleChanges, nil
}

// IsGeneratedFile returns true if the filename follows known patterns for generated go files.
func IsGeneratedFile(filename string) bool {
	suffixes := []string{".pb.go", ".pb.gw.go", "_grpc.pb.go", "_mock.go", "_gen.go", ".gen.go", GeneratedTestFileSuffix}
	for _, s := range suffixes {
		if strings.HasSuffix(filename, s) {
			return true
		}
	}
	return false
}

// TestStaticAnalysis loads all packages (including test packages), then for each
// provided CallerFunction (project function from module analysis), performs a reverse DFS
// to find any test functions that eventually lead to the given project functions.
func TestStaticAnalysis(callers []*CallerFunction, projectDir string) ([]*TestFunction, error) {
	// Load all packages including tests and build SSA + call-graph
	cg, err := loadProjectPackageCallGraph(projectDir, true)
	if err != nil || cg == nil {
		return nil, err
	}

	// Identify test roots (to retain) and other roots (nodes to stop at)
	testRoots := make(map[*callgraph.Node]bool)
	allRoots := make(map[*callgraph.Node]bool)
	for fn, node := range cg.Nodes {
		if isGoTestFunction(fn) {
			if inDir, err := fileWithinDir(filePathForSSAFunc(fn), projectDir); err != nil {
				return nil, err
			} else if inDir {
				testRoots[node] = true
				allRoots[node] = true
			}
		} else if isMainFunction(fn) || isInitFunction(fn) {
			allRoots[node] = true
		}
	}
	if len(testRoots) == 0 {
		return nil, nil // nothing to do
	}

	// Map each CallerFunction to its *ssa.Function for quick lookup
	cgNodeFunctions := make(map[string][]*ssa.Function)
	for fn := range cg.Nodes {
		ident, _ := makeSSAFunctionIdent(fn) // ignore supported for building this map
		cgNodeFunctions[ident] = append(cgNodeFunctions[ident], fn)
	}
	callerSSA := make(map[*ssa.Function]*CallerFunction)
	for _, c := range callers {
		for _, ssaFn := range cgNodeFunctions[c.FunctionIdent] {
			callerSSA[ssaFn] = c
		}
	}

	// For each caller, reverse-DFS up to testRoots and record any relevant tests
	eg := ErrGroupLimitCPU()
	var testFuncMux sync.Mutex
	testFuncMap := make(map[string]*TestFunction)
	for ssaFn, caller := range callerSSA {
		startNode := cg.Nodes[ssaFn]
		if startNode == nil {
			continue
		}
		eg.Go(func() error {
			return reverseDFS(startNode, allRoots, func(chain []*callgraph.Node) error {
				end := chain[len(chain)-1]
				if !testRoots[end] {
					return nil // not yet at a test root
				}

				// we've found a Test function that transitively calls our caller
				testSSA := end.Func
				ident, supported := makeSSAFunctionIdent(testSSA)
				if !supported {
					return nil // don't record unsupported functions we can't invoke
				}
				testFuncMux.Lock()
				defer testFuncMux.Unlock()
				if tf, exists := testFuncMap[ident]; exists {
					// add caller
					if !slices.ContainsFunc(tf.Targets, func(cf *CallerFunction) bool {
						return cf.FunctionIdent == caller.FunctionIdent
					}) {
						tf.Targets = append(tf.Targets, caller)
					}
				} else { // add to map
					entryLineNumber, returnPoints, endsInPanic := analyzeSSAFunctionReturnPoints(testSSA)
					testFuncMap[ident] = &TestFunction{
						Function: Function{
							FilePath:        filePathForSSAFunc(testSSA),
							PackageName:     testSSA.Package().Pkg.Path(),
							FunctionIdent:   ident,
							FunctionName:    testSSA.Name(),
							EntryLineNumber: entryLineNumber,
							ReturnPoints:    returnPoints,
							ReturnPanic:     endsInPanic,
						},
						Targets: []*CallerFunction{caller},
					}
				}
				return nil
			})
		})
	}
	if err := eg.Wait(); err != nil {
		return nil, err
	}

	return slices.Collect(maps.Values(testFuncMap)), nil
}

// TODO - FUTURE - replace CHA with https://pkg.go.dev/golang.org/x/tools/go/analysis
//   analysis may be able to provide more accurate traversal, and reduce the size of our implementation

// loadProjectPackageCallGraph loads the project packages and creates an SSA Program and call-graph from the packages.
func loadProjectPackageCallGraph(projectDir string, includeTests bool) (*callgraph.Graph, error) {
	cfg := &packages.Config{
		Dir:   projectDir,
		Tests: includeTests,
		Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedName |
			packages.NeedImports | packages.NeedDeps | packages.NeedTypes | packages.NeedTypesInfo,
	}

	var patterns []string
	if FileExists(filepath.Join(projectDir, "go.mod")) {
		patterns = append(patterns, "./...")
	}
	workPath := filepath.Join(projectDir, "go.work")
	if FileExists(workPath) {
		dirs, err := parseGoWork(workPath)
		if err != nil {
			return nil, err
		}
		for _, d := range dirs {
			if filepath.IsAbs(d) {
				patterns = append(patterns, filepath.Join(d, "..."))
			} else {
				patterns = append(patterns, "./"+filepath.ToSlash(filepath.Join(d, "...")))
			}
		}
	}
	if len(patterns) == 0 {
		return nil, fmt.Errorf("no go.mod or go.work found in %s", projectDir)
	}

	pkgs, err := packages.Load(cfg, patterns...)
	if err != nil {
		return nil, err
	} else if packages.PrintErrors(pkgs) > 0 {
		return nil, errors.New("project packages contain errors")
	} else if len(pkgs) == 0 {
		return nil, nil
	}

	prog := ssa.NewProgram(pkgs[0].Fset, ssa.GlobalDebug)

	created := make(map[*types.Package]*ssa.Package)
	// Recursive function to create an ssa.Package for pkg, plus all its imports
	var createAll func(*packages.Package) *ssa.Package
	createAll = func(p *packages.Package) *ssa.Package {
		if p.Types == nil || p.TypesInfo == nil {
			return nil // If there's no type info, we can't build SSA for it
		} else if ssaPkg, ok := created[p.Types]; ok {
			return ssaPkg // Already created
		}

		// Create but do not build yet
		ssaPkg := prog.CreatePackage(p.Types, p.Syntax, p.TypesInfo, false)
		created[p.Types] = ssaPkg

		// Recurse on all imports
		for _, imp := range p.Imports {
			createAll(imp)
		}
		// Return this newly created package
		return ssaPkg
	}

	// For each top-level package from packages.Load, recursively create ssa
	for _, p := range pkgs {
		createAll(p)
	}
	prog.Build() // build all packages, will be concurrent unless serial flag is passed

	return cha.CallGraph(prog), nil
}

// filePathForSSAFunc attempts to retrieve the file path of the function’s position.
func filePathForSSAFunc(fn *ssa.Function) string {
	if fn == nil {
		return ""
	} else if fn.Pos() == 0 {
		return ""
	}
	pos := fn.Prog.Fset.Position(fn.Pos())
	return pos.Filename
}

// makeFunctionIdent creates a normalized key for a SSA function, incorporating package and (if any) receiver type.
func makeSSAFunctionIdent(fn *ssa.Function) (string, bool) {
	if fn == nil {
		return "", false
	}
	var pkgName string
	if fn.Package() != nil && fn.Package().Pkg != nil {
		pkgName = fn.Package().Pkg.Path()
	}

	if funcDecl, ok := fn.Syntax().(*ast.FuncDecl); ok {
		return MakeFunctionIdent(pkgName, funcDecl), true
	}
	return makeFunctionIdentStr(pkgName, "", fn.Name()), false // unexpected type fallback
}

// MakeFunctionIdent creates a normalized key with package and receiver type.
func MakeFunctionIdent(pkgName string, funcDecl *ast.FuncDecl) string {
	var recv string
	if funcDecl.Recv != nil && len(funcDecl.Recv.List) > 0 {
		// types.ExprString will render "*MyType", "pkg.Type", "[][]T", etc
		recv = types.ExprString(funcDecl.Recv.List[0].Type)
	}

	return makeFunctionIdentStr(pkgName, recv, funcDecl.Name.Name)
}

func makeFunctionIdentStr(pkg, receiverType, funcName string) string {
	if receiverType != "" {
		return pkg + ":" + receiverType + "." + funcName
	} else {
		return pkg + ":" + funcName
	}
}

// analyzeSSAFunctionReturnPoints collects the entry line, each return point (line + call count),
// and a flag if the function has results but only panics (no normal return).
func analyzeSSAFunctionReturnPoints(fn *ssa.Function) (uint32, []FunctionReturn, bool) {
	fset := fn.Prog.Fset
	var returnCount, panicCount int
	var infos []FunctionReturn
	for _, block := range fn.Blocks {
		for _, instr := range block.Instrs {
			// detect a real return instruction
			if ret, ok := instr.(*ssa.Return); ok && ret.Pos() != token.NoPos {
				returnCount++
				line := fset.Position(ret.Pos()).Line
				var callCount uint32
				for _, val := range ret.Results {
					if _, isCall := val.(ssa.CallInstruction); isCall {
						callCount++
					}
				}
				infos = append(infos, FunctionReturn{Line: uint32(line), CallCount: callCount})
			}

			// detect a panic instruction
			if _, ok := instr.(*ssa.Panic); ok {
				panicCount++
			}
		}

		// if this is an exit block (no successors), record last‐instr call count
		if len(block.Succs) == 0 && len(block.Instrs) > 0 {
			last := block.Instrs[len(block.Instrs)-1]
			if pos := last.Pos(); pos != token.NoPos {
				line := fset.Position(pos).Line
				var callCount uint32
				if _, ok := last.(ssa.CallInstruction); ok {
					callCount = 1
				}
				infos = append(infos, FunctionReturn{Line: uint32(line), CallCount: callCount})
			}
		}
	}

	entryLine := fset.Position(fn.Pos()).Line
	hasResults := fn.Signature.Results().Len() > 0

	// if it declares results but has no return instructions and at least one panic
	endsInPanic := hasResults && returnCount == 0 && panicCount > 0

	return uint32(entryLine), mergeReturnInfos(infos), endsInPanic
}

// AnalyzeASTFunctionReturnPoints collects entry line and return lines; bool signals panic.
func AnalyzeASTFunctionReturnPoints(fset *token.FileSet, decl *ast.FuncDecl) (uint32, []FunctionReturn, bool) {
	var returnCount, panicCount int
	var infos []FunctionReturn
	if decl.Body != nil {
		ast.Inspect(decl.Body, func(n ast.Node) bool {
			switch node := n.(type) {
			// stop descending when we hit a nested FuncLit
			case *ast.FuncLit:
				return false
			// count every ReturnStmt in the outer body
			case *ast.ReturnStmt:
				if node.Pos() == token.NoPos {
					return true
				}
				returnCount++
				line := fset.Position(node.Pos()).Line
				var callCount uint32
				for _, expr := range node.Results {
					ast.Inspect(expr, func(n2 ast.Node) bool {
						if _, ok := n2.(*ast.CallExpr); ok {
							callCount++
						}
						return true
					})
				}
				infos = append(infos, FunctionReturn{Line: uint32(line), CallCount: callCount})
				return false // no need to inspect inside the ReturnStmt
			// count any panic calls in the outer body
			case *ast.CallExpr:
				if ident, ok := node.Fun.(*ast.Ident); ok && ident.Name == "panic" {
					panicCount++
				}
			}
			return true
		})
	}

	entryLine := fset.Position(decl.Pos()).Line
	hasReturnResults := decl.Type.Results != nil && len(decl.Type.Results.List) > 0
	// if function declares results but has no returns and has at least one panic, then it “ends in panic” (no normal exit path)
	endsInPanic := hasReturnResults && returnCount == 0 && panicCount > 0
	return uint32(entryLine), mergeReturnInfos(infos), endsInPanic
}

// mergeReturnInfos sorts by line and merges duplicates by summing CallCount.
func mergeReturnInfos(infos []FunctionReturn) []FunctionReturn {
	sort.Slice(infos, func(i, j int) bool { return infos[i].Line < infos[j].Line })
	unique := infos[:0]
	for i, info := range infos {
		if i == 0 || info.Line != infos[i-1].Line {
			unique = append(unique, info)
		} else {
			unique[len(unique)-1].CallCount += info.CallCount
		}
	}
	return unique
}

// reverseDFS visits all caller Nodes in the call graph, starting from `start`
// and going "upwards" to each caller using parent pointers to track the call chain.
func reverseDFS(start *callgraph.Node, rootNodes map[*callgraph.Node]bool,
	visitFunc func(chain []*callgraph.Node) error) error {
	type frame struct {
		node  *callgraph.Node
		chain []*callgraph.Node
	}
	// seed the stack with a fresh slice containing only start
	stack := []frame{{
		node:  start,
		chain: []*callgraph.Node{start},
	}}
	visited := make(map[*callgraph.Node]struct{})
	visited[start] = struct{}{}

	// Iterative DFS over the stack
	for len(stack) > 0 {
		// Pop the last stack frame (current frame)
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		logStackChain(f.chain)

		// first, invoke the callback on the current chain
		if err := visitFunc(f.chain); err != nil {
			return err
		} else if rootNodes[f.node] {
			continue // if we've reached a root, do NOT traverse its parents
		}

		// walk to each caller
		for _, inEdge := range f.node.In {
			caller := inEdge.Caller
			if caller == nil {
				continue
			} else if _, ok := visited[caller]; ok {
				continue
			}
			visited[caller] = struct{}{}

			var newChain []*callgraph.Node
			if debugCallChain == "" {
				// just don't build the call chain for efficiency
				newChain = []*callgraph.Node{caller}
			} else {
				newChain = make([]*callgraph.Node, len(f.chain)+1)
				copy(newChain, f.chain)
				newChain[len(f.chain)] = caller
			}

			stack = append(stack, frame{node: caller, chain: newChain})
		}
	}
	return nil
}

// logStackChain logs the call chain in a human-readable format.
// The chain is expected to be in invocation order (e.g., top-level caller first).
func logStackChain(chain []*callgraph.Node) {
	if debugCallChain == "" {
		return
	}
	parts := make([]string, len(chain))
	for i, node := range chain {
		if node.Func != nil {
			parts[i] = node.Func.Name()
		} else {
			parts[i] = "unknown"
		}
	}
	if len(parts) == 1 {
		fmt.Printf("Chain start: %s\n", parts[0])
		return
	}
	str := strings.Join(parts, " <- ")
	if strings.Contains(str, debugCallChain) {
		fmt.Printf("Call chain: %s\n", str)
	}
}

// isMainFunction detects standard "func main()" functions.
func isMainFunction(fn *ssa.Function) bool {
	return fn != nil && fn.Package() != nil && fn.Signature != nil &&
		fn.Package().Pkg.Name() == "main" && fn.Name() == "main" &&
		fn.Signature.Recv() == nil && fn.Signature.Params().Len() == 0
}

// isInitFunction detects standard "func init()" functions.
func isInitFunction(fn *ssa.Function) bool {
	if fn == nil {
		return false
	} else if decl, ok := fn.Syntax().(*ast.FuncDecl); ok {
		return decl.Name.Name == "init" && decl.Recv == nil && decl.Type.Params.NumFields() == 0
	}
	return false
}

// isGoTestFunction detects standard "func TestXxx(t *testing.T)" test functions.
func isGoTestFunction(fn *ssa.Function) bool {
	if fn == nil || fn.Package() == nil || fn.Signature == nil {
		return false
	} else if _, ok := fn.Syntax().(*ast.FuncDecl); !ok {
		return false // only select the top level functions, don't try to be granular to any test case literal / anonymous test functions
	} else if !strings.HasPrefix(fn.Name(), "Test") {
		return false
	} else if !strings.HasSuffix(filePathForSSAFunc(fn), "_test.go") {
		return false
	} else if fn.Signature.Params().Len() != 1 {
		return false // Must have exactly 1 parameter: (t *testing.T)
	}
	// validate parameter to be testing.T
	ptrType, ok := fn.Signature.Params().At(0).Type().(*types.Pointer)
	if !ok {
		return false
	}
	named, ok := ptrType.Elem().(*types.Named)
	if !ok {
		return false
	}
	obj := named.Obj()
	return obj.Pkg() != nil && obj.Pkg().Path() == "testing" && obj.Name() == "T"
}

func compilesForBuildContext(filePath string) (bool, error) {
	dir, file := filepath.Split(filePath)
	return build.Default.MatchFile(dir, file)
}
