package lens

import (
	"bytes"
	"cmp"
	"embed"
	"errors"
	"fmt"
	"go/ast"
	"go/build"
	"go/format"
	"go/importer"
	"go/parser"
	"go/scanner"
	"go/token"
	"go/types"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/go-analyze/bulk"
	"golang.org/x/sync/errgroup"
)

const (
	injectedFilenamePrefix            = "xx_lens_"
	syntheticFieldNamePrefixTemp      = "lenSyntheticTmp"
	syntheticFieldNamePrefixReturn    = "lenSyntheticRet"
	syntheticFieldNamePrefixRecursive = "lenSyntheticRec"
	syntheticFieldNamePrefixArg       = "lenSyntheticArg"
	syntheticFieldNamePrefixReceiver  = "lenSyntheticRecv"
	literalNil                        = "nil"
)

// MinGoVersion defines the minimum Go version required for instrumentation.
const MinGoVersion = "1.13" // Go 1.13+ is required due to signed shift count operations in generated code.

// IsGoVersionBelowMinimum returns true if goVersion is below MinGoVersion.
func IsGoVersionBelowMinimum(goVersion string) bool {
	if goVersion == "" {
		return false
	}
	return compareGoVersions(goVersion, MinGoVersion) < 0
}

// ErrNoFunctionBody indicates a function has no body (e.g., assembly-only or external).
var ErrNoFunctionBody = errors.New("function has no body (likely assembly or external implementation)")

// IsNormalAstError returns true if the error should be skipped rather than failing.
func IsNormalAstError(err error) bool {
	return errors.Is(err, ErrNoFunctionBody)
}

// embed the template files into the binary
//
//go:embed astclient.go
//go:embed astapi.go
var tmplFS embed.FS
var astFileLock = newDefaultStripedMutex()

// ASTModifier provides utilities for modifying Go AST.
// Extensions can use this to inject custom monitoring at specific points in code.
type ASTModifier struct {
	currPointId    atomic.Uint32
	cleanupLock    sync.Mutex
	cleanupActions []func() error
	fileNodeMap    sync.Map
	commitLock     sync.Mutex
	commitActions  map[string]func(*bytes.Buffer) error
}

func goCacheClean(goenv []string) error {
	cmd := exec.Command("go", "clean", "-cache", "-testcache")
	cmd.Env = mergeSafeEnv(goenv)
	return cmd.Run()
}

// MaxPointId returns the highest point currently tracked.
func (m *ASTModifier) MaxPointId() int {
	return int(m.currPointId.Load())
}

// Restore restores the modified files to their original state.
// The go environment must be provided so the build cache can be cleared.
func (m *ASTModifier) Restore(goenv []string) (result []error) {
	m.cleanupLock.Lock()
	defer m.cleanupLock.Unlock()
	if len(m.cleanupActions) == 0 {
		return // shortcut
	}
	for _, f := range m.cleanupActions {
		if err := f(); err != nil {
			result = append(result, err)
		}
	}
	m.cleanupActions = m.cleanupActions[:0] // clear completed actions
	if err := goCacheClean(goenv); err != nil {
		result = append(result, fmt.Errorf("failure to clean go cache: %w", err))
	}
	return
}

func (m *ASTModifier) addCleanupAction(f func() error) {
	m.cleanupLock.Lock()
	defer m.cleanupLock.Unlock()
	m.cleanupActions = append(m.cleanupActions, f)
}

type parsedFile struct {
	fset *token.FileSet
	file *ast.File
}

// loadParsedFileNode provides the currently parsed file.
// fileLock must be held before invoking, and until fileNode changes are done.
func (m *ASTModifier) loadParsedFileNode(filepath string) (*token.FileSet, *ast.File, error) {
	file, ok := m.fileNodeMap.Load(filepath)
	if ok {
		pf := file.(*parsedFile)
		return pf.fset, pf.file, nil
	}

	fset := token.NewFileSet()
	fileNode, err := parser.ParseFile(fset, filepath, nil, parser.ParseComments)
	if err != nil {
		return nil, nil, fmt.Errorf("ast parse failure %s: %w", filepath, err)
	}
	m.fileNodeMap.Store(filepath, &parsedFile{
		fset: fset,
		file: fileNode,
	})

	m.commitLock.Lock()
	defer m.commitLock.Unlock()
	if m.commitActions == nil {
		m.commitActions = make(map[string]func(*bytes.Buffer) error)
	}
	m.commitActions[filepath] = func(buf *bytes.Buffer) error {
		buf.Reset()
		if err := format.Node(buf, fset, fileNode); err != nil {
			return fmt.Errorf("ast format failure %s: %w", filepath, err)
		} else if err := m.backupOrigFile(filepath); err != nil {
			return err
		} else if err := os.WriteFile(filepath, buf.Bytes(), 0o644); err != nil {
			return fmt.Errorf("ast write failure %s: %w", filepath, err)
		}
		return nil
	}
	return fset, fileNode, nil
}

// CommitFile writes pending edits for a single file.
func (m *ASTModifier) CommitFile(filepath string) error {
	lock := astFileLock.Lock(filepath)
	defer lock.Unlock()
	return m.commitFileInternal(filepath)
}

func (m *ASTModifier) commitFileInternal(filepath string) error {
	m.commitLock.Lock()
	defer m.commitLock.Unlock()

	if action, ok := m.commitActions[filepath]; ok {
		delete(m.commitActions, filepath)
		m.fileNodeMap.Delete(filepath)
		var buf bytes.Buffer
		return action(&buf)
	}
	return nil
}

// Commit flushes all pending AST modifications to disk.
func (m *ASTModifier) Commit() error {
	writeCount := runtime.NumCPU()
	bufChan := make(chan *bytes.Buffer, writeCount)
	for i := 0; i < writeCount; i++ {
		bufChan <- bytes.NewBuffer(nil)
	}
	var errGroup errgroup.Group
	m.commitLock.Lock()
	defer m.commitLock.Unlock()
	for _, action := range m.commitActions {
		buf := <-bufChan
		errGroup.Go(func() error {
			defer func() {
				bufChan <- buf
			}()
			buf.Reset()
			return action(buf)
		})
	}
	if err := errGroup.Wait(); err != nil {
		return err
	}
	m.commitActions = nil // set to nil to allow GC
	m.fileNodeMap.Clear()
	return nil
}

// InjectASTClient prepares a package directory by inserting the configured client code to enable other AST point functions.
func (m *ASTModifier) InjectASTClient(pkgDir string, srvPort int, maxFieldRecurse, maxFieldLen int) error {
	if matches, _ := filepath.Glob(filepath.Join(pkgDir, injectedFilenamePrefix+"*_gen.go")); len(matches) > 0 {
		return nil // already been injected into the package
	}

	// load templates from embedded FS
	clientSrc, err := tmplFS.ReadFile("astclient.go")
	if err != nil {
		return fmt.Errorf("load embedded astclient: %w", err)
	}
	apiSrc, err := tmplFS.ReadFile("astapi.go")
	if err != nil {
		return fmt.Errorf("load embedded astapi: %w", err)
	}

	// rewrite package and replace const values
	var buf bytes.Buffer
	pkgName, err := detectPackageName(pkgDir)
	if err != nil {
		return err
	}
	clientFile := filepath.Join(pkgDir, injectedFilenamePrefix+"client_gen.go")
	clientTxt, err := rewriteAstClientTemplate(&buf, clientSrc, pkgName, map[string]string{
		"lensMonitorServerPort":      strconv.Itoa(srvPort),
		"lensMonitorFieldMaxRecurse": strconv.Itoa(maxFieldRecurse),
		"lensMonitorFieldMaxLen":     strconv.Itoa(maxFieldLen),
	})
	if err != nil {
		return fmt.Errorf("rewrite astclient failure: %w", err)
	} else if err := os.WriteFile(clientFile, clientTxt, 0o644); err != nil {
		return err
	}
	apiFile := filepath.Join(pkgDir, injectedFilenamePrefix+"api_gen.go")
	apiTxt, err := rewriteAstClientTemplate(&buf, apiSrc, pkgName, nil)
	if err != nil {
		return fmt.Errorf("rewrite astapi failure: %w", err)
	} else if err := os.WriteFile(apiFile, apiTxt, 0o644); err != nil {
		return err
	}
	m.addCleanupAction(func() error {
		return errors.Join(os.Remove(clientFile), os.Remove(apiFile))
	})
	return nil
}

func makeFileFilter(dir string) func(fi fs.FileInfo) bool {
	return func(fi fs.FileInfo) bool {
		name := fi.Name()
		// ignore tests files, they may be in a different pkg
		if strings.HasSuffix(name, "_test.go") {
			return false
		}
		// drop any file that the default go/build would ignore
		match, err := build.Default.MatchFile(dir, name)
		return err == nil && match
	}
}

// detectPackageName returns the single non-test package defined in dir.
// It fails if the directory is empty, contains only *_test.go packages, or mixes two different packages.
func detectPackageName(dir string) (string, error) {
	// parse only the package clause
	pkgs, err := parser.ParseDir(token.NewFileSet(), dir, makeFileFilter(dir), parser.PackageClauseOnly)
	if err != nil {
		return "", err
	} else if len(pkgs) == 0 {
		return "", fmt.Errorf("no non-test or main packages found in %s", dir)
	}
	pkgNames := bulk.MapKeysSlice(pkgs)
	if len(pkgNames) > 1 {
		return "", fmt.Errorf("multiple packages found in %s: %v", dir, pkgNames)
	}
	return pkgNames[0], nil
}

// rewriteAstClientTemplate sets package name and constant values for the ast client.
func rewriteAstClientTemplate(buf *bytes.Buffer, src []byte, newPkg string,
	constantReplacements map[string]string) ([]byte, error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, parser.ParseComments)
	if err != nil {
		return nil, err
	}

	// overwrite the package identifier
	file.Name = ast.NewIdent(newPkg)

	// mutate targeted consts inside the AST
	updateConstLiterals(file, constantReplacements)

	buf.Reset()
	if err := format.Node(buf, fset, file); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// updateConstLiterals walks every const and var declaration and, if it finds an
// identifier that matches one of the keys in `values`, replaces the *literal*
// on the same index position within the ValueSpec.
func updateConstLiterals(f *ast.File, values map[string]string) {
	if len(values) == 0 {
		return
	}
	for _, decl := range f.Decls {
		genDecl, ok := decl.(*ast.GenDecl)
		if !ok || (genDecl.Tok != token.CONST && genDecl.Tok != token.VAR) {
			continue
		}
		for _, spec := range genDecl.Specs {
			vspec := spec.(*ast.ValueSpec)
			for i, ident := range vspec.Names {
				if v, hasReplacement := values[ident.Name]; hasReplacement {
					lit := &ast.BasicLit{
						Kind:  token.INT,
						Value: v,
					}
					// ensure we have a slot to replace
					if len(vspec.Values) <= i {
						for len(vspec.Values) < i {
							vspec.Values = append(vspec.Values, nil)
						}
						vspec.Values = append(vspec.Values, lit)
					} else {
						vspec.Values[i] = lit
					}
				}
			}
		}
	}
}

// backupOrigFile will copy the file to a .bkp file if one does not already exist.
func (m *ASTModifier) backupOrigFile(filepath string) error {
	bkpFile := filepath + ".bkp"
	if !FileExists(bkpFile) {
		if err := CopyFile(filepath, bkpFile); err != nil {
			return fmt.Errorf("ast backup failure: %w", err)
		}
		m.addCleanupAction(func() error {
			return replaceFile(bkpFile, filepath)
		})
	}
	return nil
}

func (m *ASTModifier) nextPointId() (uint32, error) {
	var val uint32
	for {
		val = m.currPointId.Load()
		if val == 0 { // 0 is an invalid point id, attempt to skip it
			if m.currPointId.CompareAndSwap(0, 2) {
				return 1, nil
			}
			continue // retry
		} else if nextVal := val + 1; nextVal == 0 {
			return 0, errors.New("point id overflow")
		} else if m.currPointId.CompareAndSwap(val, nextVal) {
			break
		}
	}
	return val, nil
}

// injectPoint bundles the repetitive “backup → parse → mutate → write” sequence.
// `modify` gets the function body and the freshly allocated pointID and must mutate the AST in-place.
func (m *ASTModifier) injectPoint(filePath, pkg, funcIdent string, modify func(body *ast.BlockStmt, pointID uint32)) (uint32, error) {
	lock := astFileLock.Lock(filePath)
	defer lock.Unlock()

	_, fileNode, err := m.loadParsedFileNode(filePath)
	if err != nil {
		return 0, err
	}
	target := findFuncDecl(fileNode, pkg, funcIdent)
	if target == nil {
		return 0, fmt.Errorf("function %s not found in %s", funcIdent, filePath)
	} else if target.Body == nil {
		return 0, fmt.Errorf("%w: %s in %s", ErrNoFunctionBody, funcIdent, filePath)
	}

	pointID, err := m.nextPointId()
	if err != nil {
		return 0, err
	}
	modify(target.Body, pointID)

	return pointID, nil
}

func hasPatchlensMarker(funcDecl *ast.FuncDecl, marker string) bool {
	if funcDecl.Doc == nil {
		return false
	}
	for _, c := range funcDecl.Doc.List {
		if strings.Contains(c.Text, marker) {
			return true
		}
	}
	return false
}

// InjectFuncPointPanic inserts a defer recovery at the start of the function. This recovery will invoke
// the client to communicate the state, but then re-panic.  Because this is the first defer statement,
// it will trigger only if no other recovery exists.
func (m *ASTModifier) InjectFuncPointPanic(f *Function) (uint32, error) {
	return m.injectPoint(f.FilePath, f.PackageName, f.FunctionIdent, func(body *ast.BlockStmt, pointID uint32) {
		// build:
		//   defer func() {
		//     if r := recover(); r != nil {
		//       sendLensPointRecoveryMessage(pointID, r)
		//       panic(r)
		//     }
		//   }()
		deferStmt := &ast.DeferStmt{
			Call: &ast.CallExpr{
				Fun: &ast.FuncLit{
					Type: &ast.FuncType{Params: &ast.FieldList{}},
					Body: &ast.BlockStmt{List: []ast.Stmt{
						// if r := recover(); r != nil { ... }
						&ast.IfStmt{
							Init: &ast.AssignStmt{
								Lhs: []ast.Expr{ast.NewIdent("r")},
								Tok: token.DEFINE,
								Rhs: []ast.Expr{&ast.CallExpr{Fun: ast.NewIdent("recover")}},
							},
							Cond: &ast.BinaryExpr{
								X:  ast.NewIdent("r"),
								Op: token.NEQ,
								Y:  ast.NewIdent(literalNil),
							},
							Body: &ast.BlockStmt{List: []ast.Stmt{
								// sendLensPointRecoveryMessage(pointID, r)
								&ast.ExprStmt{X: &ast.CallExpr{
									Fun: ast.NewIdent("sendLensPointRecoveryMessage"),
									Args: []ast.Expr{
										&ast.BasicLit{Kind: token.INT, Value: strconv.FormatUint(uint64(pointID), 10)},
										ast.NewIdent("r"),
									},
								}},
								// panic(r)
								&ast.ExprStmt{X: &ast.CallExpr{
									Fun:  ast.NewIdent("panic"),
									Args: []ast.Expr{ast.NewIdent("r")},
								}},
							}},
						},
					}},
				},
			},
		}
		body.List = append([]ast.Stmt{deferStmt}, body.List...)
	})
}

// InjectFuncPointReturnStates inserts a state point right before the return points within the function. If the return
// line has a function call, the return point will be inserted after the call.
func (m *ASTModifier) InjectFuncPointReturnStates(fn *Function) ([]uint32, error) {
	const modificationMarker = "patchlens:return-states"
	lock := astFileLock.Lock(fn.FilePath)
	defer lock.Unlock()

	fset, fileNode, err := m.loadParsedFileNode(fn.FilePath)
	if err != nil {
		return nil, err
	}
	funcDecl := findFuncDecl(fileNode, fn.PackageName, fn.FunctionIdent)
	if funcDecl == nil {
		return nil, fmt.Errorf("function %s not found in %s", fn.FunctionIdent, fn.FilePath)
	} else if funcDecl.Body == nil {
		return nil, fmt.Errorf("%w: %s in %s", ErrNoFunctionBody, fn.FunctionIdent, fn.FilePath)
	} else if hasPatchlensMarker(funcDecl, modificationMarker) {
		return []uint32{}, nil // already inserted
	}
	var funcResultTypes []ast.Expr
	var funcResultNames []string
	if funcDecl.Type.Results != nil {
		for _, field := range funcDecl.Type.Results.List {
			reps := len(field.Names)
			if reps == 0 {
				// if no explicit names, this field still counts once
				reps = 1
				funcResultNames = append(funcResultNames, "")
			} else {
				for _, id := range field.Names {
					funcResultNames = append(funcResultNames, id.Name)
				}
			}
			for i := 0; i < reps; i++ {
				funcResultTypes = append(funcResultTypes, field.Type)
			}
		}
	}

	// Try to build *types.Info; fall back to nil on any error
	info := buildTypesInfo(fset, fileNode) // may return nil

	// Walk the AST, rewriting every *ast.ReturnStmt in-place.
	var pointIDs []uint32
	var foundExplicitReturn bool
	// helper function that recursively rewrites a *ast.BlockStmt in-place
	var buf bytes.Buffer
	var rewriteBlock func(*ast.BlockStmt) error
	rewriteBlock = func(blk *ast.BlockStmt) error {
		for i, st := range blk.List {
			switch s := st.(type) {
			case *ast.ReturnStmt:
				foundExplicitReturn = true
				pointID, err := m.nextPointId()
				if err != nil {
					return err
				}
				pointIDs = append(pointIDs, pointID)

				decls := visibleDeclsBefore(funcDecl, s.Pos())
				newNode, err := buildReturnInstrumentation(&buf, s, pointID, fn, decls, funcResultTypes, info, funcResultNames)
				if err != nil {
					return err
				}
				blk.List[i] = newNode // replace old return with block
			case *ast.BlockStmt:
				if err := rewriteBlock(s); err != nil {
					return err
				}
			case *ast.IfStmt:
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
				if s.Else != nil {
					switch e := s.Else.(type) {
					case *ast.BlockStmt:
						if err := rewriteBlock(e); err != nil {
							return err
						}
					case *ast.IfStmt:
						if err := rewriteBlock(e.Body); err != nil {
							return err
						}
					}
				}
			case *ast.ForStmt:
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
			case *ast.RangeStmt:
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
			case *ast.SwitchStmt:
				for _, stmt := range s.Body.List {
					if cc, ok := stmt.(*ast.CaseClause); ok {
						blk := &ast.BlockStmt{List: cc.Body}
						if err := rewriteBlock(blk); err != nil {
							return err
						}
						cc.Body = blk.List
					}
				}
			case *ast.TypeSwitchStmt:
				for _, stmt := range s.Body.List {
					if cc, ok := stmt.(*ast.CaseClause); ok {
						blk := &ast.BlockStmt{List: cc.Body}
						if err := rewriteBlock(blk); err != nil {
							return err
						}
						cc.Body = blk.List
					}
				}
			}
		}
		return nil
	}

	if err := rewriteBlock(funcDecl.Body); err != nil {
		return nil, fmt.Errorf("ast rewrite failure %s: %w", fn.FilePath, err)
	} else if !foundExplicitReturn {
		pointID, err := m.nextPointId()
		if err != nil {
			return nil, err
		}
		pointIDs = []uint32{pointID}

		decls := visibleDeclsBefore(funcDecl, funcDecl.Body.End()-1)
		stmt, err := buildImplicitReturnInstrumentation(&buf, pointIDs[0], decls)
		if err != nil {
			return nil, fmt.Errorf("ast rewrite failure %s: %w", fn.FilePath, err)
		}

		funcDecl.Body.List = append(funcDecl.Body.List, stmt)

		// If function has return values, add explicit return statement
		hasReturnValues := len(funcResultTypes) > 0
		if hasReturnValues {
			allNamed := len(funcResultNames) > 0 && !slices.Contains(funcResultNames, "")

			// Check if ALL returns are non-blank named identifiers
			// We can only use naked return if ALL returns are named AND non-blank
			allNamedNonBlank := allNamed
			for _, name := range funcResultNames {
				if name == "_" {
					allNamedNonBlank = false
					break
				}
			}

			if allNamedNonBlank {
				// All returns are named and non-blank - use naked return
				funcDecl.Body.List = append(funcDecl.Body.List, &ast.ReturnStmt{})
			} else {
				// Need explicit return values
				returnExprs := make([]ast.Expr, len(funcResultTypes))
				for i, typ := range funcResultTypes {
					// Use named return if it's available and not a blank identifier
					if allNamed && funcResultNames[i] != "" && funcResultNames[i] != "_" {
						// Use the named return variable
						returnExprs[i] = ast.NewIdent(funcResultNames[i])
					} else {
						// Generate zero value for unnamed or blank identifier returns
						zeroVal, err := zeroValueForType(&buf, typ)
						if err != nil {
							return nil, fmt.Errorf("failed to generate zero value for return type: %w", err)
						}
						returnExprs[i] = zeroVal
					}
				}
				funcDecl.Body.List = append(funcDecl.Body.List, &ast.ReturnStmt{Results: returnExprs})
			}
		}
	}
	// mark as updated
	if funcDecl.Doc == nil {
		funcDecl.Doc = &ast.CommentGroup{}
	}
	funcDecl.Doc.List = append(funcDecl.Doc.List, &ast.Comment{
		Slash: funcDecl.Pos() - 1,
		Text:  "// " + modificationMarker,
	})
	return pointIDs, nil
}

// InjectFuncPointBeforeCall injects monitoring points before call expressions that match the predicate.
// The predicate function is called for each CallExpr in the function body.
// If it returns true for inject, a state monitoring point is injected immediately before that call,
// and the returned metadata is associated with that point ID.
//
// The monitoring point captures only the arguments passed to the matched call, not all visible variables,
// to reduce memory overhead and focus on the specific data being passed to the function.
//
// Returns a map from point ID to caller-provided metadata for all injection points.
func (m *ASTModifier) InjectFuncPointBeforeCall(fn *Function, shouldInject func(*ast.CallExpr) (metadata any, inject bool)) (map[uint32]any, error) {
	lock := astFileLock.Lock(fn.FilePath)
	defer lock.Unlock()

	_, fileNode, err := m.loadParsedFileNode(fn.FilePath)
	if err != nil {
		return nil, err
	}
	funcDecl := findFuncDecl(fileNode, fn.PackageName, fn.FunctionIdent)
	if funcDecl == nil {
		return nil, fmt.Errorf("function %s not found in %s", fn.FunctionIdent, fn.FilePath)
	} else if funcDecl.Body == nil {
		return nil, fmt.Errorf("%w: %s in %s", ErrNoFunctionBody, fn.FunctionIdent, fn.FilePath)
	}
	filePackageNames := make(map[string]bool, len(fileNode.Imports))
	for _, imp := range fileNode.Imports {
		if imp.Name != nil {
			filePackageNames[imp.Name.Name] = true // Aliased import: import alias "path"
		} else { // else, regular import: extract package name from path
			path := strings.Trim(imp.Path.Value, `"`)
			if idx := strings.LastIndex(path, "/"); idx != -1 {
				filePackageNames[path[idx+1:]] = true
			} else {
				filePackageNames[path] = true
			}
		}
	}

	pointMap := make(map[uint32]any)
	var buf bytes.Buffer

	// Helper to find a matching call in a node, returns the call and its metadata if found.
	// Does NOT descend into function literals - they have their own scope and are processed
	// separately via rewriteFuncLitsIn to avoid extracting variables from the wrong scope.
	findMatchingCall := func(node ast.Node) (*ast.CallExpr, any) {
		var matchedCall *ast.CallExpr
		var metadata any
		ast.Inspect(node, func(n ast.Node) bool {
			// Don't descend into function literals - they have their own scope
			// and will be processed separately via rewriteFuncLitsIn
			if _, isFuncLit := n.(*ast.FuncLit); isFuncLit {
				return false
			}
			if call, ok := n.(*ast.CallExpr); ok {
				if m, inject := shouldInject(call); inject {
					matchedCall = call
					metadata = m
					return false
				}
			}
			return true
		})
		return matchedCall, metadata
	}

	var rewriteBlock func(*ast.BlockStmt) error

	// Helper to find and recurse into all FuncLit bodies in a node.
	// This ensures we instrument calls inside function literals while keeping
	// the instrumentation in the correct scope (inside the FuncLit body).
	rewriteFuncLitsIn := func(node ast.Node) error {
		var firstErr error
		ast.Inspect(node, func(n ast.Node) bool {
			if firstErr != nil {
				return false
			}
			if fl, ok := n.(*ast.FuncLit); ok {
				if fl.Body != nil {
					if err := rewriteBlock(fl.Body); err != nil {
						firstErr = err
						return false
					}
				}
				return false // Don't descend further into this FuncLit (we just processed it)
			}
			return true
		})
		return firstErr
	}

	rewriteBlock = func(blk *ast.BlockStmt) error {
		newStmts := make([]ast.Stmt, 0, len(blk.List))
		for _, st := range blk.List {
			if isPrevStmtSendLensPoint(newStmts, len(newStmts)) { // Skip if already instrumented
				newStmts = append(newStmts, st)
				continue
			}

			// Check if this statement contains a matching call (excluding nested blocks)
			var matchedCall *ast.CallExpr
			var metadata any
			switch stmt := st.(type) {
			case *ast.ExprStmt:
				matchedCall, metadata = findMatchingCall(stmt.X)
			case *ast.AssignStmt:
				matchedCall, metadata = findMatchingCall(stmt)
			case *ast.ReturnStmt:
				matchedCall, metadata = findMatchingCall(stmt)
			case *ast.DeferStmt:
				if metadata, inject := shouldInject(stmt.Call); inject {
					// Special handling for defer: wrap in inline function to preserve semantics
					pointID, err := m.nextPointId()
					if err != nil {
						return err
					}
					pointMap[pointID] = metadata

					// Build instrumentation for the deferred call
					preStmts, err := buildCallInstrumentationWithArgs(&buf, pointID, stmt.Call, filePackageNames)
					if err != nil {
						return err
					}

					// Wrap in inline function: defer func() { preStmts...; call }()
					blockList := make([]ast.Stmt, 0, len(preStmts)+1)
					blockList = append(blockList, preStmts...)
					// Add the call as the last statement (already modified by buildCallInstrumentationWithArgs)
					blockList = append(blockList, &ast.ExprStmt{X: stmt.Call})

					// Replace the defer's call with the inline function
					stmt.Call = &ast.CallExpr{
						Fun: &ast.FuncLit{
							Type: &ast.FuncType{Params: &ast.FieldList{}},
							Body: &ast.BlockStmt{List: blockList},
						},
					}

					// Recurse into any FuncLits in the preStmts (extracted arguments).
					// These contain FuncLits from the original call arguments that may have
					// target calls inside them. We do this here rather than using
					// rewriteFuncLitsIn on the whole statement to avoid re-instrumenting
					// the call we just wrapped.
					for _, preStmt := range preStmts {
						if err := rewriteFuncLitsIn(preStmt); err != nil {
							return err
						}
					}

					newStmts = append(newStmts, st)
					continue // Skip rewriteFuncLitsIn on the whole statement
				}
			case *ast.GoStmt:
				if metadata, inject := shouldInject(stmt.Call); inject {
					// Same transformation as DeferStmt
					pointID, err := m.nextPointId()
					if err != nil {
						return err
					}
					pointMap[pointID] = metadata

					preStmts, err := buildCallInstrumentationWithArgs(&buf, pointID, stmt.Call, filePackageNames)
					if err != nil {
						return err
					}

					blockList := make([]ast.Stmt, 0, len(preStmts)+1)
					blockList = append(blockList, preStmts...)
					blockList = append(blockList, &ast.ExprStmt{X: stmt.Call})

					stmt.Call = &ast.CallExpr{
						Fun: &ast.FuncLit{
							Type: &ast.FuncType{Params: &ast.FieldList{}},
							Body: &ast.BlockStmt{List: blockList},
						},
					}

					// Recurse into any FuncLits in the preStmts (same as DeferStmt)
					for _, preStmt := range preStmts {
						if err := rewriteFuncLitsIn(preStmt); err != nil {
							return err
						}
					}

					newStmts = append(newStmts, st)
					continue // Skip rewriteFuncLitsIn on the whole statement
				}
			case *ast.DeclStmt:
				// Handle var x = call()
				matchedCall, metadata = findMatchingCall(stmt)
			case *ast.SendStmt:
				// Handle ch <- call()
				matchedCall, metadata = findMatchingCall(stmt.Value)
			case *ast.IfStmt:
				// Handle if x := call(); condition and if call() { }
				if stmt.Init != nil {
					matchedCall, metadata = findMatchingCall(stmt.Init)
				}
				if matchedCall == nil && stmt.Cond != nil {
					matchedCall, metadata = findMatchingCall(stmt.Cond)
				}
			case *ast.ForStmt:
				// Handle for i := call(); condition; post
				if stmt.Init != nil {
					matchedCall, metadata = findMatchingCall(stmt.Init)
				}
				if matchedCall == nil && stmt.Cond != nil {
					matchedCall, metadata = findMatchingCall(stmt.Cond)
				}
				// Post statement handled separately in recursion section
			case *ast.RangeStmt:
				// Handle for x := range call()
				matchedCall, metadata = findMatchingCall(stmt.X)
			case *ast.SwitchStmt:
				// Handle switch x := call(); x and switch call() { }
				if stmt.Init != nil {
					matchedCall, metadata = findMatchingCall(stmt.Init)
				}
				if matchedCall == nil && stmt.Tag != nil {
					matchedCall, metadata = findMatchingCall(stmt.Tag)
				}
			case *ast.TypeSwitchStmt:
				// Handle switch x := call().(type) and switch call().(type) { }
				if stmt.Init != nil {
					matchedCall, metadata = findMatchingCall(stmt.Init)
				}
				if matchedCall == nil {
					matchedCall, metadata = findMatchingCall(stmt.Assign)
				}
			case *ast.SelectStmt:
				// Handle select { case ch <- call(): ... }
				// Check all comm clauses
				for _, commStmt := range stmt.Body.List {
					if cc, ok := commStmt.(*ast.CommClause); ok && cc.Comm != nil {
						matchedCall, metadata = findMatchingCall(cc.Comm)
						if matchedCall != nil {
							break
						}
					}
				}
			}

			if matchedCall != nil {
				pointID, err := m.nextPointId()
				if err != nil {
					return err
				}
				pointMap[pointID] = metadata

				preStmts, err := buildCallInstrumentationWithArgs(&buf, pointID, matchedCall, filePackageNames)
				if err != nil {
					return err
				}

				// Append instrumentation statements directly to maintain variable scope
				// Do not wrap in a block as this would scope any variables declared in st
				newStmts = append(newStmts, preStmts...)
				newStmts = append(newStmts, st)
			} else {
				newStmts = append(newStmts, st)
			}

			// Recursively process nested blocks
			switch s := st.(type) {
			case *ast.BlockStmt:
				if err := rewriteBlock(s); err != nil {
					return err
				}
			case *ast.IfStmt:
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
				if s.Else != nil {
					switch e := s.Else.(type) {
					case *ast.BlockStmt:
						if err := rewriteBlock(e); err != nil {
							return err
						}
					case *ast.IfStmt:
						if err := rewriteBlock(e.Body); err != nil {
							return err
						}
					}
				}
			case *ast.ForStmt:
				// If Post contains a matching call, wrap it so temps stay in scope per iteration
				if s.Post != nil {
					if postCall, postMetadata := findMatchingCall(s.Post); postCall != nil {
						pointID, err := m.nextPointId()
						if err != nil {
							return err
						}
						pointMap[pointID] = postMetadata
						preStmts, err := buildCallInstrumentationWithArgs(&buf, pointID, postCall, filePackageNames)
						if err != nil {
							return err
						}

						origPost := s.Post
						blockList := append(make([]ast.Stmt, 0, len(preStmts)+1), preStmts...)
						blockList = append(blockList, origPost)
						s.Post = &ast.ExprStmt{
							X: &ast.CallExpr{
								Fun: &ast.FuncLit{
									Type: &ast.FuncType{Params: &ast.FieldList{}},
									Body: &ast.BlockStmt{List: blockList},
								},
							},
						}
					}
				}
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
			case *ast.RangeStmt:
				if err := rewriteBlock(s.Body); err != nil {
					return err
				}
			case *ast.SwitchStmt:
				for _, stmt := range s.Body.List {
					if cc, ok := stmt.(*ast.CaseClause); ok {
						blk := &ast.BlockStmt{List: cc.Body}
						if err := rewriteBlock(blk); err != nil {
							return err
						}
						cc.Body = blk.List
					}
				}
			case *ast.TypeSwitchStmt:
				for _, stmt := range s.Body.List {
					if cc, ok := stmt.(*ast.CaseClause); ok {
						blk := &ast.BlockStmt{List: cc.Body}
						if err := rewriteBlock(blk); err != nil {
							return err
						}
						cc.Body = blk.List
					}
				}
			case *ast.SelectStmt:
				for _, stmt := range s.Body.List {
					if cc, ok := stmt.(*ast.CommClause); ok {
						blk := &ast.BlockStmt{List: cc.Body}
						if err := rewriteBlock(blk); err != nil {
							return err
						}
						cc.Body = blk.List
					}
				}
			}

			// Recurse into any function literals in this statement.
			// This handles cases like: callback := func(x) { target(x) }
			// where target() should be instrumented inside the FuncLit's scope.
			if err := rewriteFuncLitsIn(st); err != nil {
				return err
			}
		}
		blk.List = newStmts
		return nil
	}

	if err := rewriteBlock(funcDecl.Body); err != nil {
		return nil, fmt.Errorf("ast rewrite failure %s: %w", fn.FilePath, err)
	}

	return pointMap, nil
}

// buildCallInstrumentationWithArgs creates a statement that sends the call's receiver (if any) and argument values to the monitoring server.
// This reduces memory overhead by capturing only the parameters passed to the call rather than all visible variables.
//
// For method calls like obj.Method(args), the receiver (obj) is captured.
// For complex receiver expressions like (&Foo{}).Method(args), a synthetic receiver variable is created.
// Package function calls like fmt.Printf() do not capture the package identifier.
//
// All arguments are captured as synthetic variables (lenSyntheticArg<pointID>_<i>) to ensure uniqueness
// when multiple calls are instrumented in the same function, but display as arg0, arg1, arg2, etc.
//
// Note: In Go's AST, variadic arguments with ... (e.g., append(slice, elements...)) are represented with
// CallExpr.Ellipsis field set to the position of the ... token, not as an ast.Ellipsis node in the Args.
// The arguments themselves are just regular expressions, so we capture them as-is.
func buildCallInstrumentationWithArgs(buf *bytes.Buffer, pointID uint32, call *ast.CallExpr, filePackageNames map[string]bool) ([]ast.Stmt, error) {
	// Build snapshots for receiver (if any) and the call's arguments
	snaps := make([]ast.Expr, 0, len(call.Args)+1)
	stmts := make([]ast.Stmt, 0, len(call.Args)+2)

	// Check if this is a method call (has a receiver)
	if sel, ok := call.Fun.(*ast.SelectorExpr); ok && sel.X != nil {
		// sel.X is the receiver expression
		if ident, isSimpleIdent := sel.X.(*ast.Ident); isSimpleIdent {
			// Simple identifier like obj.Method() or fmt.Printf()
			// Only capture if it's receiver, not an imported package
			if ident.Name != "_" && !filePackageNames[ident.Name] {
				snaps = append(snaps, makeSnapshotLit(ident.Name, ident))
			}
		} else {
			// Complex receiver expression like (&Foo{}).Method() or outer.inner.Method()
			// Create a synthetic receiver variable with unique name using pointID
			recvVarName := fmt.Sprintf("%s%d", syntheticFieldNamePrefixReceiver, pointID)
			recvIdent := ast.NewIdent(recvVarName)
			origRecv := sel.X
			stmts = append(stmts, &ast.AssignStmt{
				Lhs: []ast.Expr{recvIdent},
				Tok: token.DEFINE,
				Rhs: []ast.Expr{origRecv},
			})
			// Create a new SelectorExpr with the synthetic receiver instead of modifying the original
			// to avoid position-related formatting issues. Use a fresh Sel identifier with no position.
			call.Fun = &ast.SelectorExpr{
				X:   recvIdent,
				Sel: ast.NewIdent(sel.Sel.Name),
			}
			snaps = append(snaps, makeSnapshotLitWithCustomName("recv", recvIdent))
		}
	}

	// Build snapshots for the call's arguments
	for i := range call.Args {
		origArg := call.Args[i]

		// Identifiers: snapshot directly, no temp needed
		if ident, ok := origArg.(*ast.Ident); ok {
			snaps = append(snaps, makeSnapshotLitWithCustomName(fmt.Sprintf("arg%d", i), ident))
			continue
		}

		// SelectorExpr (pkg.Const or obj.Field): capture but don't replace
		// These often involve implicit type conversions (e.g., syscall.SYS_IOCTL -> uintptr)
		if sel, ok := origArg.(*ast.SelectorExpr); ok {
			snaps = append(snaps, makeSnapshotLitWithCustomName(fmt.Sprintf("arg%d", i), sel))
			continue
		}

		// BasicLit: capture value without creating temp (preserve untyped semantics)
		if lit, ok := origArg.(*ast.BasicLit); ok {
			snaps = append(snaps, makeSnapshotLitWithCustomName(fmt.Sprintf("arg%d", i), lit))
			// Don't create synthetic variable - just use the literal directly
			// This preserves untyped constant semantics
			continue
		}

		// Complex expressions: create synthetic variable and replace
		argVarName := fmt.Sprintf("%s%d_%d", syntheticFieldNamePrefixArg, pointID, i)
		argIdent := ast.NewIdent(argVarName)
		stmts = append(stmts, &ast.AssignStmt{
			Lhs: []ast.Expr{argIdent},
			Tok: token.DEFINE,
			Rhs: []ast.Expr{origArg},
		})
		call.Args[i] = argIdent
		snaps = append(snaps, makeSnapshotLitWithCustomName(fmt.Sprintf("arg%d", i), argIdent))
	}

	sendStmt, err := makeSendLensPointStateMessageStmt(buf, pointID, snaps)
	if err != nil {
		return nil, err
	}
	stmts = append(stmts, sendStmt)
	return stmts, nil
}

type declInfo struct {
	ident *ast.Ident
	pos   token.Pos
}

// buildTypesInfo attempts to type-check *all* Go files that belong to the same
// package as targetFile.  On any failure it returns nil so callers can fall
// back to a syntactic scan.
func buildTypesInfo(fset *token.FileSet, targetFile *ast.File) *types.Info {
	// Locate the directory that contains the target file
	targetPos := fset.File(targetFile.Pos())
	if targetPos == nil {
		return nil
	}
	dir := filepath.Dir(targetPos.Name())

	pkgs, err := parser.ParseDir(fset, dir, makeFileFilter(dir), 0)
	if err != nil || len(pkgs) == 0 {
		return nil
	}
	// There should be exactly one non-test package in this directory
	pkgFiles := bulk.MapValuesSlice(pkgs[targetFile.Name.Name].Files)
	files := make([]*ast.File, 0, len(pkgFiles))
	targetPath := fset.File(targetFile.Pos()).Name()
	for _, f := range pkgFiles {
		if fset.File(f.Pos()).Name() == targetPath {
			files = append(files, targetFile) // reuse parsed node so pointer matches
		} else {
			files = append(files, f)
		}
	}

	info := &types.Info{
		Defs:  make(map[*ast.Ident]types.Object),
		Uses:  make(map[*ast.Ident]types.Object),
		Types: make(map[ast.Expr]types.TypeAndValue),
	}
	cfg := &types.Config{
		Importer: importer.Default(),
		Error:    func(error) {}, // ignore type errors – we’ll fall back on any failure
	}
	if _, err := cfg.Check("", fset, files, info); err != nil {
		return nil
	}
	return info
}

// isPrevStmtSendLensPoint checks if the previous statement in the slice (at idx-1)
// is a SendLensPointStateMessage call, indicating that the current statement
// has already been instrumented.
func isPrevStmtSendLensPoint(stmts []ast.Stmt, idx int) bool {
	if idx == 0 {
		return false
	}
	prev := stmts[idx-1]
	exprStmt, ok := prev.(*ast.ExprStmt)
	if !ok {
		return false
	}
	call, ok := exprStmt.X.(*ast.CallExpr)
	if !ok {
		return false
	}
	ident, ok := call.Fun.(*ast.Ident)
	return ok && ident.Name == "sendLensPointStateMessage"
}

// visibleDeclsBefore collects visible identifiers before retPos using a syntactic scan.
func visibleDeclsBefore(fn *ast.FuncDecl, retPos token.Pos) []declInfo {
	if fn == nil {
		return nil
	}
	latest := make(map[string]declInfo)
	addIdent := func(id *ast.Ident) {
		if id == nil || id.Name == "_" || id.Pos() > retPos {
			return
		} else if cur, ok := latest[id.Name]; !ok || id.Pos() > cur.pos {
			latest[id.Name] = declInfo{id, id.Pos()}
		}
	}

	// params & named results are always in scope
	if fn.Type.Params != nil {
		for _, f := range fn.Type.Params.List {
			for _, id := range f.Names {
				addIdent(id)
			}
		}
	}
	if fn.Type.Results != nil {
		for _, f := range fn.Type.Results.List {
			for _, id := range f.Names {
				addIdent(id)
			}
		}
	}

	// walk body until retPos – prune sub-trees that start after retPos
	ast.Inspect(fn.Body, func(n ast.Node) bool {
		if n == nil {
			return true
		}

		// If a block-like node ends before retPos, nothing inside it is visible
		switch n.(type) {
		case *ast.BlockStmt, *ast.IfStmt, *ast.ForStmt, *ast.RangeStmt,
			*ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.CaseClause:
			if n.End() < retPos {
				return false // prune subtree
			}
		}

		switch v := n.(type) {
		case *ast.ValueSpec:
			for _, id := range v.Names {
				addIdent(id)
			}
		case *ast.AssignStmt:
			if v.Tok == token.DEFINE {
				for _, lhs := range v.Lhs {
					if id, ok := lhs.(*ast.Ident); ok {
						addIdent(id)
					}
				}
			}
		case *ast.RangeStmt:
			if v.Tok == token.DEFINE {
				if id, ok := v.Key.(*ast.Ident); ok {
					addIdent(id)
				}
				if id, ok := v.Value.(*ast.Ident); ok {
					addIdent(id)
				}
			}
		}
		return true
	})

	result := bulk.MapValuesSlice(latest)
	slices.SortFunc(result, func(a, b declInfo) int {
		return cmp.Compare(a.pos, b.pos)
	})
	return result
}

// buildReturnInstrumentation inserts instrumentation around an explicit return. All nodes that originate
// in the project source are first cloned with their positions stripped, so the generated block is position-clean.
func buildReturnInstrumentation(buf *bytes.Buffer, ret *ast.ReturnStmt, pointID uint32, fn *Function,
	decls []declInfo, funcResultTypes []ast.Expr, info *types.Info, funcResultNames []string) (*ast.BlockStmt, error) {
	// helper to make identifiers
	ident := func(name string) *ast.Ident { return ast.NewIdent(name) }

	// collect snapshots of all visible locals
	snaps := make([]ast.Expr, 0, len(decls)+max(len(ret.Results), len(funcResultTypes)))
	seen := make(map[string]bool, len(decls)+len(ret.Results))
	for _, d := range decls {
		if d.ident.Name == literalNil || seen[d.ident.Name] {
			continue
		}
		seen[d.ident.Name] = true
		snaps = append(snaps, makeSnapshotLit(d.ident.Name, ident(d.ident.Name)))
	}

	// prepare lists for temp assignments and final return values
	preStmts := make([]ast.Stmt, 0, 1+len(ret.Results))
	var newResults []ast.Expr
	allNamed := len(funcResultNames) > 0 && !slices.Contains(funcResultNames, "")
	if len(ret.Results) == 0 && allNamed {
		hasBlankReturn := false
		for _, name := range funcResultNames {
			// Skip blank identifiers - they can't be used as values
			if name == "_" {
				hasBlankReturn = true
				continue
			}
			id := ident(name)
			if !seen[name] {
				snaps = append(snaps, makeSnapshotLit(name, id))
				seen[name] = true
			}
			newResults = append(newResults, id)
		}
		sendStmt, err := makeSendLensPointStateMessageStmt(buf, pointID, snaps)
		if err != nil {
			return nil, err
		}
		// If any return is a blank identifier, use bare return to preserve semantics
		retStmt := &ast.ReturnStmt{Results: newResults}
		if hasBlankReturn {
			retStmt = &ast.ReturnStmt{}
		}
		return &ast.BlockStmt{
			List: append(append(preStmts, sendStmt), retStmt),
		}, nil
	}
	// special-case: one CallExpr returning multiple values
	if len(ret.Results) == 1 {
		if call, ok := ret.Results[0].(*ast.CallExpr); ok && len(funcResultTypes) > 1 {
			// make temporaries lenSyntheticRet0, lenSyntheticRet1, etc
			temps := make([]ast.Expr, len(funcResultTypes))
			for i := range funcResultTypes {
				tmpName := fmt.Sprintf("%s%d", syntheticFieldNamePrefixReturn, i)
				tmpId := ident(tmpName)
				temps[i] = tmpId
				snaps = append(snaps, makeSnapshotLit(tmpName, tmpId))
			}
			// tmp0, tmp1, … := <orig call>
			rhs, err := cloneExprNoPos(buf, call)
			if err != nil {
				return nil, err
			}
			preStmts = append(preStmts, &ast.AssignStmt{
				Lhs: temps,
				Tok: token.DEFINE,
				Rhs: []ast.Expr{rhs},
			})
			newResults = append(newResults, temps...)

			sendStmt, err := makeSendLensPointStateMessageStmt(buf, pointID, snaps)
			if err != nil {
				return nil, err
			}
			return &ast.BlockStmt{
				List: append(
					append(preStmts, sendStmt),
					&ast.ReturnStmt{Results: newResults},
				),
			}, nil
		}
	}

	// default: handle each returned expr in isolation
	for i, expr := range ret.Results {
		prefix := syntheticFieldNamePrefixReturn
		if isRecursiveCall(expr, fn.FunctionName) {
			prefix = syntheticFieldNamePrefixRecursive
		}

		switch e := expr.(type) {
		case *ast.Ident:
			var needTmp bool
			if info != nil {
				if et := info.TypeOf(e); et != nil {
					switch t := et.(type) {
					case *types.Basic:
						needTmp = t.Info()&types.IsUntyped != 0
					case *types.Named:
						needTmp = t.Obj().IsAlias()
					case *types.Alias, *types.TypeParam:
						needTmp = true
					}
				}
				if rt := info.TypeOf(funcResultTypes[i]); rt != nil {
					if _, ok := rt.Underlying().(*types.Interface); ok {
						needTmp = true
					}
				}
			} else {
				switch rt := funcResultTypes[i].(type) {
				case *ast.InterfaceType:
					needTmp = true
				case *ast.Ident:
					if rt.Obj == nil && strings.ToUpper(rt.Name) == rt.Name {
						needTmp = true
					} else if rt.Obj != nil {
						if _, ok := rt.Obj.Decl.(*ast.Field); ok {
							needTmp = true
						}
					}
				}
			}
			if needTmp {
				typ, err := cloneExprNoPos(buf, funcResultTypes[i])
				if err != nil {
					return nil, err
				}
				retId, stmts, snap := makeReturnTemp(prefix, i, ident(e.Name), typ)
				preStmts = append(preStmts, stmts...)
				newResults = append(newResults, retId)
				snaps = append(snaps, snap)
				seen[retId.Name] = true
			} else {
				id := ident(e.Name)
				if !seen[e.Name] && e.Name != literalNil {
					snaps = append(snaps, makeSnapshotLit(e.Name, id))
					seen[e.Name] = true
				}
				newResults = append(newResults, id)
			}
		case *ast.BasicLit:
			// decide whether we really need a tmp for interface conversions
			var needTmp bool
			if info != nil {
				if rt := info.TypeOf(funcResultTypes[i]); rt != nil {
					if _, ok := rt.Underlying().(*types.Interface); ok {
						needTmp = true
					}
				}
			} else if _, ok := funcResultTypes[i].(*ast.InterfaceType); ok {
				needTmp = true
			}

			// prepare the return‐value identifier and the literal
			retName := fmt.Sprintf("%s%d", prefix, i)
			retId := ident(retName)
			lit, err := cloneExprNoPos(buf, e)
			if err != nil {
				return nil, err
			}

			if needTmp {
				typ, err := cloneExprNoPos(buf, funcResultTypes[i])
				if err != nil {
					return nil, err
				}
				rid, stmts, snap := makeReturnTemp(prefix, i, lit, typ)
				retId = rid
				preStmts = append(preStmts, stmts...)
				snaps = append(snaps, snap)
			} else {
				// var retX T = <lit>
				typ, err := cloneExprNoPos(buf, funcResultTypes[i])
				if err != nil {
					return nil, err
				}
				preStmts = append(preStmts,
					&ast.DeclStmt{Decl: &ast.GenDecl{
						Tok: token.VAR,
						Specs: []ast.Spec{&ast.ValueSpec{
							Names:  []*ast.Ident{retId},
							Type:   typ,
							Values: []ast.Expr{lit},
						}},
					}},
				)
			}

			// common tail: record the snapshot and return value
			newResults = append(newResults, retId)
			if needTmp {
				seen[retId.Name] = true
			} else {
				snaps = append(snaps, makeSnapshotLit(retName, retId))
				seen[retName] = true
			}
		default:
			expr, err := cloneExprNoPos(buf, expr)
			if err != nil {
				return nil, err
			}
			typ, err := cloneExprNoPos(buf, funcResultTypes[i])
			if err != nil {
				return nil, err
			}
			retId, stmts, snap := makeReturnTemp(prefix, i, expr, typ)
			preStmts = append(preStmts, stmts...)
			newResults = append(newResults, retId)
			snaps = append(snaps, snap)
			seen[retId.Name] = true
		}
	}

	// Build instrumentation call using snippet-parsing
	sendStmt, err := makeSendLensPointStateMessageStmt(buf, pointID, snaps)
	if err != nil {
		return nil, err
	}

	return &ast.BlockStmt{
		List: append(append(preStmts, sendStmt), &ast.ReturnStmt{Results: newResults}),
	}, nil
}

// zeroValueForType generates a zero value AST expression for the given type expression.
// buf is used for cloning type expressions when needed.
func zeroValueForType(buf *bytes.Buffer, typ ast.Expr) (ast.Expr, error) {
	switch t := typ.(type) {
	case *ast.Ident:
		switch t.Name {
		// Numeric types
		case "int", "int8", "int16", "int32", "int64",
			"uint", "uint8", "uint16", "uint32", "uint64", "uintptr",
			"float32", "float64", "complex64", "complex128", "byte", "rune":
			return &ast.BasicLit{Kind: token.INT, Value: "0"}, nil
		case "bool":
			return ast.NewIdent("false"), nil
		case "string":
			return &ast.BasicLit{Kind: token.STRING, Value: `""`}, nil
		case "error":
			// error is an interface
			return ast.NewIdent("nil"), nil
		case "_":
			// Blank identifier cannot be used as a value
			// This shouldn't happen since we filter out blank identifiers earlier
			// But if it does, return nil as a safe default
			return ast.NewIdent("nil"), nil
		default:
			// For named types, we face a dilemma:
			// - We can't use *new(T) as it might conflict with package names
			// - We can't use (T){} as Go doesn't allow parenthesized types in composite literals
			// - We can't use T(0) as it only works for numeric types
			//
			// Best compromise: Use T{} and accept that it might fail for types
			// that conflict with package names. This is relatively rare and the
			// compilation error will be clear when it happens.
			clonedType, err := cloneExprNoPos(buf, t)
			if err != nil {
				return nil, err
			}
			return &ast.CompositeLit{Type: clonedType}, nil
		}

	// Pointer, map, channel, function, and interface types all have nil zero value
	case *ast.StarExpr,
		*ast.MapType,
		*ast.ChanType,
		*ast.FuncType,
		*ast.InterfaceType:
		return ast.NewIdent("nil"), nil

	case *ast.ArrayType:
		// In the go/ast package, *ast.ArrayType represents both arrays and slices:
		// Len == nil => slice type ([]T), Len != nil => array type ([N]T).
		if t.Len == nil {
			// Slice type: zero value is nil.
			return ast.NewIdent("nil"), nil
		}
		// Array type: zero value is [N]T{}.
		clonedType, err := cloneExprNoPos(buf, t)
		if err != nil {
			return nil, err
		}
		return &ast.CompositeLit{Type: clonedType}, nil

	case *ast.StructType:
		// Anonymous struct: struct{...}{}.
		clonedType, err := cloneExprNoPos(buf, t)
		if err != nil {
			return nil, err
		}
		return &ast.CompositeLit{Type: clonedType}, nil

	case *ast.SelectorExpr:
		// pkg.Type - use composite literal
		clonedType, err := cloneExprNoPos(buf, t)
		if err != nil {
			return nil, err
		}
		return &ast.CompositeLit{Type: clonedType}, nil

	case *ast.IndexExpr:
		// Generic type with single param: T[U] - use *new(T[U])
		clonedType, err := cloneExprNoPos(buf, t)
		if err != nil {
			return nil, err
		}
		return &ast.StarExpr{X: &ast.CallExpr{
			Fun:  ast.NewIdent("new"),
			Args: []ast.Expr{clonedType},
		}}, nil

	case *ast.IndexListExpr:
		// Generic type with multiple params: T[K, V] - use *new(T[K,V])
		clonedType, err := cloneExprNoPos(buf, t)
		if err != nil {
			return nil, err
		}
		return &ast.StarExpr{X: &ast.CallExpr{
			Fun:  ast.NewIdent("new"),
			Args: []ast.Expr{clonedType},
		}}, nil

	default:
		// Fallback: use composite literal for any type
		clonedType, err := cloneExprNoPos(buf, typ)
		if err != nil {
			return nil, err
		}
		return &ast.CompositeLit{Type: clonedType}, nil
	}
}

// cloneExprNoPos is a helper to clone an AST, dropping positions.
func cloneExprNoPos(buf *bytes.Buffer, e ast.Node) (ast.Expr, error) {
	buf.Reset()
	err := format.Node(buf, token.NewFileSet(), e)
	if err != nil {
		return nil, err
	}
	return parser.ParseExprFrom(token.NewFileSet(), "", buf.Bytes(), 0)
}

func makeSendLensPointStateMessageStmt(buf *bytes.Buffer, pointID uint32, snaps []ast.Expr) (ast.Stmt, error) {
	// Convert all snapshot ASTs to source
	args := make([]string, 1, 1+len(snaps))
	args[0] = strconv.FormatUint(uint64(pointID), 10)
	for _, snap := range snaps {
		buf.Reset()
		if err := format.Node(buf, token.NewFileSet(), snap); err != nil {
			return nil, fmt.Errorf("failed to format snapshot: %w", err)
		}
		args = append(args, buf.String())
	}
	callSrc := fmt.Sprintf("sendLensPointStateMessage(%s)", strings.Join(args, ", "))
	expr, err := parser.ParseExpr(callSrc)
	if err != nil {
		return nil, fmt.Errorf("failed to parse instrumentation call: %w", err)
	}
	return &ast.ExprStmt{X: expr}, nil
}

// buildImplicitReturnInstrumentation creates a single ExprStmt that
// snapshots all live vars and calls SendLensPointStateMessage. It is used
// when the function has no explicit return
func buildImplicitReturnInstrumentation(buf *bytes.Buffer, pointID uint32, decls []declInfo) (ast.Stmt, error) {
	snaps := make([]ast.Expr, 0, len(decls))
	seen := make(map[string]bool, len(decls))
	for _, d := range decls {
		if d.ident.Name == literalNil || seen[d.ident.Name] {
			continue
		}
		seen[d.ident.Name] = true
		snaps = append(snaps, makeSnapshotLit(d.ident.Name, ast.NewIdent(d.ident.Name)))
	}
	return makeSendLensPointStateMessageStmt(buf, pointID, snaps)
}

const fieldKeyName = "Name"
const fieldKeyVal = "Val"

// makeSnapshotLit builds a *ast.CompositeLit representing a lensMonitorFieldSnapshot.
func makeSnapshotLit(name string, val ast.Expr) ast.Expr {
	// we use long field names to avoid conflicts, but want to communicate concise names
	if strings.HasPrefix(name, syntheticFieldNamePrefixReturn) {
		name = strings.Replace(name, syntheticFieldNamePrefixReturn, "ret", 1)
	} else if strings.HasPrefix(name, syntheticFieldNamePrefixRecursive) {
		name = strings.Replace(name, syntheticFieldNamePrefixRecursive, "rec", 1)
	} else if strings.HasPrefix(name, syntheticFieldNamePrefixArg) {
		name = strings.Replace(name, syntheticFieldNamePrefixArg, "arg", 1)
	} else if strings.HasPrefix(name, syntheticFieldNamePrefixReceiver) {
		name = strings.Replace(name, syntheticFieldNamePrefixReceiver, "recv", 1)
	}
	return &ast.CompositeLit{
		Type: ast.NewIdent("lensMonitorFieldSnapshot"),
		Elts: []ast.Expr{
			&ast.KeyValueExpr{
				Key:   ast.NewIdent(fieldKeyName),
				Value: &ast.BasicLit{Kind: token.STRING, Value: strconv.Quote(name)},
			},
			&ast.KeyValueExpr{
				Key:   ast.NewIdent(fieldKeyVal),
				Value: val,
			},
		},
	}
}

// makeSnapshotLitWithCustomName builds a *ast.CompositeLit with an explicit display name.
// Unlike makeSnapshotLit, this does not perform any prefix-based name transformations.
func makeSnapshotLitWithCustomName(displayName string, val ast.Expr) ast.Expr {
	return &ast.CompositeLit{
		Type: ast.NewIdent("lensMonitorFieldSnapshot"),
		Elts: []ast.Expr{
			&ast.KeyValueExpr{
				Key:   ast.NewIdent(fieldKeyName),
				Value: &ast.BasicLit{Kind: token.STRING, Value: strconv.Quote(displayName)},
			},
			&ast.KeyValueExpr{
				Key:   ast.NewIdent(fieldKeyVal),
				Value: val,
			},
		},
	}
}

// makeReturnTemp builds a temporary var, a typed ret var, and its snapshot.
func makeReturnTemp(namePrefix string, i int, expr ast.Expr, typ ast.Expr) (retId *ast.Ident, stmts []ast.Stmt, snap ast.Expr) {
	iStr := strconv.Itoa(i)
	retId = ast.NewIdent(namePrefix + iStr)
	if ident, ok := expr.(*ast.Ident); ok && ident.Name == literalNil {
		// nil requires explicit type
		stmts = []ast.Stmt{
			&ast.DeclStmt{Decl: &ast.GenDecl{Tok: token.VAR, Specs: []ast.Spec{
				&ast.ValueSpec{Names: []*ast.Ident{retId}, Type: typ, Values: []ast.Expr{expr}},
			}}},
		}
	} else {
		// Check if any identifier in expr might shadow a type name used in typ
		// Examples:
		// - expr = Ident("deviceFlowResponse"), typ = *deviceFlowResponse
		// - expr = UnaryExpr(&Ident("deviceFlowResponse")), typ = *deviceFlowResponse
		// - expr = SelectorExpr(obj.field), typ = *SomeType
		typeMightBeShadowed := exprContainsTypeShadow(expr, typ)

		tmpId := ast.NewIdent(syntheticFieldNamePrefixTemp + iStr)
		if typeMightBeShadowed {
			// Use := to avoid type shadowing issues
			stmts = []ast.Stmt{
				// tmpX := expr (use type inference to avoid shadowing)
				&ast.AssignStmt{
					Lhs: []ast.Expr{tmpId},
					Tok: token.DEFINE,
					Rhs: []ast.Expr{expr},
				},
				// retX := tmpX (use type inference)
				&ast.AssignStmt{
					Lhs: []ast.Expr{retId},
					Tok: token.DEFINE,
					Rhs: []ast.Expr{tmpId},
				},
			}
		} else {
			// Use var tmpX Type = expr to allow untyped constants to convert to named types
			stmts = []ast.Stmt{
				// var tmpX Type = expr (typed temp for monitoring, allows conversion)
				&ast.DeclStmt{Decl: &ast.GenDecl{Tok: token.VAR, Specs: []ast.Spec{
					&ast.ValueSpec{Names: []*ast.Ident{tmpId}, Type: typ, Values: []ast.Expr{expr}},
				}}},
				// var retX Type = tmpX (typed return variable)
				&ast.DeclStmt{Decl: &ast.GenDecl{Tok: token.VAR, Specs: []ast.Spec{
					&ast.ValueSpec{Names: []*ast.Ident{retId}, Type: typ, Values: []ast.Expr{tmpId}},
				}}},
			}
		}
	}
	snap = makeSnapshotLit(retId.Name, retId)
	return
}

// exprContainsTypeShadow checks if any identifier in expr might shadow a type name in typ.
// For example, if expr contains identifier "deviceFlowResponse" and typ is "*deviceFlowResponse",
// then a variable named "deviceFlowResponse" would shadow the type name.
func exprContainsTypeShadow(expr ast.Expr, typ ast.Expr) bool {
	// Collect all identifiers from the type expression
	typeIdents := make(map[string]bool)
	ast.Inspect(typ, func(n ast.Node) bool {
		if ident, ok := n.(*ast.Ident); ok {
			typeIdents[ident.Name] = true
		}
		return true
	})

	// Check if any identifier in expr matches a type identifier
	foundShadow := false
	ast.Inspect(expr, func(n ast.Node) bool {
		if ident, ok := n.(*ast.Ident); ok {
			if typeIdents[ident.Name] {
				foundShadow = true
				return false
			}
		}
		return true
	})

	return foundShadow
}

// isRecursiveCall reports whether expr is a direct call to the function itself.
func isRecursiveCall(expr ast.Expr, funcName string) bool {
	call, ok := expr.(*ast.CallExpr)
	if !ok {
		return false
	}

	switch fun := call.Fun.(type) {
	case *ast.Ident:
		return fun.Name == funcName // plain F(...)
	case *ast.SelectorExpr:
		return fun.Sel.Name == funcName // recv.F(...)  pkg.F(...)
	default:
		return false
	}
}

// InjectFuncPointEntry injects a sendLensPointMessage call at function entry for coverage tracking.
func (m *ASTModifier) InjectFuncPointEntry(fn *Function) (uint32, error) {
	return m.injectPoint(fn.FilePath, fn.PackageName, fn.FunctionIdent, func(body *ast.BlockStmt, pointID uint32) {
		// build sendLensPointMessage(pointID)
		stmt := &ast.ExprStmt{X: &ast.CallExpr{
			Fun:  ast.NewIdent("sendLensPointMessage"),
			Args: []ast.Expr{&ast.BasicLit{Kind: token.INT, Value: strconv.FormatUint(uint64(pointID), 10)}},
		}}
		body.List = append([]ast.Stmt{stmt}, body.List...)
	})
}

// InjectFuncPointFinish injects a deferred sendLensPointMessage call to track function completion.
func (m *ASTModifier) InjectFuncPointFinish(fn *Function) (uint32, error) {
	return m.injectPoint(fn.FilePath, fn.PackageName, fn.FunctionIdent, func(body *ast.BlockStmt, pointID uint32) {
		// build defer sendLensPointMessage(pointID)
		deferStmt := &ast.DeferStmt{Call: &ast.CallExpr{
			Fun:  ast.NewIdent("sendLensPointMessage"),
			Args: []ast.Expr{&ast.BasicLit{Kind: token.INT, Value: strconv.FormatUint(uint64(pointID), 10)}},
		}}
		body.List = append([]ast.Stmt{deferStmt}, body.List...)
	})
}

func findFuncDecl(f *ast.File, pkg, ident string) *ast.FuncDecl {
	var out *ast.FuncDecl
	ast.Inspect(f, func(n ast.Node) bool {
		if d, ok := n.(*ast.FuncDecl); ok && MakeFunctionIdent(pkg, d) == ident {
			out = d
			return false
		}
		return true
	})
	return out
}

// InsertFuncLines walks each source‐line of the given function and lets the caller
// insert an arbitrary comment (or other text) before any line.
// The callback returns three values:
//   - insertText: the text to insert above the current line (e.g. “// …”).  If empty, nothing will be inserted.
//   - keepGoing: true if we should continue processing subsequent lines.
func (m *ASTModifier) InsertFuncLines(fn *Function, cb func(i int, line string) (insertText string, keepGoing bool)) error {
	// lock and ensure any pending edits have been flushed
	lock := astFileLock.Lock(fn.FilePath)
	defer lock.Unlock()
	if err := m.commitFileInternal(fn.FilePath); err != nil {
		return err
	}

	data, err := os.ReadFile(fn.FilePath)
	if err != nil {
		return fmt.Errorf("read failure %s: %w", fn.FilePath, err)
	}
	fset := token.NewFileSet()
	fileNode, err := parser.ParseFile(fset, fn.FilePath, data, parser.ParseComments)
	if err != nil {
		return fmt.Errorf("ast parse failure %s: %w", fn.FilePath, err)
	}
	decl := findFuncDecl(fileNode, fn.PackageName, fn.FunctionIdent)
	if decl == nil {
		return fmt.Errorf("function %s not found in %s", fn.FunctionIdent, fn.FilePath)
	} else if decl.Body == nil {
		return fmt.Errorf("%w: %s in %s", ErrNoFunctionBody, fn.FunctionIdent, fn.FilePath)
	}
	funcStartLine := fset.Position(decl.Pos()).Line
	// determine which lines are "inside" the function body (exclude the braces themselves)
	bodyOpenLine := fset.Position(decl.Body.Lbrace).Line + 1  // first line after '{'
	bodyCloseLine := fset.Position(decl.Body.Rbrace).Line - 1 // last line before '}'
	lines := strings.Split(string(data), "\n")

	if bodyOpenLine > bodyCloseLine { // empty body or single line function like "func() {}"
		return nil
	}

	// classify every line inside the body
	codeLine := make([]bool, bodyCloseLine-bodyOpenLine+1) // false by default
	var sc scanner.Scanner
	sc.Init(fset.File(decl.Body.Pos()), data, nil, scanner.ScanComments)
	prevLine := bodyOpenLine
	for {
		pos, tok, lit := sc.Scan()
		if tok == token.EOF {
			break
		}
		lno := fset.Position(pos).Line
		if lno < bodyOpenLine || lno > bodyCloseLine {
			continue
		}
		if lno != prevLine {
			prevLine = lno
		}
		switch tok {
		case token.COMMENT:
			// skip comment-only lines
			// we don't want to explicitly set false here, code may have been witnessed on the line earlier
		case token.LBRACE, token.RBRACE, token.LPAREN, token.RPAREN, token.LBRACK, token.RBRACK:
			// don't mark pure braces, parentheses or brackets as code
		case token.STRING, token.CHAR:
			// if this literal spans multiple lines, skip all those lines
			if strings.Contains(lit, "\n") {
				continue
			}
			// single-line literal (foo := "str")
			codeLine[lno-bodyOpenLine] = true
		default:
			// any other token (IDENT, INT, VAR, etc), mark as code
			codeLine[lno-bodyOpenLine] = true
		}
	}

	// build new file contents
	out := append(make([]string, 0, len(lines)+len(codeLine)), lines[:bodyOpenLine-1]...) // copy everything before body
	indentOf := func(s string) string {
		i := strings.IndexFunc(s, func(r rune) bool { return r != ' ' && r != '\t' })
		if i <= 0 {
			return ""
		}
		return s[:i]
	}

	var bodyIdx int
	for lineNo := bodyOpenLine; lineNo <= bodyCloseLine; lineNo++ {
		srcLine := lines[lineNo-1]

		if codeLine[bodyIdx] {
			fullIdx := lineNo - funcStartLine
			insertText, cont := cb(fullIdx, srcLine)
			if insertText != "" {
				out = append(out, indentOf(srcLine)+insertText)
			}
			out = append(out, srcLine)
			if !cont {
				out = append(out, lines[lineNo:bodyCloseLine]...) // copy to the body close
				break
			}
		} else {
			out = append(out, srcLine)
		}
		bodyIdx++
	}

	// copy closing brace and the rest of the file
	out = append(out, lines[bodyCloseLine:]...)

	if err := m.backupOrigFile(fn.FilePath); err != nil {
		return err
	}
	return os.WriteFile(fn.FilePath, []byte(strings.Join(out, "\n")), 0644)
}
