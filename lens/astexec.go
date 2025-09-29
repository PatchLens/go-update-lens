package lens

import (
	"bytes"
	"context"
	"crypto/sha1"
	"errors"
	"fmt"
	"io"
	"log"
	"maps"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/go-analyze/bulk"
	"golang.org/x/sync/errgroup"

	"github.com/mtraver/base91"
	"github.com/vmihailenco/msgpack/v5"
)

const (
	nonStringHashSizeLimit = 128
	HashFieldValuePrefix   = "vsha1-"
	monitorDebugLogging    = false
	testPassStr            = "Pass"
	testFailStr            = "FAIL"
)

// RunModuleUpdateAnalysis modifies the project and modules AST to include hooks for calls into the AST client.
// Our astServer accepts these calls, and invokes back into our code here so that we can analyze the project execution.
func RunModuleUpdateAnalysis(gopath, gomodcache, projectDir string, portStart int,
	storage Storage, maxVariableRecurse, maxFieldLen int, // values impact memory usage
	changedModules []ModuleChange, reachableModuleChanges ReachableModuleChange,
	callingFunctions []*CallerFunction, testFunctions []*TestFunction) (int, int, Storage, Storage, error) {
	env := GoEnv(gopath, gomodcache)

	if err := goCacheClean(env); err != nil { // will be cleaned at the end of each analysis also
		return 0, 0, nil, nil, fmt.Errorf("failure to clean go cache: %w", err)
	}

	// start ast monitor servers once to be reused across tests
	serverCount := min(runtime.NumCPU()/2, len(testFunctions), 64)
	srvChan := make(chan *astServer, serverCount)
	srvs := make([]*astServer, 0, serverCount)
	defer func() { // set defer here so errors while starting will stop constructed servers
		for _, s := range srvs {
			ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
			_ = s.Stop(ctx)
			cancel()
		}
	}()
	for i := 0; i < serverCount; i++ {
		srv, err := astExecServerStart(lensMonitorServerHost, portStart+i, nil)
		if err != nil {
			return 0, 0, nil, nil, err
		}
		srvs = append(srvs, srv)
		srvChan <- srv
	}

	// capture stable field values before update
	preStorage := KeyPrefixStorage(storage, "pre")
	projectFieldChecks1, moduleChangesReached, err :=
		runMonitoredTestAnalysis(env, maxVariableRecurse, maxFieldLen, srvChan, gopath, projectDir,
			nil, preStorage,
			slices.Collect(maps.Values(reachableModuleChanges)), callingFunctions, testFunctions)
	if err != nil {
		return projectFieldChecks1, moduleChangesReached, nil, nil, err
	}

	// backup all go.mod/go.sum files then perform module update in each module directory
	goModPaths, err := ProjectGoModFiles(projectDir)
	if err != nil {
		return projectFieldChecks1, moduleChangesReached, preStorage, nil, err
	}

	type modBackupInfo struct {
		modPath string
		sumPath string
		modBkp  string
		sumBkp  string
	}
	backups := make([]modBackupInfo, 0, len(goModPaths))
	for _, gm := range goModPaths {
		sum := filepath.Join(filepath.Dir(gm), "go.sum")
		info := modBackupInfo{modPath: gm, modBkp: gm + ".bkp"}
		if err := CopyFile(gm, info.modBkp); err != nil {
			return projectFieldChecks1, moduleChangesReached, preStorage, nil,
				fmt.Errorf("backup go.mod failed: %w", err)
		}
		if FileExists(sum) {
			info.sumPath = sum
			info.sumBkp = sum + ".bkp"
			if err := CopyFile(sum, info.sumBkp); err != nil {
				return projectFieldChecks1, moduleChangesReached, preStorage, nil,
					fmt.Errorf("backup go.sum failed: %w", err)
			}
		}
		backups = append(backups, info)
	}

	for _, gm := range goModPaths {
		modDir := filepath.Dir(gm)
		for _, cm := range changedModules {
			getCmd := NewProjectLoggedExec(modDir, env, "go", "get",
				fmt.Sprintf("%s@%s", cm.Name, cm.NewVersion))
			if err := getCmd.Run(); err != nil {
				return projectFieldChecks1, moduleChangesReached, preStorage, nil,
					fmt.Errorf("module update failed: %w", err)
			}
		}
		tidyCmd := NewProjectLoggedExec(modDir, env, "go", "mod", "tidy")
		if err := tidyCmd.Run(); err != nil {
			return projectFieldChecks1, moduleChangesReached, preStorage, nil,
				fmt.Errorf("module update tidy failed: %w", err)
		}
	}

	// capture stable fields after module update
	postStorage := KeyPrefixStorage(storage, "post")
	projectFieldChecks2, _, err :=
		runMonitoredTestAnalysis(env, maxVariableRecurse, maxFieldLen, srvChan, gopath, projectDir,
			preStorage, postStorage,
			nil, // module change function definitions are not valid for the updated version
			callingFunctions, testFunctions)
	if err != nil {
		return projectFieldChecks1, moduleChangesReached, preStorage, nil, err
	}

	// RESTORE original go.mod & go.sum for each module
	for _, b := range backups {
		if err := os.Rename(b.modBkp, b.modPath); err != nil {
			log.Printf("WARN: Failed to restore %s: %v", b.modPath, err)
		} else if b.sumPath != "" {
			if err := os.Rename(b.sumBkp, b.sumPath); err != nil {
				log.Printf("WARN: Failed to restore %s: %v", b.sumPath, err)
			}
		}
	}

	return max(projectFieldChecks1, projectFieldChecks2), moduleChangesReached, preStorage, postStorage, nil
}

func runMonitoredTestAnalysis(env []string, maxVariableRecurse, maxFieldLen int,
	srvChan chan *astServer, goroot, projectDir string, stableResultsStorage Storage, storage Storage,
	moduleChanges []*ModuleFunction, callerFunctions []*CallerFunction, testFunctions []*TestFunction) (int, int, error) {
	astEditor := &astModifier{}
	defer func() {
		errs := astEditor.Restore(env)
		if len(errs) > 0 {
			log.Printf("%sFailed to cleanup AST change (%d): %v", ErrorLogPrefix, len(errs), errs[0])
		}
	}()

	projectStatePointIdToIdent, projectPanicPointIdToIdent, moduleEntryPointIdToIdent, modulePanicPointIdToIdent, err :=
		injectMonitorPoints(astEditor, maxVariableRecurse, maxFieldLen, moduleChanges, callerFunctions)
	if err != nil {
		return 0, 0, err
	}
	if err := astEditor.Commit(); err != nil {
		return 0, 0, err
	}
	log.Printf("AST monitor ready, total tracked points: %v", astEditor.MaxPointId())

	var totalFieldCheckCount int
	moduleIdentsReached := make(map[string]bool, len(moduleChanges))
	var mu sync.Mutex
	var errGrp errgroup.Group
	errGrp.SetLimit(cap(srvChan))
	for i, tFunc := range testFunctions {
		i, tFunc := i, tFunc
		testFunc := func() error {
			srv := <-srvChan
			defer func() { srvChan <- srv }()
			var stableResults map[string][]CallFrame
			if stableResultsStorage != nil {
				if stableResultBlob, found, err := stableResultsStorage.LoadState(tFunc.FunctionIdent); err != nil {
					return fmt.Errorf("failed to load stable results: %w", err)
				} else if found {
					var stableTestResult TestResult
					if err := stableTestResult.UnmarshalMsgpack(stableResultBlob); err != nil {
						return fmt.Errorf("failed to unmarshal stable results: %w", err)
					}
					stableResults = stableTestResult.CallerResults
				} else {
					log.Printf("%sUnexpected missing stable results for function: %s", ErrorLogPrefix, tFunc.FunctionName)
				}
			}
			buf := &bytes.Buffer{}
			envWithPort := append([]string{fmt.Sprintf("LENS_MONITOR_PORT=%d", srv.Port())}, env...)
			failureOutput, testResult, fieldCheckCount, testModuleChangesReached, err :=
				runMonitoredTest(envWithPort, goroot, projectDir, srv, buf, stableResults,
					projectStatePointIdToIdent, projectPanicPointIdToIdent,
					moduleEntryPointIdToIdent, modulePanicPointIdToIdent,
					tFunc)
			if err != nil {
				return err
			}
			enc := msgpack.GetEncoder()
			defer msgpack.PutEncoder(enc)
			b, err := testResult.marshalMsgpack(enc, buf)
			if err == nil {
				err = storage.SaveState(tFunc.FunctionIdent, b)
			}
			if err != nil {
				return fmt.Errorf("store test result failed: %w", err)
			}

			mu.Lock()
			defer mu.Unlock()
			testResultStr := testPassStr
			if testResult.TestFailure {
				testResultStr = testFailStr
			}
			if len(moduleChanges) > 0 {
				log.Printf("%s Finished (%v/%v)...\n\t%s, Field State Checks: %d, Module Changes Hit: %d",
					tFunc.FunctionName, i+1, len(testFunctions),
					testResultStr, fieldCheckCount, len(testModuleChangesReached))
			} else {
				log.Printf("%s Finished (%v/%v)...\n\t%s, Field State Checks: %d",
					tFunc.FunctionName, i+1, len(testFunctions),
					testResultStr, fieldCheckCount)
			}
			if failureOutput != "" {
				fmt.Println(failureOutput)
			}

			totalFieldCheckCount += fieldCheckCount
			for _, ident := range testModuleChangesReached {
				moduleIdentsReached[*ident] = true
			}
			return nil
		}
		if i == 0 { // run the first test directly to avoid re-compiling concurrently
			if err := testFunc(); err != nil {
				return totalFieldCheckCount, len(moduleIdentsReached), err
			}
		} else {
			errGrp.Go(testFunc)
		}
	}
	err = errGrp.Wait()
	return totalFieldCheckCount, len(moduleIdentsReached), err
}

func injectMonitorPoints(astEditor *astModifier, maxVariableRecurse, maxFieldLen int,
	moduleChanges []*ModuleFunction, callerFunctions []*CallerFunction) (
	map[int]*string, map[int]*string, map[int]*string, map[int]*string, error) {
	pointIdLock := sync.Mutex{}
	projectStatePointIdToIdent := make(map[int]*string)
	projectPanicPointIdToIdent := make(map[int]*string)
	projectPkgs := make([]string, 0, len(callerFunctions))
	errGrp := ErrGroupLimitCPU()
	fileFuncHandler := func(funcs []*CallerFunction) error {
		if len(funcs) == 0 {
			return nil
		} else if funcs[0].FilePath != funcs[len(funcs)-1].FilePath {
			return errors.New("unexpected file batch inconsistency")
		}
		statePointIds := make(map[int]*string)
		panicPointIds := make(map[int]*string, len(funcs))
		for _, cf := range funcs {
			if cf.ReturnPanic { // injecting the recover or return state check on a function which returns in panic could cause a compiler failure
				// TODO - FUTURE - inject state checks before panics rather than at end of function, only excluding the panic recovery check
				continue
			}

			newPoints, err := astEditor.InjectFuncPointReturnStates(&cf.Function)
			if err != nil {
				return fmt.Errorf("failed to inject project return state point monitor: %w", err)
			} else if len(newPoints) == 0 {
				fmt.Printf("%sFunction already updated: %s %s\n", ErrorLogPrefix, cf.FilePath, cf.FunctionIdent)
				continue
			}
			for _, pointId := range newPoints {
				statePointIds[pointId] = &cf.FunctionIdent
				if monitorDebugLogging {
					fmt.Printf("Added project monitor return state point ID %d in %s\n", pointId, cf.FunctionIdent)
				}
			}

			// TODO - FUTURE - add astEditor.InjectFuncPointFinish to track execution times

			panicPointId, err := astEditor.InjectFuncPointPanic(&cf.Function)
			if err != nil {
				return fmt.Errorf("failed to inject project panic point monitor: %w", err)
			}
			panicPointIds[panicPointId] = &cf.FunctionIdent
			if monitorDebugLogging {
				fmt.Printf("Added project monitor panic point ID %d in %s\n", panicPointId, cf.FunctionIdent)
			}
		}

		if err := astEditor.CommitFile(funcs[0].FilePath); err != nil {
			return err
		}

		pointIdLock.Lock()
		defer pointIdLock.Unlock()
		maps.Insert(projectStatePointIdToIdent, maps.All(statePointIds))
		maps.Insert(projectPanicPointIdToIdent, maps.All(panicPointIds))
		return nil
	}
	slices.SortFunc(callerFunctions, func(a, b *CallerFunction) int {
		return strings.Compare(a.FilePath, b.FilePath) // sort by file so grouping can be optimal
	})
	var currentFile string
	var currentFileFunctions []*CallerFunction
	for _, cf := range callerFunctions {
		if currentFile == cf.FilePath {
			currentFileFunctions = append(currentFileFunctions, cf)
			continue
		}
		// inject ast client if not already injected
		if dir := filepath.Dir(cf.FilePath); !slices.Contains(projectPkgs, dir) {
			projectPkgs = append(projectPkgs, dir)

			errGrp.Go(func() error {
				if err := astEditor.InjectASTClient(dir, 0, maxVariableRecurse, maxFieldLen); err != nil {
					return fmt.Errorf("failed to inject project AST client: %w", err)
				}
				return nil
			})
		}

		fileFunctions := currentFileFunctions
		currentFileFunctions = []*CallerFunction{cf} // reset for our new file
		currentFile = cf.FilePath
		errGrp.Go(func() error { return fileFuncHandler(fileFunctions) })
	}
	errGrp.Go(func() error { return fileFuncHandler(currentFileFunctions) })

	moduleEntryPointIdToIdent := make(map[int]*string)
	modulePanicPointIdToIdent := make(map[int]*string)
	if len(moduleChanges) > 0 {
		modulePkgs := make([]string, 0, len(moduleChanges))
		fileFuncHandler := func(funcs []*ModuleFunction) error {
			if len(funcs) == 0 {
				return nil
			} else if funcs[0].FilePath != funcs[len(funcs)-1].FilePath {
				return errors.New("unexpected file batch inconsistency")
			}
			entryPointIds := make(map[int]*string, len(funcs))
			panicPointIds := make(map[int]*string, len(funcs))
			for _, mf := range funcs {
				entryPointId, err := astEditor.InjectFuncPointEntry(&mf.Function)
				if err != nil {
					return fmt.Errorf("failed to inject module entry point monitor: %w", err)
				}
				entryPointIds[entryPointId] = &mf.FunctionIdent
				if monitorDebugLogging {
					fmt.Printf("Added module entry point ID %d in %s\n", entryPointId, mf.FunctionIdent)
				}

				if !mf.ReturnPanic { // injecting the recover on a function which returns in panic could cause a compile failure
					panicPointId, err := astEditor.InjectFuncPointPanic(&mf.Function)
					if err != nil {
						return fmt.Errorf("failed to inject module panic point monitor: %w", err)
					}
					panicPointIds[panicPointId] = &mf.FunctionIdent
					if monitorDebugLogging {
						fmt.Printf("Added module panic point ID %d in %s\n", panicPointId, mf.FunctionIdent)
					}
				}
			}

			if err := astEditor.CommitFile(funcs[0].FilePath); err != nil {
				return err
			}

			pointIdLock.Lock()
			defer pointIdLock.Unlock()
			maps.Insert(moduleEntryPointIdToIdent, maps.All(entryPointIds))
			maps.Insert(modulePanicPointIdToIdent, maps.All(panicPointIds))
			return nil
		}
		slices.SortFunc(moduleChanges, func(a, b *ModuleFunction) int {
			return strings.Compare(a.FilePath, b.FilePath) // sort by file so grouping can be optimal
		})
		var currentFile string
		var currentFileFunctions []*ModuleFunction
		for _, mf := range moduleChanges {
			if currentFile == mf.FilePath {
				currentFileFunctions = append(currentFileFunctions, mf)
				continue
			}
			// inject ast client if not already in package
			if dir := filepath.Dir(mf.FilePath); !slices.Contains(modulePkgs, dir) {
				modulePkgs = append(modulePkgs, dir)

				errGrp.Go(func() error {
					if err := astEditor.InjectASTClient(dir, 0, maxVariableRecurse, maxFieldLen); err != nil {
						return fmt.Errorf("failed to inject module AST client: %w", err)
					}
					return nil
				})
			}

			fileFunctions := currentFileFunctions
			currentFileFunctions = []*ModuleFunction{mf} // reset for our new file
			currentFile = mf.FilePath
			errGrp.Go(func() error {
				return fileFuncHandler(fileFunctions)
			})
		}
		errGrp.Go(func() error {
			return fileFuncHandler(currentFileFunctions)
		})
		log.Printf("Monitor injected in %v relevant module functions (%v pkgs)", len(moduleChanges), len(modulePkgs))
	}
	if err := errGrp.Wait(); err != nil { // wait for AST modifications to finish
		return nil, nil, nil, nil, err
	}
	return projectStatePointIdToIdent, projectPanicPointIdToIdent,
		moduleEntryPointIdToIdent, modulePanicPointIdToIdent, nil
}

func runMonitoredTest(env []string, goroot, projectDir string, srv *astServer, execOutput *bytes.Buffer,
	stableResults map[string][]CallFrame,
	projectStatePointIdToIdent, projectPanicPointIdToIdent,
	moduleEntryPointIdToIdent, modulePanicPointIdToIdent map[int]*string, tFunc *TestFunction) (string, TestResult, int, []*string, error) {
	pointHandler1 := newTestMonitor(stableResults, goroot, projectDir,
		projectStatePointIdToIdent, projectPanicPointIdToIdent, moduleEntryPointIdToIdent, modulePanicPointIdToIdent)
	if err := srv.SetPointHandler(pointHandler1); err != nil {
		return "", TestResult{}, 0, nil, err
	}
	dir := filepath.Dir(tFunc.FilePath)
	execOutput.Reset()
	testFailure1 := ExecGoTest(dir, env, newLimitedRollingBufferWriter(execOutput, 8192), tFunc) != nil
	var failureOutput string
	if testFailure1 {
		failureOutput = cleanExecOutput(execOutput)
	}
	test1Result := pointHandler1.makeTestResult(tFunc, testFailure1)
	test1FieldCheckCount := int(pointHandler1.fieldCheckCount.Load())
	test1ModuleChangesReached := pointHandler1.getModuleChangesReached()
	pointHandler1 = nil //nolint:wastedassign // allow garbage collection

	if stableResults != nil {
		// we already know the field selection, skip second test run
		return failureOutput, test1Result, test1FieldCheckCount, test1ModuleChangesReached, nil
	}

	// second run to compare against
	pointHandler2 := newTestMonitor(nil, goroot, projectDir,
		projectStatePointIdToIdent, projectPanicPointIdToIdent, moduleEntryPointIdToIdent, modulePanicPointIdToIdent)
	if err := srv.SetPointHandler(pointHandler2); err != nil {
		return "", TestResult{}, 0, nil, err
	}
	test2io := io.Discard
	if failureOutput == "" {
		execOutput.Reset()
		test2io = execOutput
	}
	testFailure2 := ExecGoTest(dir, env, test2io, tFunc) != nil
	if failureOutput == "" && testFailure2 {
		failureOutput = cleanExecOutput(execOutput)
	}
	test2Result := pointHandler2.makeTestResult(tFunc, testFailure2)

	stable := testResultStableFields(test1Result, test2Result)
	fieldCheckCount := min(test1FieldCheckCount, int(pointHandler2.fieldCheckCount.Load()))
	return failureOutput, stable, fieldCheckCount, test1ModuleChangesReached, nil
}

func cleanExecOutput(execOutput *bytes.Buffer) string {
	return strings.TrimSpace(
		strings.ReplaceAll(strings.TrimSpace(execOutput.String()), "FAIL\nexit status 1\n", ""))
}

func newTestMonitor(stableResults map[string][]CallFrame, goroot, projectDir string, projectStatePointIdToIdent, projectPanicPointIdToIdent,
	moduleEntryPointIdToIdent, modulePanicPointIdToIdent map[int]*string) *testMonitor {
	return &testMonitor{
		stableResults:              stableResults,
		goroot:                     goroot,
		projectDir:                 projectDir,
		projectStatePointIdToIdent: projectStatePointIdToIdent,
		projectPanicPointIdToIdent: projectPanicPointIdToIdent,
		moduleEntryPointIdToIdent:  moduleEntryPointIdToIdent,
		modulePanicPointIdToIdent:  modulePanicPointIdToIdent,
		pointLocks:                 newDefaultStripedMutex(),
		callerFrames:               make(map[string][]CallFrame),
		projectPanics:              make(map[string][]string),
		modulePanics:               make(map[string][]string),
	}
}

type testMonitor struct {
	// maps created by AST injection for quick lookups
	projectStatePointIdToIdent map[int]*string
	projectPanicPointIdToIdent map[int]*string
	moduleEntryPointIdToIdent  map[int]*string
	modulePanicPointIdToIdent  map[int]*string
	pointLocks                 *stripedMutex

	// runtime config
	goroot        string
	projectDir    string
	stableResults map[string][]CallFrame

	// runtime data
	moduleChangesReached sync.Map      // module funcIdent -> true
	fieldCheckCount      atomic.Uint32 // number of LensMonitorMessagePointState hits
	callerFramesMu       sync.Mutex    // protects callerFrames
	callerFrames         map[string][]CallFrame
	panicMu              sync.Mutex
	projectPanics        map[string][]string
	modulePanics         map[string][]string
	wait                 sync.WaitGroup
}

func debugLogMonitorStack(pointId int, stack []LensMonitorStackFrame) {
	fmt.Printf(">> Stacktrace for monitor point %d:\n", pointId)
	for _, frame := range stack {
		fmt.Printf("\t%s:%d\t%s\n", frame.File, frame.Line, frame.Function)
	}
}

func stackFramesKey(bb *bytes.Buffer, frames []StackFrame) string {
	bb.Reset()
	for _, sf := range frames {
		// don't use sf.ID(), it's possible for line numbers to change dependent on the AST rewrites
		if bb.Len() > 0 {
			bb.WriteRune('|')
		}
		bb.WriteString(sf.File)
		bb.WriteRune(':')
		bb.WriteString(sf.Function)
	}
	return bytesKey(bb.Bytes())
}

func trimStackFile(projectDir, goroot, file string) string {
	if projectDir == "" {
		log.Printf("%sNo protected directory set!", ErrorLogPrefix)
	} else {
		if ok, err := fileWithinDir(file, projectDir); err == nil && ok {
			if rel, err := filepath.Rel(projectDir, file); err == nil {
				return "./" + filepath.ToSlash(rel)
			}
		}
	}

	// external file trim
	file = filepath.ToSlash(file)
	if goroot != "" {
		if ok, err := fileWithinDir(file, goroot); err == nil && ok {
			trimIndex := len(goroot) // remove goroot, but leave the `/` prefix to match below
			if goroot[trimIndex-1] == filepath.Separator {
				trimIndex--
			}
			file = file[trimIndex:]
		}
	}
	if idx := strings.Index(file, "/pkg/mod/"); idx >= 0 {
		file = file[idx+len("/pkg/mod/"):]
	}

	if strings.HasPrefix(file, "./") { // safety check
		log.Printf("%sUnexpected external file identified as project: %q", ErrorLogPrefix, file)
		file = file[1:] // remove '.' for safety
	}

	return file
}

func projectFrames(frames []StackFrame) []StackFrame {
	return bulk.SliceFilter(func(sf StackFrame) bool {
		// match the relative path prefix from trimStackFile
		return strings.HasPrefix(sf.File, "./") && !strings.HasPrefix(sf.File, "./vendor/")
	}, frames)
}

func (t *testMonitor) HandleFuncPoint(msg LensMonitorMessagePoint) {
	// pointLock not needed for this state

	if monitorDebugLogging {
		debugLogMonitorStack(msg.PointID, msg.Stack)
	}
	// record pointID as reached
	t.moduleChangesReached.Store(msg.PointID, true)
}

func (t *testMonitor) HandleFuncPointState(msg LensMonitorMessagePointState) {
	t.wait.Add(1) // done in routine

	if monitorDebugLogging {
		debugLogMonitorStack(msg.PointID, msg.Stack)
		fmt.Printf(">> State fields for point %v:\n", msg.PointID)
		var fieldLog func(string, []LensMonitorField)
		fieldLog = func(prefix string, fields []LensMonitorField) {
			for _, field := range fields {
				if len(field.Children) > 0 {
					fieldLog(prefix+field.Name+".", field.Children)
				} else {
					fmt.Printf("\t%s = %v\n", prefix+field.Name, field.Value)
				}
			}
		}
		fieldLog("", msg.Fields)
	}

	callerIdent, ok := t.projectStatePointIdToIdent[msg.PointID]
	if !ok {
		log.Printf("%sUnexpected state point id: %d", ErrorLogPrefix, msg.PointID)
		return
	}

	lock := t.pointLocks.Lock(*callerIdent)
	go func() {
		defer t.wait.Done()
		defer lock.Unlock()

		t.fieldCheckCount.Add(1)

		stack := make([]StackFrame, len(msg.Stack))
		for i, f := range msg.Stack {
			stack[i] = StackFrame{
				File:     trimStackFile(t.projectDir, t.goroot, f.File),
				Line:     uint32(f.Line),
				Function: f.Function,
			}
		}

		// flatten fields
		fieldMap := make(FieldValues)
		for _, sf := range msg.Fields {
			collectFields(fieldMap, sf.Name, sf.Value, sf.Type, sf.Children)
		}
		callerIdentStr := *callerIdent

		t.callerFramesMu.Lock()
		defer t.callerFramesMu.Unlock()

		if t.stableResults != nil { // filter by stableResults if present (memory optimization)
			frames, ok := t.stableResults[callerIdentStr]
			var bb bytes.Buffer
			if !ok {
				for k := range fieldMap {
					delete(fieldMap, k)
				}
			} else {
				pStack := projectFrames(stack)
				pKey := stackFramesKey(&bb, pStack)

				var targetOccur int
				for _, cf := range t.callerFrames[callerIdentStr] {
					if stackFramesKey(&bb, projectFrames(cf.Stack)) == pKey {
						targetOccur++
					}
				}

				idx := -1
				var occ int
				for i := range frames {
					if stackFramesKey(&bb, projectFrames(frames[i].Stack)) == pKey {
						if occ == targetOccur {
							idx = i
							break
						}
						occ++
					}
				}

				if idx >= 0 {
					allowed := frames[idx].FieldValues
					for fname := range fieldMap {
						if _, ok := allowed[fname]; !ok {
							delete(fieldMap, fname)
						}
					}
				} else {
					for k := range fieldMap {
						delete(fieldMap, k)
					}
				}
			}
		}

		t.callerFrames[callerIdentStr] =
			append(t.callerFrames[callerIdentStr],
				CallFrame{
					FieldValues: fieldMap,
					Stack:       stack,
					TimeMillis:  uint32((msg.TimeNS + 500000) / 1_000_000),
				})
	}()
}

// collectFields flattens nested fields into dot‑separated names.
func collectFields(dst FieldValues, name string, val interface{}, typ string, children []LensMonitorField) {
	value := &FieldValue{}
	dst[name] = value
	if len(children) == 0 {
		str := fmt.Sprint(val)
		if !strings.HasSuffix(typ, "string") && len(str) > nonStringHashSizeLimit {
			sha := sha1.Sum([]byte(str))
			str = HashFieldValuePrefix + base91.StdEncoding.EncodeToString(sha[:])
		}
		value.Value = str
		return
	}
	vChildren := make(FieldValues)
	for _, ch := range children {
		collectFields(vChildren, ch.Name, ch.Value, ch.Type, ch.Children)
	}
	value.Children = vChildren
}

func (t *testMonitor) HandleFuncPointPanic(msg LensMonitorMessagePointPanic) {
	// acquiring the pointLock not currently required for this state
	t.panicMu.Lock()
	defer t.panicMu.Unlock()

	if callerIdent, ok := t.projectPanicPointIdToIdent[msg.PointID]; ok {
		ident := *callerIdent
		t.projectPanics[ident] = append(t.projectPanics[ident], msg.Message)
	} else if callerIdent, ok = t.modulePanicPointIdToIdent[msg.PointID]; ok {
		ident := *callerIdent
		t.modulePanics[ident] = append(t.modulePanics[ident], msg.Message)
	} else {
		log.Printf("%sUnexpected panic point id %d: %s", ErrorLogPrefix, msg.PointID, msg.Message)
	}
}

func (t *testMonitor) makeTestResult(tFunc *TestFunction, failure bool) TestResult {
	t.wait.Wait()

	return TestResult{
		TestFunction:     tFunc.Minimum(),
		CallerResults:    t.callerFrames,
		ProjectPanics:    t.projectPanics,
		ModulePanics:     t.modulePanics,
		ModuleChangesHit: t.getModuleChangesReachCount(),
		TestFailure:      failure,
	}
}

func (t *testMonitor) getModuleChangesReachCount() int {
	var count int
	t.moduleChangesReached.Range(func(key, _ any) bool {
		count++
		return true
	})
	return count
}

func (t *testMonitor) getModuleChangesReached() (out []*string) {
	t.moduleChangesReached.Range(func(key, _ any) bool {
		keyId := key.(int)
		if moduleFuncIdent, ok := t.moduleEntryPointIdToIdent[keyId]; ok {
			out = append(out, moduleFuncIdent)
		} else {
			log.Printf("%sUnexpected module entry point id: %d", ErrorLogPrefix, keyId)
		}
		return true
	})
	slices.SortFunc(out, func(a, b *string) int {
		return strings.Compare(*a, *b)
	})
	return
}

// testResultStableFields compares two TestResult and returns only field values
// that were exactly the same between the two runs.
func testResultStableFields(r1, r2 TestResult) TestResult {
	var bb bytes.Buffer
	commonCallerResults := make(map[string][]CallFrame, len(r1.CallerResults))
	for callerIdent, frames1 := range r1.CallerResults {
		frames2, ok := r2.CallerResults[callerIdent]
		if !ok {
			log.Printf("%sUnexpected missing results for %s", ErrorLogPrefix, callerIdent)
			continue
		}

		// sort both frame slices by client time for the most reliable ordering
		callFrameSortFunc := func(a, b CallFrame) int {
			if a.TimeMillis < b.TimeMillis {
				return -1
			} else if a.TimeMillis > b.TimeMillis {
				return 1
			}
			return 0
		}
		slices.SortStableFunc(frames1, callFrameSortFunc)
		slices.SortStableFunc(frames2, callFrameSortFunc)

		frames2ByKey := bulk.SliceToGroupsBy(func(f CallFrame) string {
			return stackFramesKey(&bb, projectFrames(f.Stack))
		}, frames2)

		used := make(map[string]int, len(frames1))
		commonFrames := make([]CallFrame, 0, len(frames1))
		for _, frame1 := range frames1 {
			key := stackFramesKey(&bb, projectFrames(frame1.Stack))
			idx := used[key]
			used[key] = idx + 1
			if idx >= len(frames2ByKey[key]) {
				continue
			}
			frame2 := frames2ByKey[key][idx]

			stableValues := stableFieldValues(frame1.FieldValues, frame2.FieldValues)

			commonFrames = append(commonFrames, CallFrame{
				FieldValues: stableValues,
				Stack:       frame1.Stack,
				TimeMillis:  frame1.TimeMillis,
			})
		}

		commonCallerResults[callerIdent] = commonFrames
	}

	intersectPanics := func(m1, m2 map[string][]string) map[string][]string {
		out := make(map[string][]string, len(m1))
		for ident, list1 := range m1 {
			list2, ok := m2[ident]
			if !ok {
				continue
			}
			counts := bulk.SliceToCounts(list2)
			for _, msg := range list1 {
				if counts[msg] > 0 {
					out[ident] = append(out[ident], msg)
					counts[msg]--
				}
			}
		}
		return out
	}

	return TestResult{
		TestFunction:     r1.TestFunction,
		CallerResults:    commonCallerResults,
		ProjectPanics:    intersectPanics(r1.ProjectPanics, r2.ProjectPanics),
		ModulePanics:     intersectPanics(r1.ModulePanics, r2.ModulePanics),
		ModuleChangesHit: r1.ModuleChangesHit,
		TestFailure:      r1.TestFailure || r2.TestFailure,
	}
}

// stableFieldValues returns a new FieldValues containing only keys whose
// leaf Value pointers are identical or whose nested Children contain matches
func stableFieldValues(f1, f2 FieldValues) FieldValues {
	out := make(FieldValues)
	for name, v1 := range f1 {
		v2, ok := f2[name]
		if !ok {
			continue // field missing in second run
		}

		if len(v1.Children) == 0 && len(v2.Children) == 0 {
			// both are leaves, compare interned pointers
			if v1.Value == v2.Value {
				out[name] = &FieldValue{Value: v1.Value}
			}
		} else if len(v1.Children) > 0 && len(v2.Children) > 0 {
			// both have children, recurse
			if nested := stableFieldValues(v1.Children, v2.Children); len(nested) > 0 {
				out[name] = &FieldValue{Children: nested}
			}
		}
		// mixed leaf vs node or no matches, skip
	}
	return out
}
