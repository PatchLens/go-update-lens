package lens

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"log"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"github.com/go-analyze/bulk"
	"github.com/pmezard/go-difflib/difflib"
	"golang.org/x/tools/go/packages"
)

const logFunctionCallChains = false // disabled until we transition off CHA
const noneScopeFlag = "none"
const fullScopeFlag = "full"
const areaScopeFlag = "area"
const lineScopeFlag = "line"

// Config holds settings and state for an AnalysisEngine.
type Config struct {
	ProjectDir, ModuleVersionFlag, ModulesVersionFlag     string
	UpdatedGoModFile, UpdatedGoWorkFile                   string
	AstMonitorPort, MaxFieldRecurse, MaxFieldLen, CacheMB int
	ReportJsonFile, ReportChartsFile                      string
	MutationScope, MutationMode, MutationTests            string
	TmpCopy                                               bool
	TimeMultiplier                                        int
	// Computed fields
	Gopath, Gomodcache, AbsProjDir string
	// Parsed target modules from flags
	TargetModules []TargetModule
	// Custom flags support - all stored as strings for ease of use
	CustomFlags map[string]string
	// Internal state tracking
	prepared bool
}

// TargetModule specifies a module name and version to analyze.
type TargetModule struct {
	Name    string
	Version string
}

// ModuleChangeProvider analyzes changes in Go module dependencies between versions.
// It identifies functions that have been modified, added, or removed when a module is updated from one version to another.
type ModuleChangeProvider interface {
	// AnalyzeModuleChanges examines the differences between module versions to identify changed functions.
	//
	// Parameters:
	//   - config: configuration containing paths and settings for analysis
	//   - analyzeExpandTransitive: if true, recursively analyzes transitive dependency changes
	//   - changedModules: list of modules that have version changes to analyze
	//   - neighbourRadius: radius for marking changed lines in function definitions (used for mutation testing scope)
	//
	// Returns:
	//   - []*ModuleFunction: list of functions that have changed between versions
	//   - []string: list of module names that were checked during analysis
	//   - error: any error encountered during analysis
	AnalyzeModuleChanges(config Config, analyzeExpandTransitive bool,
		changedModules []ModuleChange, neighbourRadius int) ([]*ModuleFunction, []string, error)

	// Cleanup is invoked after engine analysis is complete, allowing freeing of resources used during analysis.
	Cleanup()
}

// CallerAnalysisProvider performs static analysis to identify project functions that call changed module functions.
// This establishes the call graph from the project code to the modified dependency functions.
type CallerAnalysisProvider interface {
	// PerformCallerStaticAnalysis analyzes the project's source code to find all
	// functions that directly or indirectly call the changed module functions.
	// It builds a call graph to trace how module changes might affect project code.
	//
	// Parameters:
	//   - config: configuration containing paths and settings for analysis
	//   - moduleChanges: list of functions in dependencies that have changed
	//
	// Returns:
	//   - []*CallerFunction: list of project functions that call changed module functions
	//   - ReachableModuleChange: mapping of which module changes are reachable from project code
	//   - error: any error encountered during static analysis
	PerformCallerStaticAnalysis(config Config, moduleChanges []*ModuleFunction) ([]*CallerFunction, ReachableModuleChange, error)

	// Cleanup is invoked after engine analysis is complete, allowing freeing of resources used during static analysis.
	Cleanup()
}

// TestProvider discovers and optionally generates test functions that exercise
// the project code affected by module changes.
type TestProvider interface {
	// ProvideTests discovers existing test functions that exercise the calling functions.
	// Advanced implementations may optionally generate additional tests to improve coverage.
	//
	// Parameters:
	//   - config: configuration containing paths and settings for analysis
	//   - callingFunctions: list of project functions that call changed module functions
	//
	// Returns:
	//   - []*TestFunction: list of test functions that exercise the affected code
	//   - error: any error encountered during test discovery or generation
	ProvideTests(config Config, callingFunctions []*CallerFunction) ([]*TestFunction, error)

	// Cleanup is invoked after engine analysis is complete, allowing freeing resources used during test provision.
	Cleanup()
}

// UpdateAnalysisProvider executes tests with runtime monitoring to capture
// the behavior of code before and after module updates.
type UpdateAnalysisProvider interface {
	// RunModuleUpdateAnalysis runs tests with AST instrumentation to capture runtime
	// behavior before and after module updates. It injects monitoring code to record
	// function calls, field states, panics, and timing information.
	//
	// Parameters:
	//   - config: configuration containing paths and settings for analysis
	//   - portStart: starting port number for the monitoring server
	//   - storage: storage interface for persisting test results
	//   - changedModules: list of modules that have version changes
	//   - reachableModuleChanges: mapping of module changes reachable from project code
	//   - callingFunctions: project functions that call changed module functions
	//   - testFunctions: test functions that exercise the affected code
	//
	// Returns:
	//   - int: number of project field checks performed
	//   - int: number of module changes reached during testing
	//   - Storage: pre-update test results storage
	//   - Storage: post-update test results storage
	//   - error: any error encountered during analysis
	RunModuleUpdateAnalysis(config Config, storage Storage, changedModules []ModuleChange, reachableModuleChanges ReachableModuleChange,
		callingFunctions []*CallerFunction, testFunctions []*TestFunction) (int, int, Storage, Storage, error)

	// Cleanup is invoked after engine analysis is complete, allowing freeing of resources used during update analysis.
	Cleanup()
}

// MutationTester performs mutation testing on the changed module code to validate
// that the discovered tests adequately cover the behavioral changes. It introduces
// deliberate mutations in the changed code and verifies that tests catch them.
type MutationTester interface {
	// RunMutationTesting applies mutations to the changed module functions and runs
	// the relevant tests to validate test coverage. It uses go-mutesting to introduce
	// code mutations and checks if the test suite can detect the introduced changes.
	//
	// Parameters:
	//   - config: configuration containing paths and settings for analysis
	//   - fastMutations: if true, use fast mutation mode (fewer mutations for speed)
	//   - lineScopedMutations: if true, limit mutations to specific changed lines
	//   - runTargetedTests: if true, run only tests that target the changed functions
	//   - moduleChanges: list of module functions that have changed
	//   - testFunctions: list of test functions to run during mutation testing
	//
	// Returns:
	//   - MutationResult: results of mutation testing including mutation scores and details
	//   - error: any error encountered during mutation testing
	RunMutationTesting(config Config, fastMutations, lineScopedMutations,
		runTargetedTests bool, moduleChanges []*ModuleFunction, testFunctions []*TestFunction) (MutationResult, error)

	// Cleanup is invoked after engine analysis is complete, allowing freeing resources used during mutation testing.
	Cleanup()
}

// TestResultAnalyzer compares test execution results from before and after
// module updates to identify behavioral changes. It analyzes captured field
// values, execution paths, and performance metrics.
type TestResultAnalyzer interface {
	// CompareTestResults analyzes the differences between pre-update and post-update
	// test execution results. It compares captured field values, function call sequences,
	// timing information, and other runtime behavior to detect changes.
	//
	// Parameters:
	//   - preResults: storage containing test results from before the module update
	//   - postResults: storage containing test results from after the module update
	//   - timeMultiplier: multiplier for timing tolerances (higher values are more lenient)
	//
	// Returns:
	//   - int: number of test cases with identical behavior (same results)
	//   - int: number of test cases with different behavior (different results)
	//   - []TestReport: detailed reports of differences found between test runs
	//   - error
	CompareTestResults(preResults, postResults Storage, timeMultiplier int) (int, int, []TestReport, error)
}

// StorageProvider creates storage instances for persisting test execution results
// and analysis data. It abstracts the storage backend to allow different
// implementations (file-based, in-memory, database, etc.).
type StorageProvider interface {
	// NewStorage creates a new storage instance for persisting test results and
	// other analysis data. The storage is used to save captured runtime information
	// during test execution and retrieve it during result comparison.
	//
	// Returns:
	//   - Storage: a new storage interface instance
	//   - error: any error encountered during storage creation
	NewStorage() (Storage, error)
}

// ReportWriter generates analysis reports in various formats (JSON, charts, etc.)
// containing the results of module update analysis. It consolidates all analysis
// data into comprehensive reports for review and decision-making.
type ReportWriter interface {
	// WriteReportFiles generates and writes analysis reports to the specified file paths.
	// It creates both JSON and chart-based reports containing all analysis results,
	// including timing information, test results, mutation testing results, and
	// behavioral change summaries.
	//
	// Parameters:
	//   - reportJsonFile: path where the JSON report should be written
	//   - reportChartsFile: path where the chart report should be written
	//   - startTime: when the analysis started (for computing total duration)
	//   - analysisTime: duration of module change analysis
	//   - testDiscoveryTime: duration of test discovery or generation
	//   - testExecutionTime: duration of test execution with monitoring
	//   - mutationTime: duration of mutation testing
	//   - changedModules: list of modules with version changes
	//   - checkedModules: list of all modules that were analyzed
	//   - moduleChangeCount: total number of changed functions across all modules
	//   - moduleChangesReachedInTesting: number of module changes exercised by tests
	//   - projectFieldChecks: number of field value checks performed on project code
	//   - callingFunctions: project functions that call changed module functions
	//   - testFunctions: test functions that exercise the affected code
	//   - sameCount: number of test cases with identical behavior before/after update
	//   - diffCount: number of test cases with different behavior before/after update
	//   - testReports: detailed reports of behavioral differences found
	//   - globalMutations: results from mutation testing
	//
	// Returns:
	//   - error: any error encountered during report generation or file writing
	WriteReportFiles(reportJsonFile, reportChartsFile string, startTime time.Time,
		analysisTime, testDiscoveryTime, testExecutionTime, mutationTime time.Duration,
		changedModules []ModuleChange, checkedModules []string, moduleChangeCount, moduleChangesReachedInTesting int,
		projectFieldChecks int, callingFunctions []*CallerFunction, testFunctions []*TestFunction,
		sameCount, diffCount int, testReports []TestReport,
		globalMutations MutationResult) error
}

// ModuleAnalysisData contains the complete analysis data for a single module update.
// This structure is passed to PostModuleAnalysis hooks to provide extensions with changed function data.
type ModuleAnalysisData struct {
	// ModuleChange identifies the module and versions being compared
	ModuleChange ModuleChange

	// ChangedFunctions contains only functions that changed between versions, using
	// the OLD (pre-update) version's definition with LineChangeBitmap marking modified lines
	// relative to the old definition.
	// Each ModuleFunction.Definition contains the old version's source code.
	ChangedFunctions []*ModuleFunction
}

// DefaultModuleChangeProvider provides the standard implementation of ModuleChangeProvider.
type DefaultModuleChangeProvider struct {
	// PostModuleAnalysis is an optional hook called after analyzing all module updates.
	//
	// The hook is called once after all modules have been analyzed, with aggregated data from all modules.
	//
	// Parameters:
	//   - allModuleData: Slice of ModuleAnalysisData, one per analyzed module
	//
	// Returns:
	//   - error: Any error encountered during analysis. Errors are FATAL and will stop the entire analysis.
	PostModuleAnalysis func(allModuleData []ModuleAnalysisData) error
}

func (d *DefaultModuleChangeProvider) AnalyzeModuleChanges(config Config, analyzeExpandTransitive bool,
	changedModules []ModuleChange, neighbourRadius int) ([]*ModuleFunction, []string, error) {
	return AnalyzeModuleChanges(analyzeExpandTransitive, config.Gomodcache, config.AbsProjDir, changedModules, neighbourRadius, d.PostModuleAnalysis)
}

func (d *DefaultModuleChangeProvider) Cleanup() {}

// DefaultCallerAnalysisProvider provides the standard implementation of CallerAnalysisProvider.
type DefaultCallerAnalysisProvider struct {
	// PostCallerAnalysis is an optional hook called after project caller static analysis completes.
	//
	// The hook is called once after all project callers have been identified.
	//
	// Parameters:
	//   - projectPackages: Project packages with type information from static analysis
	//   - modulePackages: Module (dependency) packages with type information from static analysis
	//   - identEdges: Call graph edges mapping function idents to callees
	//   - moduleChanges: All functions that changed in module updates
	//   - callers: Project functions that call into changed module functions
	//   - reachable: Map of which module changes are reachable from project code
	//
	// The package parameters provide access to type information for accurate analysis.
	// Project and module packages are separated to enable targeted analysis.
	// The identEdges parameter provides a simplified view of the project call graph,
	// enabling extensions to perform additional reachability analysis without needing
	// to reload the expensive SSA call graph.
	//
	// Returns:
	//   - error: Any fatal error encountered during analysis.
	PostCallerAnalysis func(projectPackages []*packages.Package, modulePackages []*packages.Package,
		identEdges map[string][]string, moduleChanges []*ModuleFunction,
		callers []*CallerFunction, reachable ReachableModuleChange) error
}

func (d *DefaultCallerAnalysisProvider) PerformCallerStaticAnalysis(config Config, moduleChanges []*ModuleFunction) ([]*CallerFunction, ReachableModuleChange, error) {
	callers, reachable, cg, projectPkgs, modulePkgs, err := CallerStaticAnalysis(moduleChanges, config.AbsProjDir)
	if err != nil {
		return nil, nil, err
	}

	if d.PostCallerAnalysis != nil {
		// Only extract edges when hook exists
		identEdges := extractCallGraphEdges(cg)
		cg = nil //nolint:ineffassign,wastedassign // Allow GC to collect call graph during hook execution
		if err := d.PostCallerAnalysis(projectPkgs, modulePkgs, identEdges, moduleChanges, callers, reachable); err != nil {
			return nil, nil, fmt.Errorf("post-caller analysis hook failed: %w", err)
		}
	}

	return callers, reachable, nil
}

func (d *DefaultCallerAnalysisProvider) Cleanup() {}

// DefaultTestProvider provides the standard implementation of TestProvider for static test discovery only.
type DefaultTestProvider struct{}

func (d *DefaultTestProvider) ProvideTests(config Config, callingFunctions []*CallerFunction) ([]*TestFunction, error) {
	return TestStaticAnalysis(callingFunctions, config.AbsProjDir)
}

func (d *DefaultTestProvider) Cleanup() {}

// DefaultUpdateAnalysisProvider provides the standard implementation of UpdateAnalysisProvider.
type DefaultUpdateAnalysisProvider struct {
	// ExtensionPointConfig is an optional function that extensions can use to inject additional
	// monitoring points during AST instrumentation. The function receives the ASTModifier and
	// changed module/caller functions, and returns a map of point IDs to frame keys for storage.
	// The returned map is used to route LensMonitorMessagePointState events to ExtensionFrames.
	ExtensionPointConfig func(astEditor *ASTModifier, moduleChanges []*ModuleFunction, callerFunctions []*CallerFunction) (map[int]*string, error)
}

func (d *DefaultUpdateAnalysisProvider) RunModuleUpdateAnalysis(config Config,
	storage Storage, changedModules []ModuleChange, reachableModuleChanges ReachableModuleChange,
	callingFunctions []*CallerFunction, testFunctions []*TestFunction) (int, int, Storage, Storage, error) {
	return RunModuleUpdateAnalysis(config.Gopath, config.Gomodcache, config.AbsProjDir, config.AstMonitorPort,
		storage, config.MaxFieldRecurse, config.MaxFieldLen,
		changedModules, reachableModuleChanges, callingFunctions, testFunctions, d.ExtensionPointConfig)
}

func (d *DefaultUpdateAnalysisProvider) Cleanup() {}

// DefaultMutationTester provides the standard implementation of MutationTester.
type DefaultMutationTester struct{}

func (d *DefaultMutationTester) RunMutationTesting(config Config, fastMutations, lineScopedMutations,
	runTargetedTests bool, moduleChanges []*ModuleFunction, testFunctions []*TestFunction) (MutationResult, error) {
	return RunMutationTesting(config.Gopath, config.Gomodcache, config.AbsProjDir, fastMutations, lineScopedMutations, runTargetedTests, moduleChanges, testFunctions)
}

func (d *DefaultMutationTester) Cleanup() {}

// DefaultTestResultAnalyzer provides the standard implementation of TestResultAnalyzer.
type DefaultTestResultAnalyzer struct{}

// DiffValues provides a simple human-readable diff explanation of two complex value types.
// If the values are identical an empty string will be returned.
func (d *DefaultTestResultAnalyzer) DiffValues(v1, v2 string) string {
	if v1 == v2 {
		return ""
	}
	preHashed := strings.HasPrefix(v1, HashFieldValuePrefix)
	postHashed := strings.HasPrefix(v2, HashFieldValuePrefix)
	if preHashed && postHashed {
		var v1Suffix, v2Suffix string
		if len(v1) >= 4 {
			v1Suffix = v1[len(v1)-4:]
		}
		if len(v2) >= 4 {
			v2Suffix = v2[len(v2)-4:]
		}
		return fmt.Sprintf("<VALUE TOO LARGE ...%s> != <VALUE TOO LARGE ...%s>", v1Suffix, v2Suffix)
	} else if preHashed {
		var v1Suffix string
		if len(v1) >= 4 {
			v1Suffix = v1[len(v1)-4:]
		}
		return fmt.Sprintf("<VALUE TOO LARGE ...%s> != %q", v1Suffix, v2)
	} else if postHashed {
		var v2Suffix string
		if len(v2) >= 4 {
			v2Suffix = v2[len(v2)-4:]
		}
		return fmt.Sprintf("%q != <VALUE TOO LARGE ...%s>", v1, v2Suffix)
	}
	// else, build a unified diff of the raw values
	diff := difflib.UnifiedDiff{
		A:       difflib.SplitLines(v1),
		B:       difflib.SplitLines(v2),
		Context: 2,
	}
	if text, err := difflib.GetUnifiedDiffString(diff); err == nil && text != "" {
		return text
	} else { // fallback to basic format if unexpected diff error
		return fmt.Sprintf("\t'%v'\n!=\n\t'%v'", v1, v2)
	}
}

func (d *DefaultTestResultAnalyzer) CompareTestResults(preResultStorage, postResultStorage Storage, timeMultiplier int) (int, int, []TestReport, error) {
	// sort results for consistent output
	preResultNames, err := preResultStorage.ListKeys()
	if err != nil {
		return 0, 0, nil, fmt.Errorf("error listing pre-update results: %w", err)
	}
	postResultsNames, err := postResultStorage.ListKeys()
	if err != nil {
		return 0, 0, nil, fmt.Errorf("error listing post-update results: %w", err)
	}
	slices.Sort(preResultNames)
	slices.Sort(postResultsNames)

	// compare the pre and post module update field values
	var sameCount, diffCount int
	testReports := make([]TestReport, len(postResultsNames))
	var performanceLogBuffer strings.Builder
	for i, funcIdent := range postResultsNames {
		preResults, found, err := d.loadTestResult(preResultStorage, funcIdent)
		if err != nil {
			return 0, 0, nil, fmt.Errorf("error loading pre-results for %s: %w", funcIdent, err)
		} else if !found {
			log.Printf("WARN: post‑update test %s not in pre‑results", funcIdent)
			continue
		}
		postResults, found, err := d.loadTestResult(postResultStorage, funcIdent)
		if err != nil {
			return 0, 0, nil, fmt.Errorf("error loading post-results for %s: %w", funcIdent, err)
		} else if !found {
			return 0, 0, nil, fmt.Errorf("unexpected missing post results: %s", funcIdent)
		}
		callerFieldChanges := make(map[string]map[string]string)
		callerTimeChanges := make(map[string]PerformanceTimeChange)
		var testSameCount, testDiffCount, testRegressionCount int
		sortedIdents := slices.Collect(maps.Keys(preResults.CallerResults))
		slices.Sort(sortedIdents) // iterate sorted idents in case we want to compare across runs

		var bb bytes.Buffer
		for _, callerIdent := range sortedIdents {
			frames := preResults.CallerResults[callerIdent]
			postResult := postResults.CallerResults[callerIdent]

			// Build map of post-update frames by stack key for proper matching
			postFramesByKey := bulk.SliceToGroupsBy(func(f CallFrame) string {
				return StackFramesKey(&bb, ProjectFrames(f.Stack))
			}, postResult)

			// Track which frames with the same stack key have been used
			usedFrames := make(map[string]int)
			var mostSignificantTimeChange PerformanceTimeChange
			var lastPreCallTime, lastPostCallTime uint32
			for i, frame := range frames {
				// Get matching post-update frame using stack key matching
				key := StackFramesKey(&bb, ProjectFrames(frame.Stack))
				idx := usedFrames[key]
				usedFrames[key] = idx + 1

				var postFrame *CallFrame
				if matchingFrames, exists := postFramesByKey[key]; exists && idx < len(matchingFrames) {
					postFrame = &matchingFrames[idx]
				}

				if postFrame == nil {
					// No matching frame found - this indicates a behavior change
					if i == 0 || len(postResult) == 0 {
						fmt.Printf("WARN: %s->%s Behavior change - no matching call frame found\n",
							postResults.TestFunction.FunctionName, callerIdent)
					}
					preFlat := frame.FieldValues.FlattenFieldValues()
					testDiffCount += len(preFlat)
					continue
				}

				// Compare field values
				preFlat := frame.FieldValues.FlattenFieldValues()
				postFlat := postFrame.FieldValues.FlattenFieldValues()

				sortedNames := slices.Collect(maps.Keys(preFlat))
				slices.Sort(sortedNames)
				for _, fname := range sortedNames {
					value := preFlat[fname]
					vPost, ok := postFlat[fname]
					if !ok {
						fmt.Printf("WARN: %s->%s Field %s became unstable or changed field names\n",
							postResults.TestFunction.FunctionName, callerIdent, fname)
						testDiffCount++
						continue
					} else if value == vPost {
						testSameCount++
						continue
					}
					diffTxt := d.DiffValues(value, vPost)

					fmt.Printf("WARN: %s->%s Field %s changed:\n%s\n",
						postResults.TestFunction.FunctionName, callerIdent, fname, diffTxt)

					callerFields, ok := callerFieldChanges[callerIdent]
					if !ok {
						callerFields = make(map[string]string)
						callerFieldChanges[callerIdent] = callerFields
					}
					callerFields[fname] = diffTxt
					testDiffCount++
				}

				// Compare execution times between calls
				preTime := frame.TimeMillis
				postTime := postFrame.TimeMillis
				if preTime > 0 && postTime > 0 && preTime >= lastPreCallTime && postTime >= lastPostCallTime {
					preInterval := preTime - lastPreCallTime
					postInterval := postTime - lastPostCallTime

					if max(1, preInterval)*uint32(timeMultiplier) < postInterval {
						// Performance regression detected
						intervalDiff := int64(postInterval) - int64(preInterval)
						_, _ = fmt.Fprintf(&performanceLogBuffer,
							"WARN: %s->%s Performance regression detected: %dms -> %dms (diff: %dms)\n",
							postResults.TestFunction.FunctionName, callerIdent, preInterval, postInterval, intervalDiff)

						// Track the most significant regression (largest positive interval diff)
						timeDiff := time.Duration(intervalDiff) * time.Millisecond
						if timeDiff > mostSignificantTimeChange.TimeDiff {
							mostSignificantTimeChange = PerformanceTimeChange{
								TimeDiff:   timeDiff,
								PreTimeMs:  preInterval,
								PostTimeMs: postInterval,
							}
						}
					} else if preInterval > max(1, postInterval)*uint32(timeMultiplier) {
						// Performance improvement detected
						intervalDiff := int64(postInterval) - int64(preInterval)
						_, _ = fmt.Fprintf(&performanceLogBuffer,
							"%s->%s Performance improvement detected: %dms -> %dms (diff: %dms)\n",
							postResults.TestFunction.FunctionName, callerIdent, preInterval, postInterval, intervalDiff)

						// Track the most significant improvement (largest negative interval diff)
						timeDiff := time.Duration(intervalDiff) * time.Millisecond
						if mostSignificantTimeChange.TimeDiff == 0 || timeDiff < mostSignificantTimeChange.TimeDiff {
							mostSignificantTimeChange = PerformanceTimeChange{
								TimeDiff:   timeDiff,
								PreTimeMs:  preInterval,
								PostTimeMs: postInterval,
							}
						}
					}
				}

				// Update last call times for next iteration
				lastPreCallTime = preTime
				lastPostCallTime = postTime
			}

			// Store the most significant time change for this caller
			if mostSignificantTimeChange.TimeDiff != 0 {
				callerTimeChanges[callerIdent] = mostSignificantTimeChange
			}
		}

		comparePanics := func(preMap, postMap map[string][]string, typ string) {
			for ident, preList := range preMap {
				counts := bulk.SliceToCounts(postMap[ident])
				for _, m := range preList {
					if counts[m] > 0 {
						counts[m]--
					} else {
						fmt.Printf("WARN: %s->%s %s panic removed: %s\n", postResults.TestFunction.FunctionName, ident, typ, m)
						testDiffCount++
					}
				}
				for msg, c := range counts {
					for ; c > 0; c-- {
						fmt.Printf("WARN: %s->%s %s panic added: %s\n", postResults.TestFunction.FunctionName, ident, typ, msg)
						testDiffCount++
					}
				}
			}
			for ident, list := range postMap {
				if _, ok := preMap[ident]; ok {
					continue
				}
				for _, m := range list {
					fmt.Printf("WARN: %s->%s %s panic added: %s\n", postResults.TestFunction.FunctionName, ident, typ, m)
					testDiffCount++
				}
			}
		}

		comparePanics(preResults.ProjectPanics, postResults.ProjectPanics, "project")
		comparePanics(preResults.ModulePanics, postResults.ModulePanics, "module")

		if !preResults.TestFailure && postResults.TestFailure {
			testRegressionCount++
			fmt.Printf("WARN: Test regression after update: %s\n", postResults.TestFunction.FunctionName)
		}
		fmt.Printf("Test %s consistency: %d/%d\n",
			postResults.TestFunction.FunctionName, testSameCount, testSameCount+testDiffCount)
		sameCount += testSameCount
		diffCount += testDiffCount
		// We need to avoid retaining the full preResults and postResults here, too much memory
		// TODO - improve the ergonomics
		preResults.CallerResults = nil
		preResults.ProjectPanics = nil
		preResults.ModulePanics = nil
		postResults.CallerResults = nil
		postResults.ProjectPanics = nil
		postResults.ModulePanics = nil
		testReports[i] = TestReport{
			OriginalResult:      preResults,
			PostUpdateResult:    postResults,
			CallerFieldChanges:  callerFieldChanges,
			CallerTimeChanges:   callerTimeChanges,
			TestRegressionCount: testRegressionCount,
			SameFieldCount:      testSameCount,
			DiffFieldCount:      testDiffCount,
		}
	}

	if performanceLogBuffer.Len() > 0 {
		fmt.Print(performanceLogBuffer.String())
	}

	return sameCount, diffCount, testReports, nil
}

func (d *DefaultTestResultAnalyzer) loadTestResult(storage Storage, funcIdent string) (TestResult, bool, error) {
	preResultBlob, ok, err := storage.LoadState(funcIdent)
	if err != nil {
		return TestResult{}, false, fmt.Errorf("error loading results: %w", err)
	} else if !ok {
		return TestResult{}, false, nil
	}
	var result TestResult
	if err := result.UnmarshalMsgpack(preResultBlob); err != nil {
		return TestResult{}, false, fmt.Errorf("error unmarshalling results: %w", err)
	}
	return result, true, nil
}

// DefaultStorageProvider provides the standard implementation of StorageProvider using BadgerDB.
type DefaultStorageProvider struct {
	Path    string
	CacheMB int
	store   Storage
}

func (d *DefaultStorageProvider) NewStorage() (Storage, error) {
	if d.store == nil {
		if d.Path == "" {
			d.Path = filepath.Join(os.TempDir(),
				fmt.Sprintf("lens_state-%d-%s",
					os.Getpid(), strconv.FormatInt(time.Now().UnixNano(), 16)))
		}
		store, err := NewBadgerStorage(d.Path, d.CacheMB)
		if err != nil {
			return nil, err
		}
		d.store = store
	}
	return d.store, nil
}

// SingletonStorageProvider is a StorageProvider that returns a single consistent storage instance.
type SingletonStorageProvider struct {
	Store Storage
}

func (s *SingletonStorageProvider) NewStorage() (Storage, error) {
	return s.Store, nil
}

// DefaultReportWriter provides the standard implementation of ReportWriter.
type DefaultReportWriter struct{}

func (d *DefaultReportWriter) WriteReportFiles(jsonPath, chartPath string, startTime time.Time,
	analysisDuration, testDiscoveryDuration, fieldCheckDuration, mutationDuration time.Duration,
	changedModules []ModuleChange, checkedModules []string, moduleChangeFuncCount, moduleChangesReachedInTesting int,
	projectFieldChecks int, projectCallingFunctions []*CallerFunction, relevantTestFunctions []*TestFunction,
	testFieldSameCount, testFieldDiffCount int, testResults []TestReport,
	globalMutations MutationResult) error {
	reachableModuleFunctionsIdents, relevantProjectFunctionIdents, relevantTestFunctionsIdents,
		performanceChanges, testDetails, rootM, syntheticTestFuncCount := PrepareReportData(
		changedModules, projectCallingFunctions, relevantTestFunctions, testResults, moduleChangeFuncCount)

	err := writeReportJSON(jsonPath, startTime, analysisDuration, testDiscoveryDuration, fieldCheckDuration, mutationDuration,
		rootM.Name, rootM.PriorVersion, rootM.NewVersion,
		checkedModules, moduleChangeFuncCount, moduleChangesReachedInTesting,
		reachableModuleFunctionsIdents,
		relevantProjectFunctionIdents,
		projectFieldChecks, relevantTestFunctionsIdents, testFieldSameCount, testFieldDiffCount,
		syntheticTestFuncCount, globalMutations, performanceChanges, testDetails)
	if err != nil {
		return err
	}

	err = writeReportCharts(chartPath, rootM.Name, rootM.PriorVersion, rootM.NewVersion,
		moduleChangeFuncCount, len(reachableModuleFunctionsIdents), moduleChangesReachedInTesting,
		testFieldSameCount, testFieldDiffCount, testResults, globalMutations)
	if err != nil {
		return err
	}
	return nil
}

// AnalysisEngine orchestrates module change analysis, testing, and reporting.
type AnalysisEngine struct {
	Config                 *Config
	ModuleChangeProvider   ModuleChangeProvider
	CallerAnalysisProvider CallerAnalysisProvider
	TestProvider           TestProvider
	UpdateAnalysisProvider UpdateAnalysisProvider
	MutationTester         MutationTester
	TestResultAnalyzer     TestResultAnalyzer
	StorageProvider        StorageProvider
	ReportWriter           ReportWriter
}

// NewAnalysisEngine creates an AnalysisEngine with default providers.
func NewAnalysisEngine(config *Config) *AnalysisEngine {
	return &AnalysisEngine{
		Config:                 config,
		ModuleChangeProvider:   &DefaultModuleChangeProvider{},
		CallerAnalysisProvider: &DefaultCallerAnalysisProvider{},
		TestProvider:           &DefaultTestProvider{},
		UpdateAnalysisProvider: &DefaultUpdateAnalysisProvider{},
		MutationTester:         &DefaultMutationTester{},
		TestResultAnalyzer:     &DefaultTestResultAnalyzer{},
		StorageProvider: &DefaultStorageProvider{
			CacheMB: config.CacheMB,
		},
		ReportWriter: &DefaultReportWriter{},
	}
}

// NewAnalysisEngineWithProviders creates an AnalysisEngine using the supplied providers.
func NewAnalysisEngineWithProviders(config *Config, moduleChangeProvider ModuleChangeProvider,
	callerAnalysisProvider CallerAnalysisProvider, testProvider TestProvider,
	updateAnalysisProvider UpdateAnalysisProvider, mutationTester MutationTester,
	testResultAnalyzer TestResultAnalyzer, storageProvider StorageProvider,
	reportWriter ReportWriter) *AnalysisEngine {
	engine := NewAnalysisEngine(config)
	if moduleChangeProvider != nil {
		engine.ModuleChangeProvider = moduleChangeProvider
	}
	if callerAnalysisProvider != nil {
		engine.CallerAnalysisProvider = callerAnalysisProvider
	}
	if testProvider != nil {
		engine.TestProvider = testProvider
	}
	if updateAnalysisProvider != nil {
		engine.UpdateAnalysisProvider = updateAnalysisProvider
	}
	if mutationTester != nil {
		engine.MutationTester = mutationTester
	}
	if testResultAnalyzer != nil {
		engine.TestResultAnalyzer = testResultAnalyzer
	}
	if storageProvider != nil {
		engine.StorageProvider = storageProvider
	}
	if reportWriter != nil {
		engine.ReportWriter = reportWriter
	}
	return engine
}

// Run executes the analysis workflow using configured providers.
func (e *AnalysisEngine) Run() error {
	startTime := time.Now()

	if err := e.Config.Prepare(); err != nil {
		return err
	}

	if e.Config.TmpCopy {
		cleanup, err := e.setupTempEnvironment()
		if err != nil {
			return err
		}
		defer cleanup()
	}

	// Use ModuleChangeProvider for module change analysis
	initialModules, err := e.parseInitialModules()
	if err != nil {
		return err
	} else if len(initialModules.changedModules) == 0 {
		log.Printf("No direct changed modules, exiting")
		return nil
	}

	// Analyze the changes for the updated module
	moduleChanges, checkedModuleNames, err :=
		e.ModuleChangeProvider.AnalyzeModuleChanges(*e.Config, initialModules.analyzeExpandTransitive,
			initialModules.changedModules, initialModules.neighbourRadius)
	if err != nil {
		errStr := err.Error()
		for _, cm := range initialModules.changedModules {
			if !strings.Contains(errStr, cm.Name) {
				continue
			}
			if strings.Contains(errStr, cm.PriorVersion) {
				return fmt.Errorf("module %s@%s not found on disk, run: go install %s@%s",
					cm.Name, cm.PriorVersion, cm.Name, cm.PriorVersion)
			} else if strings.Contains(errStr, cm.NewVersion) {
				return fmt.Errorf("module %s@%s not found on disk, run: go install %s@%s",
					cm.Name, cm.NewVersion, cm.Name, cm.NewVersion)
			}
		}
		return fmt.Errorf("error analyzing changes %w", err)
	}
	defer e.ModuleChangeProvider.Cleanup()
	if len(moduleChanges) == 0 {
		log.Printf("Module has no changed functions, exiting")
		analysisEndTime := time.Now()
		return e.ReportWriter.WriteReportFiles(e.Config.ReportJsonFile, e.Config.ReportChartsFile,
			startTime, analysisEndTime.Sub(startTime), 0, 0, 0,
			initialModules.changedModules, checkedModuleNames, 0, 0,
			0, nil, nil,
			0, 0, nil, MutationResult{})
	}
	log.Printf("Changed function count: %d", len(moduleChanges))
	if logFunctionCallChains {
		for _, fn := range moduleChanges {
			fmt.Println(fn.ShortIdent())
		}
	}

	// Perform static analysis on the project to determine which functions call into changed module functions
	callingFunctions, reachableModuleChanges, err :=
		e.CallerAnalysisProvider.PerformCallerStaticAnalysis(*e.Config, moduleChanges)
	if err != nil {
		return fmt.Errorf("error analyzing project callers: %w", err)
	}
	analysisEndTime := time.Now()
	defer e.CallerAnalysisProvider.Cleanup()
	if len(callingFunctions) == 0 {
		log.Printf("Module changes are not reachable by project, exiting")
		return e.ReportWriter.WriteReportFiles(e.Config.ReportJsonFile, e.Config.ReportChartsFile,
			startTime, analysisEndTime.Sub(startTime), 0, 0, 0,
			initialModules.changedModules, checkedModuleNames, 0, 0,
			0, callingFunctions, nil,
			0, 0, nil, MutationResult{})
	}
	log.Printf("Identified change entry point count: %d", len(callingFunctions))
	if logFunctionCallChains {
		for _, caller := range callingFunctions {
			fmt.Printf("%s -> %s\n", caller.ShortIdent(), caller.ChangeFunctionIdents())
		}
	}

	// Analyze test functions to see which tests exercise these caller functions
	testFunctions, err := e.TestProvider.ProvideTests(*e.Config, callingFunctions)
	testDiscoveryEndTime := time.Now()
	if err != nil {
		return fmt.Errorf("error providing tests: %w", err)
	}
	defer e.TestProvider.Cleanup()
	log.Printf("Relevant test function count: %d", len(testFunctions))
	if len(testFunctions) == 0 {
		log.Printf("Unable to find or create relevant test functions, exiting...")
		return e.ReportWriter.WriteReportFiles(e.Config.ReportJsonFile, e.Config.ReportChartsFile,
			startTime, analysisEndTime.Sub(startTime), testDiscoveryEndTime.Sub(analysisEndTime), 0, 0,
			initialModules.changedModules, checkedModuleNames, len(moduleChanges), 0,
			0, callingFunctions, testFunctions,
			0, 0, nil, MutationResult{})
	}
	if logFunctionCallChains {
		for _, test := range testFunctions {
			fmt.Printf("%s -> %s\n", test.ShortIdent(), test.TargetFunctionIdents())
		}
	}

	// Run the ast monitoring session for test execution and field recording
	// We need to allocate special storage to hold all of the data captured
	storage, err := e.StorageProvider.NewStorage()
	if err != nil {
		return fmt.Errorf("error opening storage: %w", err)
	}
	defer storage.Close()
	projectFieldChecks, moduleChangesReachedInTesting, preResults, postResults, err :=
		e.UpdateAnalysisProvider.RunModuleUpdateAnalysis(*e.Config, storage,
			initialModules.changedModules, reachableModuleChanges, callingFunctions, testFunctions)
	if err != nil {
		return fmt.Errorf("error during monitored test execution: %w", err)
	}
	defer e.UpdateAnalysisProvider.Cleanup()
	testExecutionAnalysisEndTime := time.Now()

	// Add mutations in the module changes and run the identified tests
	var globalMutations MutationResult
	runMutationTesting := e.Config.MutationScope != noneScopeFlag
	if runMutationTesting {
		log.Printf("Starting mutation testing (may be slow)")
		lineScopedMutations := e.Config.MutationScope == lineScopeFlag || e.Config.MutationScope == areaScopeFlag
		fastMutations := e.Config.MutationMode != fullScopeFlag
		targetedMutationTests := e.Config.MutationTests != fullScopeFlag
		globalMutations, err = e.MutationTester.RunMutationTesting(*e.Config,
			fastMutations, lineScopedMutations, targetedMutationTests, moduleChanges, testFunctions)
		if err != nil {
			return fmt.Errorf("error during mutation testing: %w", err)
		}
		defer e.MutationTester.Cleanup()
	}
	mutationEndTime := time.Now()

	// TODO - track panic changes different from field changes
	sameCount, diffCount, testReports, err :=
		e.TestResultAnalyzer.CompareTestResults(preResults, postResults, e.Config.TimeMultiplier)
	if err != nil {
		return fmt.Errorf("error comparing test results: %w", err)
	}
	log.Printf("Total fields unchanged: %d, fields changed: %d", sameCount, diffCount)
	log.Printf("Module changes checked: %d, reached: %d",
		len(reachableModuleChanges), moduleChangesReachedInTesting)

	// Use ReportWriter
	err = e.ReportWriter.WriteReportFiles(e.Config.ReportJsonFile, e.Config.ReportChartsFile, startTime,
		analysisEndTime.Sub(startTime),
		testDiscoveryEndTime.Sub(analysisEndTime),
		testExecutionAnalysisEndTime.Sub(testDiscoveryEndTime),
		mutationEndTime.Sub(testExecutionAnalysisEndTime),
		initialModules.changedModules, checkedModuleNames, len(moduleChanges), moduleChangesReachedInTesting,
		projectFieldChecks, callingFunctions, testFunctions, sameCount, diffCount, testReports,
		globalMutations)
	if err != nil {
		return fmt.Errorf("error writing report files: %w", err)
	}

	log.Println("PatchLens Analysis completed normally")
	return nil
}

type initialModulesResult struct {
	changedModules          []ModuleChange
	analyzeExpandTransitive bool
	neighbourRadius         int
}

func (e *AnalysisEngine) parseInitialModules() (*initialModulesResult, error) {
	// Locate go.mod files for the project (workspace aware)
	goModPaths, err := ProjectGoModFiles(e.Config.AbsProjDir)
	if err != nil {
		return nil, fmt.Errorf("go.mod or go.work file not readable in project directory: %s", e.Config.AbsProjDir)
	}

	var analyzeExpandTransitive bool
	var changedModules []ModuleChange
	if len(e.Config.TargetModules) > 0 {
		analyzeExpandTransitive = true // expand to include transitive modules to the specified modules
		changedModules = make([]ModuleChange, 0, len(e.Config.TargetModules))
		for _, targetModule := range e.Config.TargetModules {
			// Parse go.mod to find the current version
			oldVer, indirect, err := FindModuleVersion(e.Config.AbsProjDir, targetModule.Name)
			if err != nil {
				return nil, fmt.Errorf("error reading go.mod: %w", err)
			} else if oldVer == "" {
				log.Printf("WARN: Module %s not found in workspace", targetModule.Name)
				continue
			}
			changedModules = append(changedModules, ModuleChange{
				Name:         targetModule.Name,
				PriorVersion: oldVer,
				NewVersion:   targetModule.Version,
				Indirect:     indirect,
			})
		}
	} else if e.Config.UpdatedGoModFile != "" {
		if len(goModPaths) != 1 {
			return nil, errors.New("-gomod unsupported for go.work projects")
		}
		changedModules, err = DiffModulesFromGoModFiles(goModPaths[0], e.Config.UpdatedGoModFile)
		if err != nil {
			return nil, fmt.Errorf("error diffing go.mod files: %w", err)
		}
	} else if e.Config.UpdatedGoWorkFile != "" {
		changedModules, err = DiffModulesFromGoWorkFiles(e.Config.AbsProjDir, e.Config.UpdatedGoWorkFile)
		if err != nil {
			return nil, fmt.Errorf("error diffing go.work files: %w", err)
		}
	}

	var neighbourRadius int
	if e.Config.MutationScope == areaScopeFlag {
		neighbourRadius = 1
	}

	return &initialModulesResult{
		changedModules:          changedModules,
		analyzeExpandTransitive: analyzeExpandTransitive,
		neighbourRadius:         neighbourRadius,
	}, nil
}

func (e *AnalysisEngine) setupTempEnvironment() (func(), error) {
	tempRoot, err := os.MkdirTemp("", "patchlens-*")
	if err != nil {
		return nil, fmt.Errorf("unable to create temp dir: %w", err)
	}
	cleanup := func() {
		if err := WriteChmod(context.Background(), tempRoot); err != nil {
			log.Printf("%sFailed to Chmod temp dir for cleanup: %v", ErrorLogPrefix, err)
		}
		if err := os.RemoveAll(tempRoot); err != nil {
			log.Printf("%sFailed to remove temp dir %s: %v", ErrorLogPrefix, tempRoot, err)
		}
	}

	fmt.Printf("Copying files for analysis")
	const logSize = 1024 * 1024 * 200
	var logCopied atomic.Int64
	copyProgressHandler := func(target string, info os.FileInfo) {
		if !info.IsDir() {
			logCopied.Add(info.Size())
			for {
				if current := logCopied.Load(); current > logSize {
					if logCopied.CompareAndSwap(current, current-logSize) {
						fmt.Printf(".")
					}
				} else {
					break
				}
			}
		}
	}

	ctx := context.Background()
	newProj := filepath.Join(tempRoot, "project")
	if err := CopyDir(ctx, e.Config.AbsProjDir, newProj, copyProgressHandler); err != nil {
		return nil, fmt.Errorf("unable to copy project: %w", err)
	}
	e.Config.AbsProjDir = newProj

	newGOPATH := filepath.Join(tempRoot, "gopath")
	if err := CopyDir(ctx, e.Config.Gopath, newGOPATH, copyProgressHandler); err != nil {
		return nil, fmt.Errorf("unable to copy GOPATH: %w", err)
	}
	if !strings.HasPrefix(e.Config.Gomodcache, e.Config.Gopath) {
		newModCache := filepath.Join(tempRoot, "gomodcache")
		if err := CopyDir(ctx, e.Config.Gomodcache, newModCache, copyProgressHandler); err != nil {
			return nil, fmt.Errorf("unable to copy GOMODCACHE: %w", err)
		}
		e.Config.Gomodcache = newModCache
	} else {
		e.Config.Gomodcache = filepath.Join(newGOPATH, "pkg", "mod")
	}
	e.Config.Gopath = newGOPATH
	fmt.Println()
	return cleanup, nil
}

// Prepare performs comprehensive validation and preparation of the configuration
func (c *Config) Prepare() error {
	if c.prepared {
		return errors.New("config has already been prepared")
	}

	// Validate required fields
	if c.ProjectDir == "" {
		return errors.New("project directory is required")
	} else if c.ModuleVersionFlag == "" && c.ModulesVersionFlag == "" && c.UpdatedGoModFile == "" && c.UpdatedGoWorkFile == "" {
		return errors.New("must specify one of: -module, -modules, -gomod, or -gowork")
	} else if c.UpdatedGoModFile != "" && c.UpdatedGoWorkFile != "" {
		return errors.New("-gomod and -gowork are mutually exclusive")
	}

	// Resolve absolute project directory
	absProjDir, err := filepath.Abs(c.ProjectDir)
	if err != nil {
		return fmt.Errorf("error resolving project directory: %w", err)
	}
	c.AbsProjDir = absProjDir

	// Parse and validate target modules
	if c.ModuleVersionFlag != "" {
		targetModule, err := parseTargetModule(c.ModuleVersionFlag)
		if err != nil {
			return fmt.Errorf("invalid module version format: %w", err)
		}
		c.TargetModules = append(c.TargetModules, targetModule)
	}

	if c.ModulesVersionFlag != "" {
		modules := strings.Split(c.ModulesVersionFlag, ",")
		for _, module := range modules {
			module = strings.TrimSpace(module)
			if module == "" {
				return errors.New("empty module specification in modules list")
			}
			targetModule, err := parseTargetModule(module)
			if err != nil {
				return fmt.Errorf("invalid module version format in modules list: %w", err)
			}
			c.TargetModules = append(c.TargetModules, targetModule)
		}
	}

	// Validate file paths exist if specified
	if c.UpdatedGoModFile != "" {
		if err := c.validateFilePath(c.UpdatedGoModFile, "go.mod"); err != nil {
			return fmt.Errorf("invalid go.mod file: %w", err)
		}
	} else if c.UpdatedGoWorkFile != "" {
		if err := c.validateFilePath(c.UpdatedGoWorkFile, "go.work"); err != nil {
			return fmt.Errorf("invalid go.work file: %w", err)
		}
	}

	// Validate numeric fields are within reasonable ranges
	if c.AstMonitorPort < 1024 || c.AstMonitorPort > 65535 {
		return fmt.Errorf("ast monitor port must be between 1024 and 65535, got %d", c.AstMonitorPort)
	} else if c.MaxFieldRecurse < 1 || c.MaxFieldRecurse > 100 {
		return fmt.Errorf("max field recurse must be between 1 and 100, got %d", c.MaxFieldRecurse)
	} else if c.MaxFieldLen < 1 || c.MaxFieldLen > 1048576 { // 1MB limit
		return fmt.Errorf("max field length must be between 1 and 1048576, got %d", c.MaxFieldLen)
	} else if c.CacheMB < 1 || c.CacheMB > 10240 { // 10GB limit
		return fmt.Errorf("cache size must be between 1 and 10240 MB, got %d", c.CacheMB)
	} else if c.TimeMultiplier < 1 || c.TimeMultiplier > 100 {
		return fmt.Errorf("time multiplier must be between 1 and 100, got %d", c.TimeMultiplier)
	}

	// Validate enum-like string fields
	validMutationScopes := map[string]bool{"function": true, lineScopeFlag: true, areaScopeFlag: true, noneScopeFlag: true}
	if !validMutationScopes[c.MutationScope] {
		return fmt.Errorf("invalid mutation scope '%s', must be one of: function, line, area, none", c.MutationScope)
	}
	validMutationModes := map[string]bool{fullScopeFlag: true, "fast": true}
	if !validMutationModes[c.MutationMode] {
		return fmt.Errorf("invalid mutation mode '%s', must be one of: full, fast", c.MutationMode)
	}
	validMutationTests := map[string]bool{fullScopeFlag: true, "targeted": true}
	if !validMutationTests[c.MutationTests] {
		return fmt.Errorf("invalid mutation tests '%s', must be one of: full, targeted", c.MutationTests)
	}

	// Validate output file paths are writable (basic check)
	if c.ReportJsonFile != "" {
		if err := c.validateOutputPath(c.ReportJsonFile); err != nil {
			return fmt.Errorf("invalid JSON report file path: %w", err)
		}
	} else if c.ReportChartsFile != "" {
		if err := c.validateOutputPath(c.ReportChartsFile); err != nil {
			return fmt.Errorf("invalid charts report file path: %w", err)
		}
	}

	c.prepared = true
	return nil
}

// parseTargetModule parses a module version string and returns a TargetModule struct
func parseTargetModule(moduleVersion string) (TargetModule, error) {
	parts := strings.SplitN(moduleVersion, "@", 2)
	if len(parts) != 2 {
		return TargetModule{}, fmt.Errorf("module version must be in format 'module@version', got '%s'", moduleVersion)
	}

	moduleName, version := parts[0], parts[1]
	if moduleName == "" {
		return TargetModule{}, errors.New("module name cannot be empty")
	} else if version == "" {
		return TargetModule{}, errors.New("version cannot be empty")
	} else if !strings.Contains(moduleName, "/") && !strings.Contains(moduleName, ".") {
		return TargetModule{}, fmt.Errorf("module name '%s' appears invalid (should contain domain or path)", moduleName)
	}

	return TargetModule{
		Name:    moduleName,
		Version: version,
	}, nil
}

// validateFilePath validates that a file path exists and is readable
func (c *Config) validateFilePath(path, expectedType string) error {
	info, err := os.Stat(path)
	if err != nil {
		return fmt.Errorf("file does not exist or is not accessible: %w", err)
	} else if info.IsDir() {
		return fmt.Errorf("path is a directory, expected a %s file", expectedType)
	}

	// Try to open the file to check readability
	file, err := os.Open(path)
	if err != nil {
		return fmt.Errorf("file is not readable: %w", err)
	}
	if err := file.Close(); err != nil {
		return fmt.Errorf("failed to close file: %w", err)
	}

	return nil
}

// validateOutputPath validates that an output file path can be written to
func (c *Config) validateOutputPath(path string) error {
	dir := filepath.Dir(path)

	// Check if directory exists, if not try to create it
	if _, err := os.Stat(dir); os.IsNotExist(err) {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("cannot create output directory '%s': %w", dir, err)
		}
	}

	// Check if we can write to the directory
	testFile := filepath.Join(dir, ".write_test")
	file, err := os.Create(testFile)
	if err != nil {
		return fmt.Errorf("cannot write to output directory '%s': %w", dir, err)
	}
	_ = file.Close()
	return os.Remove(testFile)
}
