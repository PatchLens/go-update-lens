package lens

import (
	"encoding/json"
	"fmt"
	"maps"
	"os"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/go-analyze/charts"
)

const bottomTableMaxRecords = 10

// chart color constants
var greenTextColor = charts.ColorGreenAlt3
var orangeTextColor = charts.ColorOrangeAlt1.WithAdjustHSL(0, .2, 0)
var redTextColor = charts.ColorRed.WithAdjustHSL(0, .1, -.1)

// ReportMetrics contains run and validation metrics.
type ReportMetrics struct {
	GeneratedAt           time.Time         `json:"generated_at"`
	RunDuration           int64             `json:"run_ms"`
	AnalysisDuration      int64             `json:"analysis_ms"`
	TestDiscoveryDuration int64             `json:"test_discovery_ms"`
	FieldCheckDuration    int64             `json:"field_check_ms"`
	MutationDuration      int64             `json:"mutation_ms"`
	Module                ModuleMetrics     `json:"module"`
	Validation            ValidationMetrics `json:"validation"`
}

// ModuleMetrics summarizes module change statistics.
type ModuleMetrics struct {
	RootModuleName            string   `json:"root_module_name"`
	RootModuleStartVersion    string   `json:"root_module_start_version"`
	RootModuleUpdateVersion   string   `json:"root_module_update_version"`
	ChangedModules            []string `json:"changed_modules"`
	ChangedModuleCount        int      `json:"changed_module_count"`
	ChangeFuncCount           int      `json:"changed_function_count"`
	ReachableChangedFunctions []string `json:"reachable_changed_functions"`
	ReachableChangedFuncCount int      `json:"reachable_changed_function_count"`
}

// ValidationMetrics aggregates test and mutation statistics.
type ValidationMetrics struct {
	RelevantProjectFunctions   []string            `json:"relevant_project_functions"`
	RelevantProjectFuncCount   int                 `json:"relevant_project_function_count"`
	RelevantTestFunctions      []string            `json:"relevant_test_functions"`
	RelevantTestFuncCount      int                 `json:"relevant_test_function_count"`
	ProjectFieldCheckPoints    int                 `json:"project_field_check_point_count"`
	ModuleChangeHitInTestCount int                 `json:"module_change_hit_in_test_count"`
	TestFieldMatchCount        int                 `json:"test_field_match_count"`
	TestFieldDiffCount         int                 `json:"test_field_diff_count"`
	GeneratedTestFuncCount     int                 `json:"generated_test_function_count"`
	MutationCount              int                 `json:"mutation_count"`
	MutationsSquashed          int                 `json:"mutations_squashed"`
	PerformanceChanges         []PerformanceChange `json:"performance_changes"` // detected performance changes
	TestDetails                []TestDetail        `json:"test_details"`
}

// PerformanceChange represents a performance change detected between test runs
type PerformanceChange struct {
	TestFunctionIdent string `json:"test_function_ident"` // identifier of the test function
	TestFunctionName  string `json:"test_function_name"`  // name of the test function
	CallerIdent       string `json:"caller_ident"`        // identifier of the caller function
	TimeDiffMs        int64  `json:"time_diff_ms"`        // time interval difference in milliseconds (positive = slower, negative = faster)
	PreTimeMs         uint32 `json:"pre_time_ms"`         // call interval before change in milliseconds
	PostTimeMs        uint32 `json:"post_time_ms"`        // call interval after change in milliseconds
}

// PerformanceTimeChange stores detailed timing information for a caller
type PerformanceTimeChange struct {
	TimeDiff   time.Duration // time interval difference (positive = slower, negative = faster)
	PreTimeMs  uint32        // call interval before change in milliseconds
	PostTimeMs uint32        // call interval after change in milliseconds
}

// TestDetail summarizes per-test changes.
type TestDetail struct {
	TestFunctionIdent    string                       `json:"test_function_ident"` // ident of the test
	TestFunctionName     string                       `json:"test_function_name"`
	BaselineFailure      bool                         `json:"baseline_failure"`
	PassRegression       bool                         `json:"pass_regression"`         // Did the test fail only after the change
	DiffFieldCount       int                          `json:"diff_field_count"`        // how many fields changed
	ModuleChangeHitCount int                          `json:"module_change_hit_count"` // how many module functions that test reached
	FieldChanges         map[string]map[string]string `json:"field_changes"`           // [callerIdent][fieldName]valueDiff
}

// TestReport compares test results.
type TestReport struct {
	OriginalResult      TestResult // OriginalResult must be used to get mutation hit counts
	PostUpdateResult    TestResult
	CallerFieldChanges  map[string]map[string]string     // [callerIdent][fieldName]valueDiff
	CallerTimeChanges   map[string]PerformanceTimeChange // [callerIdent]detailed timing info
	TestRegressionCount int
	SameFieldCount      int
	DiffFieldCount      int
	// ExtensionDataDiff contains differences in extension data between pre/post update.
	// Key is the extension namespace (e.g., "security"), value is a human-readable diff summary.
	// Extensions can provide custom diff logic via DefaultTestResultAnalyzer.ExtensionDataAnalyzer.
	ExtensionDataDiff map[string]string
}

// ReportMap represents a report as an extensible map structure.
// Custom implementations can add additional fields before writing to JSON.
type ReportMap map[string]interface{}

// PrepareReportData prepares all the data needed for report generation.
func PrepareReportData(changedModules []ModuleChange, projectCallingFunctions []*CallerFunction,
	relevantTestFunctions []*TestFunction, testResults []TestReport,
	moduleChangeFuncCount int) (reachableModuleFunctionsIdents []string,
	relevantProjectFunctionIdents []string, relevantTestFunctionsIdents []string,
	performanceChanges []PerformanceChange, testDetails []TestDetail,
	rootM ModuleChange, syntheticTestFuncCount int) {
	// Prepare relevant function identifiers
	relevantProjectFunctionMap := make(map[string]bool, len(projectCallingFunctions))
	reachableModuleFunctionMap := make(map[string]bool, moduleChangeFuncCount)
	for _, f := range projectCallingFunctions {
		for _, change := range f.ChangeFunctions {
			reachableModuleFunctionMap[change.FunctionIdent] = true
		}
		relevantProjectFunctionMap[f.FunctionIdent] = true
	}

	relevantProjectFunctionIdents = slices.Collect(maps.Keys(relevantProjectFunctionMap))
	reachableModuleFunctionsIdents = slices.Collect(maps.Keys(reachableModuleFunctionMap))

	relevantTestFunctionsIdents = make([]string, len(relevantTestFunctions))
	for i := range relevantTestFunctions {
		relevantTestFunctionsIdents[i] = relevantTestFunctions[i].FunctionIdent
		if strings.HasPrefix(relevantTestFunctions[i].FunctionName, GeneratedTestFunctionPrefix) {
			syntheticTestFuncCount++
		}
	}
	slices.SortFunc(testResults, func(a, b TestReport) int { // keep consistent order in report
		return strings.Compare(a.OriginalResult.TestFunction.FunctionIdent, b.OriginalResult.TestFunction.FunctionIdent)
	})

	// build per-test metrics
	testDetails = make([]TestDetail, len(testResults))
	for i, tr := range testResults {
		// ensure field changes are minimized
		for k1, v1 := range tr.CallerFieldChanges {
			for k2, v2 := range v1 {
				tr.CallerFieldChanges[k1][k2] = strings.TrimSpace(v2) // may have prefixed tab and / or suffixed newline
			}
		}
		testDetails[i] = TestDetail{
			TestFunctionIdent:    tr.OriginalResult.TestFunction.FunctionIdent,
			TestFunctionName:     tr.OriginalResult.TestFunction.FunctionName,
			BaselineFailure:      tr.OriginalResult.TestFailure,
			PassRegression:       !tr.OriginalResult.TestFailure && tr.PostUpdateResult.TestFailure,
			DiffFieldCount:       tr.DiffFieldCount,
			ModuleChangeHitCount: tr.OriginalResult.ModuleChangesHit,
			FieldChanges:         tr.CallerFieldChanges,
		}

		// Collect performance changes
		if len(tr.CallerTimeChanges) > 0 {
			for callerIdent, timeChange := range tr.CallerTimeChanges {
				performanceChanges = append(performanceChanges, PerformanceChange{
					TestFunctionIdent: tr.OriginalResult.TestFunction.FunctionIdent,
					TestFunctionName:  tr.OriginalResult.TestFunction.FunctionName,
					CallerIdent:       callerIdent,
					TimeDiffMs:        timeChange.TimeDiff.Milliseconds(),
					PreTimeMs:         timeChange.PreTimeMs,
					PostTimeMs:        timeChange.PostTimeMs,
				})
			}
		}
	}

	rootM = rootModule(changedModules)
	return
}

func rootModule(changedModules []ModuleChange) ModuleChange {
	if len(changedModules) == 1 {
		return changedModules[0]
	}
	var directModule ModuleChange
	for _, m := range changedModules {
		if !m.Indirect {
			if directModule.Name == "" {
				directModule = m
			} else {
				return ModuleChange{} // return empty module to indicate no root module
			}
		}
	}
	return directModule
}

// BuildReportMap creates the report as a ReportMap that can be extended
// by custom implementations before writing to JSON.
func BuildReportMap(startTime time.Time,
	analysisDuration, testDiscoveryDuration, fieldCheckDuration, mutationDuration time.Duration,
	moduleName, startVersion, changeVersion string,
	checkedModules []string, moduleChangeFuncCount, moduleChangesReachedInTesting int,
	reachableModuleFunctionsIdents, relevantProjectFunctionIdents []string,
	projectFieldChecks int,
	relevantTestFunctionsIdents []string, testFieldSameCount, testFieldDiffCount, syntheticTestFuncCount int,
	globalMutations MutationResult, performanceChanges []PerformanceChange, testDetails []TestDetail) (ReportMap, error) {
	report := ReportMetrics{
		GeneratedAt:           startTime,
		RunDuration:           time.Since(startTime).Milliseconds(),
		AnalysisDuration:      analysisDuration.Milliseconds(),
		TestDiscoveryDuration: testDiscoveryDuration.Milliseconds(),
		FieldCheckDuration:    fieldCheckDuration.Milliseconds(),
		MutationDuration:      mutationDuration.Milliseconds(),
		Module: ModuleMetrics{
			RootModuleName:            moduleName,
			RootModuleStartVersion:    startVersion,
			RootModuleUpdateVersion:   changeVersion,
			ChangedModules:            checkedModules,
			ChangedModuleCount:        len(checkedModules),
			ChangeFuncCount:           moduleChangeFuncCount,
			ReachableChangedFunctions: reachableModuleFunctionsIdents,
			ReachableChangedFuncCount: len(reachableModuleFunctionsIdents),
		},
		Validation: ValidationMetrics{
			RelevantProjectFunctions:   relevantProjectFunctionIdents,
			RelevantProjectFuncCount:   len(relevantProjectFunctionIdents),
			RelevantTestFunctions:      relevantTestFunctionsIdents,
			RelevantTestFuncCount:      len(relevantTestFunctionsIdents),
			ProjectFieldCheckPoints:    projectFieldChecks,
			ModuleChangeHitInTestCount: moduleChangesReachedInTesting,
			TestFieldMatchCount:        testFieldSameCount,
			TestFieldDiffCount:         testFieldDiffCount,
			GeneratedTestFuncCount:     syntheticTestFuncCount,
			MutationCount:              globalMutations.MutationCount,
			MutationsSquashed:          globalMutations.SquashedCount,
			PerformanceChanges:         performanceChanges,
			TestDetails:                testDetails,
		},
	}

	// Convert struct to map for extensibility
	reportBytes, err := json.Marshal(report)
	if err != nil {
		return nil, fmt.Errorf("marshal report to bytes failed: %w", err)
	}

	var reportMap ReportMap
	if err := json.Unmarshal(reportBytes, &reportMap); err != nil {
		return nil, fmt.Errorf("unmarshal report to map failed: %w", err)
	}

	return reportMap, nil
}

// WriteToFile writes the report map to a JSON file.
// This method allows custom implementations to write extended reports.
func (rm ReportMap) WriteToFile(path string) error {
	if path == "" {
		return nil
	}

	encodedReport, err := json.MarshalIndent(rm, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal report map failed: %w", err)
	}
	if err := os.WriteFile(path, encodedReport, 0644); err != nil {
		return fmt.Errorf("write report file failed: %w", err)
	}
	return nil
}

func writeReportJSON(path string, startTime time.Time,
	analysisDuration, testDiscoveryDuration, fieldCheckDuration, mutationDuration time.Duration,
	moduleName, startVersion, changeVersion string,
	checkedModules []string, moduleChangeFuncCount, moduleChangesReachedInTesting int,
	reachableModuleFunctionsIdents, relevantProjectFunctionIdents []string,
	projectFieldChecks int,
	relevantTestFunctionsIdents []string, testFieldSameCount, testFieldDiffCount, syntheticTestFuncCount int,
	globalMutations MutationResult, performanceChanges []PerformanceChange, testDetails []TestDetail) error {
	// Build the report map
	reportMap, err := BuildReportMap(startTime,
		analysisDuration, testDiscoveryDuration, fieldCheckDuration, mutationDuration,
		moduleName, startVersion, changeVersion, checkedModules, moduleChangeFuncCount,
		moduleChangesReachedInTesting, reachableModuleFunctionsIdents, relevantProjectFunctionIdents,
		projectFieldChecks, relevantTestFunctionsIdents, testFieldSameCount, testFieldDiffCount,
		syntheticTestFuncCount, globalMutations, performanceChanges, testDetails)
	if err != nil {
		return err
	}

	// Write the map to file
	return reportMap.WriteToFile(path)
}

// RenderReportChartsFromJson takes a ReportMetrics and renders the report to a png.
func RenderReportChartsFromJson(report ReportMetrics) ([]byte, error) {
	// rebuild []TestReport from report.Validation.TestDetails
	testResults := make([]TestReport, len(report.Validation.TestDetails))
	for i, td := range report.Validation.TestDetails {
		orig := TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: td.TestFunctionIdent,
				FunctionName:  td.TestFunctionName,
			},
			TestFailure:      td.BaselineFailure,
			ModuleChangesHit: td.ModuleChangeHitCount,
		}
		post := TestResult{
			TestFunction: MinimumTestFunction{
				FunctionIdent: td.TestFunctionIdent,
				FunctionName:  td.TestFunctionName,
			},
			// PassRegression indicates "original passed, now failed"
			TestFailure: td.PassRegression,
		}
		// Rebuild CallerTimeChanges from PerformanceChanges
		callerTimeChanges := make(map[string]PerformanceTimeChange)
		for _, pc := range report.Validation.PerformanceChanges {
			if pc.TestFunctionIdent == td.TestFunctionIdent {
				callerTimeChanges[pc.CallerIdent] = PerformanceTimeChange{
					TimeDiff:   time.Duration(pc.TimeDiffMs) * time.Millisecond,
					PreTimeMs:  pc.PreTimeMs,
					PostTimeMs: pc.PostTimeMs,
				}
			}
		}

		testResults[i] = TestReport{
			OriginalResult:     orig,
			PostUpdateResult:   post,
			CallerFieldChanges: td.FieldChanges,
			CallerTimeChanges:  callerTimeChanges,
			DiffFieldCount:     td.DiffFieldCount,
		}
	}
	// sort for stable ordering, same as in WriteReportFiles
	slices.SortFunc(testResults, func(a, b TestReport) int {
		return strings.Compare(
			a.OriginalResult.TestFunction.FunctionIdent,
			b.OriginalResult.TestFunction.FunctionIdent,
		)
	})

	painterOpt := charts.PainterOptions{
		OutputFormat: charts.ChartOutputPNG,
		Width:        1024,
		Height:       768,
	}
	return renderReportCharts(painterOpt,
		report.Module.RootModuleName, report.Module.RootModuleStartVersion, report.Module.RootModuleUpdateVersion,
		report.Module.ChangeFuncCount, report.Module.ReachableChangedFuncCount,
		report.Validation.ModuleChangeHitInTestCount,
		report.Validation.TestFieldMatchCount, report.Validation.TestFieldDiffCount,
		testResults, MutationResult{
			MutationCount: report.Validation.MutationCount,
			SquashedCount: report.Validation.MutationsSquashed,
		})
}

func writeReportCharts(path string, moduleName, startVersion, changeVersion string,
	moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
	testFieldSameCount, testFieldDiffCount int, testResults []TestReport,
	globalMutations MutationResult) error {
	var outputType string
	if strings.HasSuffix(path, ".png") {
		outputType = charts.ChartOutputPNG
	} else if strings.HasSuffix(path, ".jpg") || strings.HasSuffix(path, ".jpeg") {
		outputType = charts.ChartOutputJPG
	} else if strings.HasSuffix(path, ".svg") {
		outputType = charts.ChartOutputSVG
	} else {
		return fmt.Errorf("unhandled chart file type: %s", path)
	}

	painterOpt := charts.PainterOptions{
		OutputFormat: outputType,
		Width:        1024,
		Height:       1024,
	}
	if buf, err := renderReportCharts(painterOpt, moduleName, startVersion, changeVersion,
		moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
		testFieldSameCount, testFieldDiffCount, testResults, globalMutations); err != nil {
		return fmt.Errorf("render charts failed: %w", err)
	} else if err = os.WriteFile(path, buf, 0644); err != nil {
		return fmt.Errorf("write chart file failed: %w", err)
	}
	return nil
}

func renderReportCharts(painterOpt charts.PainterOptions, moduleName, startVersion, changeVersion string,
	moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
	testFieldSameCount, testFieldDiffCount int, testResults []TestReport,
	globalMutations MutationResult) ([]byte, error) {
	p := charts.NewPainter(painterOpt)
	if chartBox, err := renderChartsToPainter(p, moduleName, startVersion, changeVersion,
		moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
		testFieldSameCount, testFieldDiffCount, testResults, globalMutations); err != nil {
		return nil, err
	} else if chartBox.Height() < p.Height()-128 || chartBox.Height() > p.Height() {
		// re-render with a smaller painter to better fit the charts
		painterOpt.Height = chartBox.Height()
		p = charts.NewPainter(painterOpt)
		if _, err := renderChartsToPainter(p, moduleName, startVersion, changeVersion,
			moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
			testFieldSameCount, testFieldDiffCount, testResults, globalMutations); err != nil {
			return nil, err
		}
	}
	return p.Bytes()
}

func renderChartsToPainter(p *charts.Painter, moduleName, startVersion, changeVersion string,
	moduleChangeFuncCount, reachableModuleFunctionCount, moduleChangesReachedInTesting,
	testFieldSameCount, testFieldDiffCount int, testResults []TestReport,
	globalMutations MutationResult) (charts.Box, error) {
	// Calculate total performance changes
	var totalPreTime, totalPostTime float64
	for _, tr := range testResults {
		for _, timeChange := range tr.CallerTimeChanges {
			totalPreTime += float64(timeChange.PreTimeMs)
			totalPostTime += float64(timeChange.PostTimeMs)
		}
	}
	timeUnit := "milliseconds"
	if max(totalPreTime, totalPostTime) > 2000 {
		timeUnit = "seconds"
		totalPreTime /= 1000.0
		totalPostTime /= 1000.0
		if max(totalPreTime, totalPostTime) > 120 {
			timeUnit = "minutes"
			totalPreTime /= 60
			totalPostTime /= 60
		}
	}

	const chartPadding = 10
	resultBox := charts.NewBoxEqual(0)
	resultBox.Right = p.Width()
	p.FilledRect(0, 0, p.Width(), p.Height(), charts.ColorWhite, charts.ColorWhite, 0)
	p = p.Child(charts.PainterPaddingOption(charts.NewBox(0, chartPadding, chartPadding, chartPadding)))

	var title string
	var titleBox charts.Box
	var titleBottom int
	titleFont := charts.FontStyle{
		FontSize:  16,
		FontColor: charts.ColorBlack,
		Font:      charts.GetDefaultFont(),
	}
	if moduleName != "" {
		title = moduleName + "@" + startVersion + "->" + changeVersion
		titleBox = p.MeasureText(title, 0, titleFont)
		// title rendered after the charts to ensure it does not get clipped
		titleBottom = titleBox.Height()
		resultBox.Bottom += titleBottom
	}

	// Use layout builder API to create painters for each chart
	const middleUpShift = "-40" // overlap amount between rows
	layoutBuilder := p.LayoutByRows()
	if titleBottom > 0 {
		layoutBuilder = layoutBuilder.RowGap(strconv.Itoa(titleBottom))
	}
	painters, err := layoutBuilder.
		Row().Height("128").Columns("topLeft", "topRight").
		Row().Height("112").RowOffset(middleUpShift).Columns("down1Left", "down1Right").
		Row().Height("120").RowOffset(middleUpShift).Columns("down2").
		Row().Columns("bottom"). // single large painter at the bottom with all remaining space
		Build()
	if err != nil {
		return resultBox, fmt.Errorf("error building chart layout: %w", err)
	}
	topLeft := painters["topLeft"]
	topRight := painters["topRight"]
	down1Left := painters["down1Left"]
	down1Right := painters["down1Right"]
	down2 := painters["down2"]
	bottom := painters["bottom"]

	barGaugeThemeGreenRed := charts.GetTheme(charts.ThemeLight).
		WithBackgroundColor(charts.ColorTransparent).
		WithSeriesColors([]charts.Color{
			charts.ColorGreenAlt1,
			charts.ColorRed,
		})
	barGaugeThemeGreenYellowRed := charts.GetTheme(charts.ThemeLight).
		WithBackgroundColor(charts.ColorTransparent).
		WithSeriesColors([]charts.Color{
			charts.ColorGreenAlt1,
			{ /* Golden yellow */ R: 220, G: 210, B: 100, A: 255},
			charts.ColorRed,
		})

	topLeftOpt := charts.NewHorizontalBarChartOptionWithData([][]float64{
		{float64(reachableModuleFunctionCount)}, {float64(moduleChangeFuncCount - reachableModuleFunctionCount)},
	})
	topLeftOpt.StackSeries = charts.Ptr(true)
	topLeftOpt.Theme = barGaugeThemeGreenYellowRed
	topLeftOpt.Title.Text = "Module Change Impact"
	topLeftOpt.XAxis.Unit = axisUnitForMax(moduleChangeFuncCount)
	topLeftOpt.YAxis.Show = charts.Ptr(false)
	topLeftOpt.SeriesList[1].Label.Show = charts.Ptr(true)
	topLeftOpt.SeriesList[1].Label.FontStyle.FontColor = firstValueSeriesRankColor(topLeftOpt.Theme, topLeftOpt.SeriesList)
	topLeftOpt.SeriesList[1].Label.ValueFormatter = func(f float64) string {
		total := float64(moduleChangeFuncCount)
		return charts.FormatValueHumanize(100.0*(total-f)/total, 1, false) + "%"
	}
	if err := topLeft.HorizontalBarChart(topLeftOpt); err != nil {
		return resultBox, fmt.Errorf("error rendering chart: %w", err)
	}
	// subtext is added after due to a desire for custom formatting
	topLeft.Text("(Functions reachable by project)", 210, 37, 0, charts.FontStyle{
		FontSize:  8,
		FontColor: topLeftOpt.Theme.GetTitleTextColor(),
		Font:      charts.GetDefaultFont(),
	})

	topRightOpt := charts.NewHorizontalBarChartOptionWithData([][]float64{
		{float64(moduleChangesReachedInTesting)},                                // validated
		{float64(reachableModuleFunctionCount - moduleChangesReachedInTesting)}, // could be validated, but weren't
	})
	topRightOpt.StackSeries = charts.Ptr(true)
	topRightOpt.Theme = barGaugeThemeGreenYellowRed
	topRightOpt.Title.Text = "Changed Module Function Coverage"
	topRightOpt.XAxis.Unit = axisUnitForMax(reachableModuleFunctionCount)
	topRightOpt.YAxis.Show = charts.Ptr(false)
	topRightOpt.SeriesList[1].Label.Show = charts.Ptr(true)
	topRightOpt.SeriesList[1].Label.FontStyle.FontColor = firstValueSeriesRankColor(topRightOpt.Theme, topRightOpt.SeriesList)
	topRightOpt.SeriesList[1].Label.ValueFormatter = func(f float64) string {
		total := float64(reachableModuleFunctionCount)
		return charts.FormatValueHumanize(100.0*(total-f)/total, 1, false) + "%"
	}
	if err := topRight.HorizontalBarChart(topRightOpt); err != nil {
		return resultBox, fmt.Errorf("error rendering chart: %w", err)
	}

	resultBox.Bottom += max(topLeft.Height(), topRight.Height())

	down1LeftOpt := charts.NewHorizontalBarChartOptionWithData([][]float64{
		{float64(testFieldSameCount)}, {float64(testFieldDiffCount)},
	})
	down1LeftOpt.StackSeries = charts.Ptr(true)
	down1LeftOpt.Theme = barGaugeThemeGreenRed
	down1LeftOpt.Title.Text = "Field Stability"
	down1LeftOpt.XAxis.Show = charts.Ptr(false) // absolute number is fairly arbitrary
	down1LeftOpt.YAxis.Show = charts.Ptr(false)
	down1LeftOpt.BarHeight = 22
	down1LeftOpt.SeriesList[1].Label.Show = charts.Ptr(true)
	down1LeftOpt.SeriesList[1].Label.FontStyle.FontColor = firstValueSeriesRankColor(down1LeftOpt.Theme, down1LeftOpt.SeriesList)
	down1LeftOpt.SeriesList[1].Label.ValueFormatter = func(diff float64) string {
		same := float64(testFieldSameCount)
		percent := 100.0 * same / (same + diff)
		if diff > 0 && percent > 99.9 {
			percent = 99.9 // ensure we don't show 100% when there were some field diffs
		}
		return charts.FormatValueHumanize(percent, 1, false) + "%"
	}
	if err := down1Left.HorizontalBarChart(down1LeftOpt); err != nil {
		return resultBox, fmt.Errorf("error rendering chart: %w", err)
	}

	down1RightOpt := charts.NewHorizontalBarChartOptionWithData([][]float64{
		{float64(globalMutations.SquashedCount)}, {float64(globalMutations.MutationCount - globalMutations.SquashedCount)},
	})
	down1RightOpt.StackSeries = charts.Ptr(true)
	down1RightOpt.Theme = barGaugeThemeGreenYellowRed
	down1RightOpt.Title.Text = "Mutations Squashed"
	down1RightOpt.XAxis.Show = charts.Ptr(false) // absolute number is fairly arbitrary
	down1RightOpt.YAxis.Show = charts.Ptr(false)
	down1RightOpt.BarHeight = down1LeftOpt.BarHeight
	down1RightOpt.SeriesList[1].Label.Show = charts.Ptr(true)
	down1RightOpt.SeriesList[1].Label.FontStyle.FontColor = firstValueSeriesRankColor(down1RightOpt.Theme, down1RightOpt.SeriesList)
	down1RightOpt.SeriesList[1].Label.ValueFormatter = func(f float64) string {
		total := float64(globalMutations.MutationCount)
		percent := 100.0 * (total - f) / total
		if f > 0 && percent > 99.9 {
			percent = 99.9 // ensure we don't show 100% when there were some surviving mutations
		}
		return charts.FormatValueHumanize(percent, 1, false) + "%"
	}
	if err := down1Right.HorizontalBarChart(down1RightOpt); err != nil {
		return resultBox, fmt.Errorf("error rendering chart: %w", err)
	}

	// TODO - remove chart and painter if totalPreTime == 0
	var down2Opt charts.HorizontalBarChartOption
	if totalPostTime <= totalPreTime {
		// improvement: post time first (smaller), then additional time that was saved
		down2Opt = charts.NewHorizontalBarChartOptionWithData([][]float64{
			{totalPostTime}, {totalPreTime - totalPostTime},
		})
		down2Opt.Theme = barGaugeThemeGreenYellowRed
		down2Opt.SeriesList[1].Label.FontStyle.FontColor = charts.ColorBlack
	} else {
		// regression: pre time first (smaller), then additional time that was added
		down2Opt = charts.NewHorizontalBarChartOptionWithData([][]float64{
			{totalPreTime}, {totalPostTime - totalPreTime},
		})
		down2Opt.Theme = barGaugeThemeGreenRed
		down2Opt.SeriesList[1].Label.FontStyle.FontColor = firstValueSeriesRankColor(down2Opt.Theme, down2Opt.SeriesList)
	}
	down2Opt.StackSeries = charts.Ptr(true)
	down2Opt.Title.Text = "Performance Change (" + timeUnit + ")"
	down2Opt.XAxis.Unit = axisUnitForMax(int(max(totalPreTime, totalPostTime)))
	down2Opt.YAxis.Show = charts.Ptr(false)
	down2Opt.BarHeight = down1LeftOpt.BarHeight
	down2Opt.SeriesList[1].Label.Show = charts.Ptr(true)
	down2Opt.SeriesList[1].Label.ValueFormatter = func(f float64) string {
		if totalPreTime == 0 {
			return "No time recorded"
		}
		ratio := totalPostTime / totalPreTime
		if totalPostTime <= totalPreTime { // improvement, ratio <= 1
			return charts.FormatValueHumanize(100.0-(ratio*100.0), 1, false) + "% faster"
		} else {
			return charts.FormatValueHumanize((1-ratio)*100.0, 1, false) + "% slower"
		}
	}
	if err := down2.HorizontalBarChart(down2Opt); err != nil {
		return resultBox, fmt.Errorf("error rendering chart: %w", err)
	}

	resultBox.Bottom += max(down1Left.Height(), down1Right.Height()) + down2.Height()

	var riskyTests [][]string
	for _, tr := range testResults {
		testRegression := !tr.OriginalResult.TestFailure && tr.PostUpdateResult.TestFailure

		if testRegression || tr.DiffFieldCount > 0 {
			regressionStr := testPassStr
			if testRegression {
				regressionStr = testFailStr
			} else if tr.OriginalResult.TestFailure {
				regressionStr = "Baseline FAIL"
			}

			var lines int
			var fieldChangeBuilder strings.Builder
			for callerIdent, fieldMap := range tr.CallerFieldChanges {
				if lines > 1 {
					fieldChangeBuilder.WriteString("\n(")
					fieldChangeBuilder.WriteString(strconv.Itoa(len(tr.CallerFieldChanges) - lines))
					fieldChangeBuilder.WriteString(" more field differences)")
					break
				} else if lines > 0 {
					fieldChangeBuilder.WriteRune('\n')
				}
				lines++

				fieldChangeStr := callerIdent + "[" + strings.Join(slices.Collect(maps.Keys(fieldMap)), "|") + "]"
				fieldChangeStr += fieldChangeStr
				if len(fieldChangeStr) > 66 {
					fieldChangeStr = fieldChangeStr[:64] + ".."
				}
				fieldChangeBuilder.WriteString(fieldChangeStr)
			}

			riskyTests = append(riskyTests, []string{
				tr.OriginalResult.TestFunction.FunctionName,
				regressionStr,
				strconv.Itoa(tr.DiffFieldCount),
				fieldChangeBuilder.String(),
			})
		}
	}
	if len(riskyTests) == 0 {
		text := "No Risky Tests Identified"
		textBox := bottom.MeasureText(text, 0, titleFont)
		bottom.Text(text, (bottom.Width()-textBox.Width())/2, bottom.Height()/2, 0, titleFont)
		resultBox.Bottom += textBox.Height() * 2
	} else {
		slices.SortFunc(riskyTests, func(a, b []string) int {
			aGen := strings.HasPrefix(a[0], GeneratedTestFunctionPrefix)
			bGen := strings.HasPrefix(b[0], GeneratedTestFunctionPrefix)
			if aGen != bGen { // sort generated functions last
				if aGen {
					return 1
				} else {
					return -1
				}
			}
			var aRegress, bRegress int
			if a[1] == testFailStr {
				aRegress = 1
			}
			if b[1] == testFailStr {
				bRegress = 1
			}
			if aRegress != bRegress {
				return bRegress - aRegress
			}

			aCount, _ := strconv.Atoi(a[2])
			bCount, _ := strconv.Atoi(b[2])
			if aCount != bCount { // sort by field change count first, highest first
				return bCount - aCount
			}

			aCount, _ = strconv.Atoi(a[3])
			bCount, _ = strconv.Atoi(b[3])
			if aCount != bCount { // highest mutations second
				return bCount - aCount
			}

			return 0
		})
		if len(riskyTests) > bottomTableMaxRecords {
			riskyTests = riskyTests[:bottomTableMaxRecords]
		}
		tableTitle := "Risky Tests"
		tableTitleFont := charts.FontStyle{
			FontSize:  12,
			FontColor: barGaugeThemeGreenRed.GetTitleTextColor(),
			Font:      charts.GetDefaultFont(),
		}
		tableTitleBox := bottom.MeasureText(tableTitle, 0, tableTitleFont)
		bottom.Text(tableTitle, 10, tableTitleBox.Height(), 0, tableTitleFont)
		rowColors := []charts.Color{
			{R: 240, G: 240, B: 240, A: 255},
			charts.ColorTransparent,
		}
		if len(riskyTests)%2 == 0 {
			// reverse row colors so table end is opposite of transparent
			rowColors[0], rowColors[1] = rowColors[1], rowColors[0]
		}
		defaultCellFontStyle := charts.FontStyle{
			FontSize:  12,
			FontColor: charts.Color{R: 50, G: 50, B: 50, A: 255},
			Font:      charts.GetDefaultFont(),
		}
		bottomOpt := charts.TableChartOption{
			Header:                []string{"Test Name", "Regression", "Fields Changed", "Field Changes"},
			Data:                  riskyTests,
			HeaderBackgroundColor: charts.Color{R: 210, G: 210, B: 210, A: 255},
			RowBackgroundColors:   rowColors,
			Padding:               charts.NewBoxEqual(10),
			Spans:                 []int{24, 8, 8, 28},
			TextAligns:            []string{charts.AlignLeft, charts.AlignLeft, charts.AlignCenter, charts.AlignLeft},
			CellModifier: func(cell charts.TableCell) charts.TableCell {
				// TODO - FUTURE - simpler api for charts?
				if cell.Row == 0 {
					return cell
				}
				cell.FontStyle = defaultCellFontStyle // reset on each call to prevent prior changes persisting

				switch cell.Column {
				case 1: // Regression field
					if cell.Text == testFailStr {
						cell.FontStyle.FontColor = redTextColor
					} else if strings.Contains(cell.Text, testFailStr) {
						cell.FontStyle.FontColor = orangeTextColor
					} else {
						cell.FontStyle.FontColor = greenTextColor
					}
				case 2: // field change count
					if cell.Text != "0" {
						if len(cell.Text) < 2 { // less than 10
							cell.FontStyle.FontColor = orangeTextColor
						} else {
							cell.FontStyle.FontColor = redTextColor
						}
					} else {
						cell.FontStyle.FontColor = greenTextColor
					}
				case 3: // field changes
					cell.FontStyle.FontSize = 8
				}
				return cell
			},
		}
		tablePainter := bottom.Child(charts.PainterPaddingOption(charts.NewBox(10, tableTitleBox.Height()+8, 0, 0)))
		if err := tablePainter.TableChart(bottomOpt); err != nil {
			return resultBox, fmt.Errorf("error rendering table: %w", err)
		}
		// re-render just so we can calculate the height of the table, currently charts does not return the table sizes
		// TODO - FUTURE - improve charts API to avoid this
		bottomOpt.Width = bottom.Width()
		if p, _ := charts.TableOptionRenderDirect(bottomOpt); p != nil {
			resultBox.Bottom += tableTitleBox.Height() + p.Height()
		} else {
			resultBox.Bottom += bottom.Height()
		}
	}

	// render the final chart extras
	if title != "" {
		p.Text(title, (p.Width()/2)-(titleBox.Width()/2), titleBox.Height(), 0, titleFont)
	}
	return resultBox, nil
}

func firstValueSeriesRankColor(theme charts.ColorPalette, sl charts.HorizontalBarSeriesList) charts.Color {
	sum := sl.SumSeriesValues()
	if sl[0].Values[0] < sum[0]/2 {
		return redTextColor
	} else if sl[0].Values[0] < sum[0]*.8 {
		return orangeTextColor
	} else {
		return theme.GetLabelTextColor()
	}
}

func axisUnitForMax(val int) float64 {
	if val >= 8000 {
		return 2000
	} else if val > 2000 {
		return 1000
	} else if val >= 800 {
		return 200
	} else if val > 200 {
		return 100
	} else if val >= 80 {
		return 20
	} else if val > 20 {
		return 10
	} else if val >= 10 {
		return 2
	} else {
		return 1
	}
}
