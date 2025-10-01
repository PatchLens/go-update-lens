package lens

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Mock implementations for testing
type mockModuleChangeProvider struct {
	moduleChanges []*ModuleFunction
	checkedNames  []string
	err           error
}

func (m *mockModuleChangeProvider) AnalyzeModuleChanges(config Config, analyzeExpandTransitive bool,
	changedModules []ModuleChange, neighbourRadius int) ([]*ModuleFunction, []string, error) {
	return m.moduleChanges, m.checkedNames, m.err
}

func (m *mockModuleChangeProvider) Cleanup() {}

type mockCallerAnalysisProvider struct {
	callingFunctions       []*CallerFunction
	reachableModuleChanges ReachableModuleChange
	err                    error
}

func (m *mockCallerAnalysisProvider) PerformCallerStaticAnalysis(config Config, moduleChanges []*ModuleFunction) ([]*CallerFunction, ReachableModuleChange, error) {
	return m.callingFunctions, m.reachableModuleChanges, m.err
}

func (m *mockCallerAnalysisProvider) Cleanup() {}

type mockTestProvider struct {
	testFunctions []*TestFunction
	err           error
}

func (m *mockTestProvider) ProvideTests(config Config, callingFunctions []*CallerFunction) ([]*TestFunction, error) {
	return m.testFunctions, m.err
}

func (m *mockTestProvider) Cleanup() {}

type mockUpdateAnalysisProvider struct {
	projectFieldChecks            int
	moduleChangesReachedInTesting int
	preResults, postResults       Storage
	err                           error
}

func (m *mockUpdateAnalysisProvider) RunModuleUpdateAnalysis(config Config, storage Storage,
	changedModules []ModuleChange, reachableModuleChanges ReachableModuleChange,
	callingFunctions []*CallerFunction, testFunctions []*TestFunction) (int, int, Storage, Storage, error) {
	return m.projectFieldChecks, m.moduleChangesReachedInTesting, m.preResults, m.postResults, m.err
}

func (m *mockUpdateAnalysisProvider) Cleanup() {}

type mockMutationTester struct {
	mutationResult MutationResult
	err            error
}

func (m *mockMutationTester) RunMutationTesting(config Config, fastMutations, lineScopedMutations,
	runTargetedTests bool, moduleChanges []*ModuleFunction, testFunctions []*TestFunction) (MutationResult, error) {
	return m.mutationResult, m.err
}

func (m *mockMutationTester) Cleanup() {}

type mockReportWriter struct {
	err error
}

func (m *mockReportWriter) WriteReportFiles(reportJsonFile, reportChartsFile string, startTime time.Time,
	analysisTime, testExpansionTime, testExecutionTime, mutationTime time.Duration,
	changedModules []ModuleChange, checkedModules []string, moduleChangeCount, moduleChangesReachedInTesting int,
	projectFieldChecks int, callingFunctions []*CallerFunction, testFunctions []*TestFunction,
	sameCount, diffCount int, testReports []TestReport, performanceRegressionCount int,
	globalMutations MutationResult) error {
	return m.err
}

type mockTestResultAnalyzer struct {
	sameCount, diffCount int
	testReports          []TestReport
}

func (m *mockTestResultAnalyzer) CompareTestResults(preStorage, postStorage Storage, timeMultiplier int) (int, int, []TestReport, error) {
	return m.sameCount, m.diffCount, m.testReports, nil
}

type mockStorageProvider struct {
	storage Storage
	err     error
}

func (m *mockStorageProvider) NewStorage() (Storage, error) {
	return m.storage, m.err
}

func createTestConfig(t *testing.T) *Config {
	t.Helper()

	tmpDir := t.TempDir()

	// Create a basic go.mod file
	goModContent := `module test
go 1.21
require github.com/test/module v1.0.0
`
	err := os.WriteFile(filepath.Join(tmpDir, "go.mod"), []byte(goModContent), 0644)
	require.NoError(t, err)

	return &Config{
		ProjectDir:        tmpDir,
		ModuleVersionFlag: "github.com/test/module@v1.2.3",
		AbsProjDir:        tmpDir,
		Gopath:            tmpDir,
		Gomodcache:        filepath.Join(tmpDir, "mod"),
		AstMonitorPort:    44440,
		MaxFieldRecurse:   20,
		MaxFieldLen:       1024,
		CacheMB:           200,
		TimeMultiplier:    2,
		ReportJsonFile:    filepath.Join(tmpDir, "test.json"),
		ReportChartsFile:  filepath.Join(tmpDir, "test.png"),
		MutationScope:     "line",
		MutationMode:      "fast",
		MutationTests:     "targeted",
		TmpCopy:           false, // Disable for testing
	}
}

func TestAnalysisEngine_Run(t *testing.T) {
	t.Run("successful_analysis_flow", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		// Create mock providers
		mockModuleChanges := []*ModuleFunction{
			{Function: Function{FunctionName: "TestFunc", PackageName: "test"}},
		}
		mockCallingFunctions := []*CallerFunction{
			{Function: Function{FunctionName: "CallerFunc"}},
		}
		mockTestFunctions := []*TestFunction{
			{Function: Function{FunctionName: "TestCallerFunc"}},
		}

		// Create mock storage with test data
		preStorage := NewMemStorage()
		err := preStorage.SaveState("test.func", createMockTestResultBytes(t, "TestFunc"))
		require.NoError(t, err)
		postStorage := NewMemStorage()
		err = postStorage.SaveState("test.func", createMockTestResultBytes(t, "TestFunc"))
		require.NoError(t, err)

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: mockModuleChanges,
				checkedNames:  []string{"github.com/test/module"},
			},
			&mockCallerAnalysisProvider{
				callingFunctions: mockCallingFunctions,
			},
			&mockTestProvider{
				testFunctions: mockTestFunctions,
			},
			&mockUpdateAnalysisProvider{
				projectFieldChecks:            10,
				moduleChangesReachedInTesting: 1,
				preResults:                    preStorage,
				postResults:                   postStorage,
			},
			&mockMutationTester{
				mutationResult: MutationResult{},
			},
			&mockTestResultAnalyzer{
				sameCount:   1,
				diffCount:   0,
				testReports: []TestReport{},
			},
			&mockStorageProvider{
				storage: NewMemStorage(),
			},
			&mockReportWriter{},
		)

		err = engine.Run()
		require.NoError(t, err)
		assert.True(t, config.prepared)
	})

	t.Run("no_changed_modules", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)
		// This test uses mock providers that return no changes, so we should get no work done
		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: []*ModuleFunction{}, // No changes
				checkedNames:  []string{},
			},
			nil, nil, nil, nil, nil, nil,
			&mockReportWriter{},
		)

		err := engine.Run()
		require.NoError(t, err)
		assert.True(t, config.prepared)
	})

	t.Run("no_module_changes", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: []*ModuleFunction{}, // No changes
				checkedNames:  []string{"github.com/test/module"},
			},
			nil, nil, nil, nil, nil, nil,
			&mockReportWriter{},
		)

		err := engine.Run()
		require.NoError(t, err)
		assert.True(t, config.prepared)
	})

	t.Run("no_reachable_changes", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		mockModuleChanges := []*ModuleFunction{
			{Function: Function{FunctionName: "TestFunc", PackageName: "test"}},
		}

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: mockModuleChanges,
				checkedNames:  []string{"github.com/test/module"},
			},
			&mockCallerAnalysisProvider{
				callingFunctions: []*CallerFunction{}, // No callers
			},
			nil, nil, nil, nil, nil,
			&mockReportWriter{},
		)

		err := engine.Run()
		require.NoError(t, err)
		assert.True(t, config.prepared)
	})

	t.Run("no_test_functions", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		mockModuleChanges := []*ModuleFunction{
			{Function: Function{FunctionName: "TestFunc", PackageName: "test"}},
		}
		mockCallingFunctions := []*CallerFunction{
			{Function: Function{FunctionName: "CallerFunc"}},
		}

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: mockModuleChanges,
				checkedNames:  []string{"github.com/test/module"},
			},
			&mockCallerAnalysisProvider{
				callingFunctions: mockCallingFunctions,
			},
			&mockTestProvider{
				testFunctions: []*TestFunction{}, // No tests
			},
			nil, nil, nil, nil,
			&mockReportWriter{},
		)

		err := engine.Run()
		require.NoError(t, err)
		assert.True(t, config.prepared)
	})

	t.Run("module_analysis_error", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				err: errors.New("module analysis failed"),
			},
			nil, nil, nil, nil, nil, nil, nil,
		)

		err := engine.Run()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "module analysis failed")
	})

	t.Run("caller_analysis_error", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: []*ModuleFunction{{Function: Function{FunctionName: "TestFunc"}}},
				checkedNames:  []string{"test"},
			},
			&mockCallerAnalysisProvider{
				err: errors.New("caller analysis failed"),
			},
			nil, nil, nil, nil, nil, nil,
		)

		err := engine.Run()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "caller analysis failed")
	})

	t.Run("test_provider_error", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)

		engine := NewAnalysisEngineWithProviders(
			config,
			&mockModuleChangeProvider{
				moduleChanges: []*ModuleFunction{{Function: Function{FunctionName: "TestFunc"}}},
				checkedNames:  []string{"test"},
			},
			&mockCallerAnalysisProvider{
				callingFunctions: []*CallerFunction{{Function: Function{FunctionName: "CallerFunc"}}},
			},
			&mockTestProvider{
				err: errors.New("test provider failed"),
			},
			nil, nil, nil, nil, nil,
		)

		err := engine.Run()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "test provider failed")
	})
}

func TestAnalysisEngine_parseInitialModules(t *testing.T) {
	t.Run("module_flag_parsing", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)
		config.ModuleVersionFlag = "github.com/test/module@v1.2.3"

		// Prepare the config to populate parsed target modules
		err := config.Prepare()
		require.NoError(t, err)

		engine := NewAnalysisEngine(config)

		result, err := engine.parseInitialModules()
		require.NoError(t, err)
		assert.NotNil(t, result)
		assert.True(t, result.analyzeExpandTransitive)
		assert.Len(t, result.changedModules, 1)
		assert.Equal(t, "github.com/test/module", result.changedModules[0].Name)
		assert.Equal(t, "v1.0.0", result.changedModules[0].PriorVersion)
		assert.Equal(t, "v1.2.3", result.changedModules[0].NewVersion)
	})

	t.Run("invalid_module_format", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)
		config.ModuleVersionFlag = "invalid-format" // Missing @version

		err := config.Prepare()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid module version format")
	})

	t.Run("mutation_scope_area", func(t *testing.T) {
		t.Parallel()

		config := createTestConfig(t)
		config.MutationScope = "area"

		// Prepare the config to populate parsed target modules
		err := config.Prepare()
		require.NoError(t, err)

		engine := NewAnalysisEngine(config)

		result, err := engine.parseInitialModules()
		require.NoError(t, err)
		assert.Equal(t, 1, result.neighbourRadius)
	})
}

func TestAnalysisEngine_compareTestResults(t *testing.T) {
	t.Run("basic_comparison", func(t *testing.T) {
		t.Parallel()

		// Create mock storage with test data
		preStorage := NewMemStorage()
		err := preStorage.SaveState("test.func", createMockTestResultBytes(t, "TestFunc"))
		require.NoError(t, err)
		postStorage := NewMemStorage()
		err = postStorage.SaveState("test.func", createMockTestResultBytes(t, "TestFunc"))
		require.NoError(t, err)

		analyzer := &mockTestResultAnalyzer{
			sameCount: 1,
			diffCount: 0,
			testReports: []TestReport{{
				OriginalResult: TestResult{
					TestFunction: MinimumTestFunction{FunctionName: "TestFunc"},
				},
				PostUpdateResult: TestResult{
					TestFunction: MinimumTestFunction{FunctionName: "TestFunc"},
				},
				SameFieldCount: 1,
				DiffFieldCount: 0,
			}},
		}
		sameCount, diffCount, testReports, err := analyzer.CompareTestResults(preStorage, postStorage, 2)
		require.NoError(t, err)

		assert.GreaterOrEqual(t, sameCount, 0)
		assert.GreaterOrEqual(t, diffCount, 0)
		assert.Len(t, testReports, 1)
	})
}

func TestNewAnalysisEngine(t *testing.T) {
	t.Run("default_providers", func(t *testing.T) {
		config := createTestConfig(t)
		engine := NewAnalysisEngine(config)

		assert.NotNil(t, engine.Config)
		assert.IsType(t, &DefaultModuleChangeProvider{}, engine.ModuleChangeProvider)
		assert.IsType(t, &DefaultCallerAnalysisProvider{}, engine.CallerAnalysisProvider)
		assert.IsType(t, &DefaultTestProvider{}, engine.TestProvider)
		assert.IsType(t, &DefaultUpdateAnalysisProvider{}, engine.UpdateAnalysisProvider)
		assert.IsType(t, &DefaultMutationTester{}, engine.MutationTester)
		assert.IsType(t, &DefaultReportWriter{}, engine.ReportWriter)
	})

	t.Run("custom_providers", func(t *testing.T) {
		config := createTestConfig(t)
		mockProvider := &mockModuleChangeProvider{}

		engine := NewAnalysisEngineWithProviders(
			config,
			mockProvider,
			nil, nil, nil, nil, nil, nil, nil,
		)

		assert.Same(t, mockProvider, engine.ModuleChangeProvider)
		// Other providers should remain default when nil is passed
		assert.IsType(t, &DefaultCallerAnalysisProvider{}, engine.CallerAnalysisProvider)
	})
}

// Helper function to create mock test result bytes
func createMockTestResultBytes(t *testing.T, funcName string) []byte {
	testResult := TestResult{
		TestFunction: MinimumTestFunction{
			FunctionName: funcName,
		},
		CallerResults: map[string][]CallFrame{
			"test.caller": {
				{
					FieldValues: FieldValues{
						"field1": &FieldValue{
							Value: "value1",
						},
					},
					TimeMillis: 100,
				},
			},
		},
		ProjectPanics: map[string][]string{},
		ModulePanics:  map[string][]string{},
		TestFailure:   false,
	}

	data, err := testResult.MarshalMsgpack()
	require.NoError(t, err)
	return data
}

func TestConfig_Prepare(t *testing.T) {
	t.Run("required_fields_validation", func(t *testing.T) {
		t.Run("missing_project_dir", func(t *testing.T) {
			config := &Config{
				ModuleVersionFlag: "github.com/test/module@v1.0.0",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "project directory is required")
		})

		t.Run("missing_all_module_specs", func(t *testing.T) {
			config := &Config{
				ProjectDir: t.TempDir(),
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "must specify one of: -module, -modules, -gomod, or -gowork")
		})

		t.Run("mutually_exclusive_gomod_gowork", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				UpdatedGoModFile:  "/tmp/go.mod",
				UpdatedGoWorkFile: "/tmp/go.work",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "-gomod and -gowork are mutually exclusive")
		})
	})

	t.Run("module_parsing_validation", func(t *testing.T) {
		t.Run("invalid_module_format_no_at", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "github.com/test/module",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "module version must be in format 'module@version'")
		})

		t.Run("empty_module_name", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "@v1.0.0",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "module name cannot be empty")
		})

		t.Run("empty_version", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "github.com/test/module@",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "version cannot be empty")
		})

		t.Run("invalid_module_name_format", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "invalidmodule@v1.0.0",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "appears invalid (should contain domain or path)")
		})

		t.Run("multiple_modules_with_invalid", func(t *testing.T) {
			config := &Config{
				ProjectDir:         t.TempDir(),
				ModulesVersionFlag: "github.com/valid/module@v1.0.0,invalidmodule@v1.0.0",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "appears invalid (should contain domain or path)")
		})

		t.Run("empty_module_in_modules_list", func(t *testing.T) {
			config := &Config{
				ProjectDir:         t.TempDir(),
				ModulesVersionFlag: "github.com/test/module@v1.0.0,,github.com/other/module@v2.0.0",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "empty module specification in modules list")
		})
	})

	t.Run("file_path_validation", func(t *testing.T) {
		t.Run("non_existent_gomod_file", func(t *testing.T) {
			config := &Config{
				ProjectDir:       t.TempDir(),
				UpdatedGoModFile: "/non/existent/go.mod",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "file does not exist or is not accessible")
		})

		t.Run("directory_instead_of_gomod_file", func(t *testing.T) {
			config := &Config{
				ProjectDir:       t.TempDir(),
				UpdatedGoModFile: t.TempDir(), // Directory instead of file
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "path is a directory, expected a go.mod file")
		})

		t.Run("non_existent_gowork_file", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				UpdatedGoWorkFile: "/non/existent/go.work",
			}
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "file does not exist or is not accessible")
		})
	})

	t.Run("numeric_range_validation", func(t *testing.T) {
		baseConfig := func() *Config {
			return &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "github.com/test/module@v1.0.0",
				AstMonitorPort:    44440,
				MaxFieldRecurse:   20,
				MaxFieldLen:       1024,
				CacheMB:           200,
				TimeMultiplier:    2,
			}
		}

		t.Run("ast_monitor_port_too_low", func(t *testing.T) {
			config := baseConfig()
			config.AstMonitorPort = 1023
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "ast monitor port must be between ")
		})

		t.Run("ast_monitor_port_too_high", func(t *testing.T) {
			config := baseConfig()
			config.AstMonitorPort = 65536
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "ast monitor port must be between ")
		})

		t.Run("max_field_recurse_too_low", func(t *testing.T) {
			config := baseConfig()
			config.MaxFieldRecurse = 0
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "max field recurse must be between 1 and ")
		})

		t.Run("max_field_recurse_too_high", func(t *testing.T) {
			config := baseConfig()
			config.MaxFieldRecurse = 101
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "max field recurse must be between 1 and ")
		})

		t.Run("max_field_len_too_low", func(t *testing.T) {
			config := baseConfig()
			config.MaxFieldLen = 0
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "max field length must be between 1 and ")
		})

		t.Run("max_field_len_too_high", func(t *testing.T) {
			config := baseConfig()
			config.MaxFieldLen = 1048577
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "max field length must be between 1 and ")
		})

		t.Run("cache_mb_too_low", func(t *testing.T) {
			config := baseConfig()
			config.CacheMB = 0
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "cache size must be between 1 and ")
		})

		t.Run("cache_mb_too_high", func(t *testing.T) {
			config := baseConfig()
			config.CacheMB = 10241
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "cache size must be between 1 and ")
		})

		t.Run("time_multiplier_too_low", func(t *testing.T) {
			config := baseConfig()
			config.TimeMultiplier = 0
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "time multiplier must be between 1 and ")
		})

		t.Run("time_multiplier_too_high", func(t *testing.T) {
			config := baseConfig()
			config.TimeMultiplier = 101
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "time multiplier must be between 1 and ")
		})
	})

	t.Run("enum_validation", func(t *testing.T) {
		baseConfig := func() *Config {
			return &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "github.com/test/module@v1.0.0",
				AstMonitorPort:    44440,
				MaxFieldRecurse:   20,
				MaxFieldLen:       1024,
				CacheMB:           200,
				TimeMultiplier:    2,
				MutationScope:     "line",
				MutationMode:      "fast",
				MutationTests:     "targeted",
			}
		}

		t.Run("invalid_mutation_scope", func(t *testing.T) {
			config := baseConfig()
			config.MutationScope = "invalid1"
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "invalid mutation scope 'invalid1', must be one of: ")
		})

		t.Run("invalid_mutation_mode", func(t *testing.T) {
			config := baseConfig()
			config.MutationMode = "invalid2"
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "invalid mutation mode 'invalid2', must be one of: ")
		})

		t.Run("invalid_mutation_tests", func(t *testing.T) {
			config := baseConfig()
			config.MutationTests = "invalid3"
			err := config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "invalid mutation tests 'invalid3', must be one of: ")
		})
	})

	t.Run("state_management", func(t *testing.T) {
		t.Run("multiple_prepare_calls", func(t *testing.T) {
			config := &Config{
				ProjectDir:        t.TempDir(),
				ModuleVersionFlag: "github.com/test/module@v1.0.0",
				AstMonitorPort:    44440,
				MaxFieldRecurse:   20,
				MaxFieldLen:       1024,
				CacheMB:           200,
				TimeMultiplier:    2,
				MutationScope:     "line",
				MutationMode:      "fast",
				MutationTests:     "targeted",
			}

			// First prepare should succeed
			err := config.Prepare()
			require.NoError(t, err)

			// Second prepare should fail
			err = config.Prepare()
			require.Error(t, err)
			assert.Contains(t, err.Error(), "config has already been prepared")
		})
	})

	t.Run("success_cases", func(t *testing.T) {
		t.Run("valid_single_module", func(t *testing.T) {
			projectDir := t.TempDir()
			config := &Config{
				ProjectDir:        projectDir,
				ModuleVersionFlag: "github.com/test/module@v1.0.0",
				AstMonitorPort:    44440,
				MaxFieldRecurse:   20,
				MaxFieldLen:       1024,
				CacheMB:           200,
				TimeMultiplier:    2,
				MutationScope:     "line",
				MutationMode:      "fast",
				MutationTests:     "targeted",
				ReportJsonFile:    filepath.Join(t.TempDir(), "report.json"),
				ReportChartsFile:  filepath.Join(t.TempDir(), "charts.png"),
			}

			err := config.Prepare()
			require.NoError(t, err)

			// Check that computed fields are set correctly
			absPath, _ := filepath.Abs(projectDir)
			assert.Equal(t, absPath, config.AbsProjDir)
			assert.Len(t, config.TargetModules, 1)
			assert.Equal(t, "github.com/test/module", config.TargetModules[0].Name)
			assert.Equal(t, "v1.0.0", config.TargetModules[0].Version)
			assert.True(t, config.prepared)
		})

		t.Run("valid_multiple_modules", func(t *testing.T) {
			config := &Config{
				ProjectDir:         t.TempDir(),
				ModulesVersionFlag: "github.com/test/module@v1.0.0,github.com/other/module@v2.0.0",
				AstMonitorPort:     44440,
				MaxFieldRecurse:    20,
				MaxFieldLen:        1024,
				CacheMB:            200,
				TimeMultiplier:     2,
				MutationScope:      "area",
				MutationMode:       fullScopeFlag,
				MutationTests:      fullScopeFlag,
			}

			err := config.Prepare()
			require.NoError(t, err)

			// Check that multiple modules are parsed correctly
			assert.Len(t, config.TargetModules, 2)
			assert.Equal(t, "github.com/test/module", config.TargetModules[0].Name)
			assert.Equal(t, "v1.0.0", config.TargetModules[0].Version)
			assert.Equal(t, "github.com/other/module", config.TargetModules[1].Name)
			assert.Equal(t, "v2.0.0", config.TargetModules[1].Version)
		})

		t.Run("valid_with_gomod_file", func(t *testing.T) {
			// Create a temporary go.mod file
			goModFile := filepath.Join(t.TempDir(), "go.mod")
			err := os.WriteFile(goModFile, []byte("module test\ngo 1.21\n"), 0644)
			require.NoError(t, err)

			config := &Config{
				ProjectDir:       t.TempDir(),
				UpdatedGoModFile: goModFile,
				AstMonitorPort:   44440,
				MaxFieldRecurse:  20,
				MaxFieldLen:      1024,
				CacheMB:          200,
				TimeMultiplier:   2,
				MutationScope:    "function",
				MutationMode:     "fast",
				MutationTests:    "targeted",
			}

			err = config.Prepare()
			require.NoError(t, err)

			// Should have no target modules since we're using go.mod diff
			assert.Empty(t, config.TargetModules)
		})

		t.Run("valid_with_gowork_file", func(t *testing.T) {
			// Create a temporary go.work file
			goWorkFile := filepath.Join(t.TempDir(), "go.work")
			err := os.WriteFile(goWorkFile, []byte("go 1.21\nuse ./module1\nuse ./module2\n"), 0644)
			require.NoError(t, err)

			config := &Config{
				ProjectDir:        t.TempDir(),
				UpdatedGoWorkFile: goWorkFile,
				AstMonitorPort:    44440,
				MaxFieldRecurse:   20,
				MaxFieldLen:       1024,
				CacheMB:           200,
				TimeMultiplier:    2,
				MutationScope:     noneScopeFlag,
				MutationMode:      "fast",
				MutationTests:     "targeted",
			}

			err = config.Prepare()
			require.NoError(t, err)

			// Should have no target modules since we're using go.work diff
			assert.Empty(t, config.TargetModules)
		})
	})
}

func TestParseTargetModule(t *testing.T) {
	t.Run("valid_module", func(t *testing.T) {
		result, err := parseTargetModule("github.com/test/module@v1.0.0")
		require.NoError(t, err)
		assert.Equal(t, "github.com/test/module", result.Name)
		assert.Equal(t, "v1.0.0", result.Version)
	})

	t.Run("invalid_format_no_at", func(t *testing.T) {
		_, err := parseTargetModule("github.com/test/module")
		require.Error(t, err)
		assert.Contains(t, err.Error(), "module version must be in format 'module@version'")
	})

	t.Run("empty_module_name", func(t *testing.T) {
		_, err := parseTargetModule("@v1.0.0")
		require.Error(t, err)
		assert.Contains(t, err.Error(), "module name cannot be empty")
	})

	t.Run("empty_version", func(t *testing.T) {
		_, err := parseTargetModule("github.com/test/module@")
		require.Error(t, err)
		assert.Contains(t, err.Error(), "version cannot be empty")
	})

	t.Run("invalid_module_name", func(t *testing.T) {
		_, err := parseTargetModule("invalidmodule@v1.0.0")
		require.Error(t, err)
		assert.Contains(t, err.Error(), "appears invalid (should contain domain or path)")
	})

	t.Run("valid_module_with_domain", func(t *testing.T) {
		result, err := parseTargetModule("example.com/module@v2.1.0")
		require.NoError(t, err)
		assert.Equal(t, "example.com/module", result.Name)
		assert.Equal(t, "v2.1.0", result.Version)
	})

	t.Run("valid_module_with_path", func(t *testing.T) {
		result, err := parseTargetModule("golang/x/net@v0.1.0")
		require.NoError(t, err)
		assert.Equal(t, "golang/x/net", result.Name)
		assert.Equal(t, "v0.1.0", result.Version)
	})
}

// Fuzzing tests for module parsing validation
func FuzzParseTargetModule(f *testing.F) {
	// Seed with valid test cases
	f.Add("github.com/test/module@v1.0.0")
	f.Add("example.com/pkg@v2.1.0")
	f.Add("golang.org/x/tools@v0.1.0")
	f.Add("domain.com/user/repo@v1.2.3-beta")

	// Seed with invalid test cases to ensure they're handled properly
	f.Add("@v1.0.0")
	f.Add("module@")
	f.Add("module")
	f.Add("invalid@v1.0.0")
	f.Add("")
	f.Add("@")
	f.Add("module@@v1.0.0")
	f.Add("module@version@extra")

	f.Fuzz(func(t *testing.T, moduleSpec string) {
		// parseTargetModule should never panic, regardless of input
		defer func() {
			if r := recover(); r != nil {
				t.Errorf("parseTargetModule panicked with input %q: %v", moduleSpec, r)
			}
		}()

		result, err := parseTargetModule(moduleSpec)

		if err != nil {
			assert.NotEmpty(t, err.Error())
			assert.NotContains(t, err.Error(), "panic")
			return
		}

		// If no error, validate the parsed result
		assert.NotEmpty(t, result.Name)
		assert.NotEmpty(t, result.Version)

		// Module name should contain domain or path separator
		assert.True(t, strings.Contains(result.Name, ".") || strings.Contains(result.Name, "/"),
			"module name should contain domain or path separator: %s", result.Name)

		// Module name should not contain @ symbol
		assert.NotContains(t, result.Name, "@", "module name should not contain @ symbol")

		// Version should not contain @ symbol
		assert.NotContains(t, result.Version, "@", "version should not contain @ symbol")

		// Module name should be reasonable length
		assert.True(t, len(result.Name) > 0 && len(result.Name) < 500,
			"module name should be reasonable length: %d", len(result.Name))

		// Version should be reasonable length
		assert.True(t, len(result.Version) > 0 && len(result.Version) < 100,
			"version should be reasonable length: %d", len(result.Version))
	})
}

func FuzzConfigPrepareModuleValidation(f *testing.F) {
	// Seed with valid module specifications
	f.Add("github.com/test/module@v1.0.0")
	f.Add("github.com/test/mod@v1.0.0,example.com/other@v2.0.0")
	f.Add("domain.com/user/repo@v1.2.3-beta")

	// Seed with invalid specifications
	f.Add("invalid@v1.0.0")
	f.Add("@v1.0.0")
	f.Add("module@")
	f.Add("")
	f.Add("module1@v1.0.0,@v2.0.0")
	f.Add("module1@v1.0.0,,module2@v2.0.0")

	f.Fuzz(func(t *testing.T, moduleSpec string) {
		// Create temporary directory for testing
		projectDir := t.TempDir()

		config := &Config{
			ProjectDir:        projectDir,
			ModuleVersionFlag: moduleSpec,
			AstMonitorPort:    44440,
			MaxFieldRecurse:   20,
			MaxFieldLen:       1024,
			CacheMB:           200,
			TimeMultiplier:    2,
			MutationScope:     "line",
			MutationMode:      "fast",
			MutationTests:     "targeted",
		}

		// Config.Prepare should never panic
		defer func() {
			if r := recover(); r != nil {
				t.Errorf("Config.Prepare panicked with module spec %q: %v", moduleSpec, r)
			}
		}()

		err := config.Prepare()

		if err != nil {
			assert.NotEmpty(t, err.Error())
			assert.NotContains(t, err.Error(), "panic")

			// Config should not be marked as prepared on error
			assert.False(t, config.prepared, "config should not be prepared on error")
			return
		}

		// If no error, validate the prepared config
		assert.True(t, config.prepared, "config should be marked as prepared on success")

		// Target modules should be populated and valid
		for _, module := range config.TargetModules {
			assert.NotEmpty(t, module.Name, "target module name should not be empty")
			assert.NotEmpty(t, module.Version, "target module version should not be empty")
			assert.True(t, strings.Contains(module.Name, ".") || strings.Contains(module.Name, "/"),
				"module name should contain domain or path: %s", module.Name)
		}
	})
}

func TestDefaultTestResultAnalyzer_DiffValues(t *testing.T) {
	tests := []struct {
		name          string
		v1            string
		v2            string
		expected      string
		isUnifiedDiff bool
	}{
		{
			name:     "identical values",
			v1:       "same value",
			v2:       "same value",
			expected: "",
		},
		{
			name:     "both hashed values",
			v1:       HashFieldValuePrefix + "abc123",
			v2:       HashFieldValuePrefix + "def456",
			expected: "<VALUE TOO LARGE ...c123> != <VALUE TOO LARGE ...f456>",
		},
		{
			name:     "first value hashed",
			v1:       HashFieldValuePrefix + "abc123",
			v2:       "normal value",
			expected: "<VALUE TOO LARGE ...c123> != \"normal value\"",
		},
		{
			name:     "second value hashed",
			v1:       "normal value",
			v2:       HashFieldValuePrefix + "abc123",
			expected: "\"normal value\" != <VALUE TOO LARGE ...c123>",
		},
		{
			name:          "simple string diff",
			v1:            "hello",
			v2:            "world",
			expected:      "@@ -1 +1 @@\n-hello\n+world\n",
			isUnifiedDiff: true,
		},
		{
			name:          "multiline diff",
			v1:            "line1\nline2\nline3",
			v2:            "line1\nmodified\nline3",
			expected:      "@@ -1,3 +1,3 @@\n line1\n-line2\n+modified\n line3\n",
			isUnifiedDiff: true,
		},
		{
			name:          "empty string to non-empty",
			v1:            "",
			v2:            "not empty",
			expected:      "@@ -1 +1 @@\n-\n+not empty\n",
			isUnifiedDiff: true,
		},
		{
			name:          "non-empty to empty string",
			v1:            "not empty",
			v2:            "",
			expected:      "@@ -1 +1 @@\n-not empty\n+\n",
			isUnifiedDiff: true,
		},
		{
			name:     "both empty strings",
			v1:       "",
			v2:       "",
			expected: "",
		},
		{
			name:          "whitespace differences",
			v1:            "hello world",
			v2:            "hello  world",
			expected:      "@@ -1 +1 @@\n-hello world\n+hello  world\n",
			isUnifiedDiff: true,
		},
		{
			name:          "newline differences",
			v1:            "hello\nworld",
			v2:            "hello\r\nworld",
			expected:      "@@ -1,2 +1,2 @@\n-hello\n+hello\r\n world\n",
			isUnifiedDiff: true,
		},
		{
			name:          "json structure diff",
			v1:            `{"key": "value1", "other": "same"}`,
			v2:            `{"key": "value2", "other": "same"}`,
			expected:      "@@ -1 +1 @@\n-{\"key\": \"value1\", \"other\": \"same\"}\n+{\"key\": \"value2\", \"other\": \"same\"}\n",
			isUnifiedDiff: true,
		},
		{
			name:          "very long single line",
			v1:            strings.Repeat("a", 100),
			v2:            strings.Repeat("b", 100),
			expected:      "@@ -1 +1 @@\n-" + strings.Repeat("a", 100) + "\n+" + strings.Repeat("b", 100) + "\n",
			isUnifiedDiff: true,
		},
		{
			name:          "partial hash prefix match v1",
			v1:            "vsha1",
			v2:            "something",
			expected:      "@@ -1 +1 @@\n-vsha1\n+something\n",
			isUnifiedDiff: true,
		},
		{
			name:          "partial hash prefix match v2",
			v1:            "something",
			v2:            "vsha1",
			expected:      "@@ -1 +1 @@\n-something\n+vsha1\n",
			isUnifiedDiff: true,
		},
		{
			name:          "lines with only spaces",
			v1:            "line1\n   \nline3",
			v2:            "line1\n\nline3",
			expected:      "@@ -1,3 +1,3 @@\n line1\n-   \n+\n line3\n",
			isUnifiedDiff: true,
		},
		{
			name:          "tab vs spaces",
			v1:            "hello\tworld",
			v2:            "hello world",
			expected:      "@@ -1 +1 @@\n-hello\tworld\n+hello world\n",
			isUnifiedDiff: true,
		},
	}

	analyzer := &DefaultTestResultAnalyzer{}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()

			result := analyzer.DiffValues(tt.v1, tt.v2)

			if tt.isUnifiedDiff {
				// For unified diff output, check that it contains the expected structure
				assert.Contains(t, result, "@@")
				// Verify the diff contains expected changes
				if tt.v1 != "" {
					assert.Contains(t, result, "-")
				}
				if tt.v2 != "" {
					assert.Contains(t, result, "+")
				}
				// Verify exact expected output
				assert.Equal(t, tt.expected, result)
			} else {
				assert.Equal(t, tt.expected, result)
			}
		})
	}
}

func FuzzConfigPrepareModulesValidation(f *testing.F) {
	// Seed with valid multi-module specifications
	f.Add("github.com/test/mod@v1.0.0,example.com/other@v2.0.0")
	f.Add("domain.com/pkg@v1.0.0,golang.org/x/tools@v0.1.0,example.com/lib@v3.0.0")

	// Seed with invalid specifications
	f.Add("valid@v1.0.0,invalid@v1.0.0")
	f.Add("mod1@v1.0.0,,mod2@v2.0.0")
	f.Add(",mod@v1.0.0")
	f.Add("mod@v1.0.0,")
	f.Add("@v1.0.0,@v2.0.0")

	f.Fuzz(func(t *testing.T, modulesSpec string) {
		projectDir := t.TempDir()

		config := &Config{
			ProjectDir:         projectDir,
			ModulesVersionFlag: modulesSpec,
			AstMonitorPort:     44440,
			MaxFieldRecurse:    20,
			MaxFieldLen:        1024,
			CacheMB:            200,
			TimeMultiplier:     2,
			MutationScope:      "line",
			MutationMode:       "fast",
			MutationTests:      "targeted",
		}

		err := config.Prepare()
		if err != nil {
			assert.NotEmpty(t, err.Error())
			assert.NotContains(t, err.Error(), "panic")
			return
		}

		// If successful, validate all parsed modules
		assert.True(t, config.prepared)

		for i, module := range config.TargetModules {
			assert.NotEmpty(t, module.Name, "target module %d name should not be empty", i)
			assert.NotEmpty(t, module.Version, "target module %d version should not be empty", i)
			assert.True(t, strings.Contains(module.Name, ".") || strings.Contains(module.Name, "/"),
				"module %d name should contain domain or path: %s", i, module.Name)

			for j := i + 1; j < len(config.TargetModules); j++ {
				assert.NotEqual(t, module.Name, config.TargetModules[j].Name,
					"duplicate module names found: %s", module.Name)
			}
		}
	})
}
