package cmd

import (
	"errors"
	"flag"
	"go/build"
	"os"
	"path/filepath"
	"strconv"

	"github.com/PatchLens/go-update-lens/lens"
)

// CustomFlag defines a custom CLI option.
type CustomFlag struct {
	Name         string
	DefaultValue any
	Usage        string
	Type         string // "string", "int", "bool"
}

// ParseFlags builds Config from standard and custom flags.
func ParseFlags(customFlags []CustomFlag) (*lens.Config, error) {
	config := &lens.Config{CustomFlags: make(map[string]string)}

	// Define all standard flags
	projectDir := flag.String("project", "", "Path to the project directory")
	moduleVersionFlag := flag.String("module", "", "module@version update to analyze (e.g., github.com/foo/bar@v1.2.3)")
	modulesVersionFlag := flag.String("modules", "", "module1@version,module2@version update to analyze")
	updatedGoModFile := flag.String("gomod", "", "Path to an updated go.mod file to determine updates")
	updatedGoWorkFile := flag.String("gowork", "", "Path to an updated go.work file to determine updates")
	astMonitorPort := flag.Int("monitorport", 44440, "Port to bind to for execution monitoring")
	reportJsonFile := flag.String("json", "modreport.json", "File to output analysis details")
	reportChartsFile := flag.String("charts", "modreport.png", "File to output analysis overview chart image")
	maxFieldRecurse := flag.Int("fieldrecurse", 20, "Maximum field recurse, increases accuracy but also memory usage")
	maxFieldLen := flag.Int("fieldlen", 1024, "Maximum slice and string length, too small may miss changes, but increases memory usage")
	cacheMB := flag.Int("cachemb", 200, "Cache memory budget in MB")
	mutationScope := flag.String("mutationscope", "line", "Set mutation scope, values can be: function, line (default), area, none")
	mutationMode := flag.String("mutationset", "fast", "Set mutation set, values can be: full, fast (default)")
	mutationTests := flag.String("mutationtests", "targeted", "Set mutation unit test selection, values can be: full, targeted (default)")
	tmpCopy := flag.Bool("tmpcopy", true, "Copy project and GOPATH to temp directory for analysis")
	timeMultiplier := flag.Int("timemultiplier", 2, "Time change multiplier for performance regression detection (default 2)")

	// Define custom flags
	customPtrs := make(map[string]interface{})
	for _, cf := range customFlags {
		switch cf.Type {
		case "string":
			customPtrs[cf.Name] = flag.String(cf.Name, cf.DefaultValue.(string), cf.Usage)
		case "int":
			customPtrs[cf.Name] = flag.Int(cf.Name, cf.DefaultValue.(int), cf.Usage)
		case "bool":
			customPtrs[cf.Name] = flag.Bool(cf.Name, cf.DefaultValue.(bool), cf.Usage)
		}
	}

	flag.Parse()

	// Validate standard flags
	if (*moduleVersionFlag == "" && *modulesVersionFlag == "" && *updatedGoModFile == "" && *updatedGoWorkFile == "") || *projectDir == "" {
		return nil, errors.New("single Module Usage: -project ../foo -module <module>@<version>\ngo.mod Usage: -project ../foo -gomod ../foo-updated/go.mod\ngo.work Usage: -project ../foo -gowork ../foo-updated/go.work")
	} else if *updatedGoModFile != "" && *updatedGoWorkFile != "" {
		return nil, errors.New("-gomod and -gowork are mutually exclusive")
	}

	// Populate config
	config.ProjectDir = *projectDir
	config.ModuleVersionFlag = *moduleVersionFlag
	config.ModulesVersionFlag = *modulesVersionFlag
	config.UpdatedGoModFile = *updatedGoModFile
	config.UpdatedGoWorkFile = *updatedGoWorkFile
	config.AstMonitorPort = *astMonitorPort
	config.ReportJsonFile = *reportJsonFile
	config.ReportChartsFile = *reportChartsFile
	config.MaxFieldRecurse = *maxFieldRecurse
	config.MaxFieldLen = *maxFieldLen
	config.CacheMB = *cacheMB
	config.MutationScope = *mutationScope
	config.MutationMode = *mutationMode
	config.MutationTests = *mutationTests
	config.TmpCopy = *tmpCopy
	config.TimeMultiplier = *timeMultiplier

	// Populate custom flags - convert all to strings for ease of use
	for name, ptr := range customPtrs {
		switch v := ptr.(type) {
		case *string:
			config.CustomFlags[name] = *v
		case *int:
			config.CustomFlags[name] = strconv.Itoa(*v)
		case *bool:
			config.CustomFlags[name] = strconv.FormatBool(*v)
		}
	}

	// Path resolution and environment setup
	if err := setupEnvironment(config); err != nil {
		return nil, err
	}

	return config, nil
}

func setupEnvironment(c *lens.Config) error {
	// Setup GOPATH and GOMODCACHE
	c.Gopath = build.Default.GOPATH
	c.Gomodcache = os.Getenv("GOMODCACHE")
	if c.Gomodcache == "" {
		if c.Gopath == "" {
			return errors.New("neither GOMODCACHE nor GOPATH is set")
		}
		c.Gomodcache = filepath.Join(c.Gopath, "pkg", "mod")
	}

	return nil
}
