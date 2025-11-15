package lens

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/printer"
	"io/fs"
	"log"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/go-analyze/bulk"
	"github.com/pmezard/go-difflib/difflib"
	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
	"golang.org/x/mod/semver"
	"golang.org/x/tools/go/packages"
)

const logModuleErrors = false

// FindModuleVersionInGoMod parses the given go.mod file to find the version of the specified module.
// Returns empty string if the module is not found in the go.mod file.
func FindModuleVersionInGoMod(goModFile, modName string) (string, bool, error) {
	data, err := os.ReadFile(goModFile)
	if err != nil {
		return "", false, fmt.Errorf("read %s failed: %w", goModFile, err)
	}
	f, err := modfile.Parse(goModFile, data, nil)
	if err != nil {
		return "", false, fmt.Errorf("parse %s failed: %w", goModFile, err)
	}
	for _, r := range f.Require {
		if r.Mod.Path == modName {
			return r.Mod.Version, r.Indirect, nil
		}
	}
	return "", false, nil
}

// DiffModulesFromGoModFiles returns all direct (non-indirect) modules whose versions
// differ between the “old” and “new” go.mod files.
func DiffModulesFromGoModFiles(oldGoModPath, newGoModPath string) ([]*ModuleChange, error) {
	oldData, err := os.ReadFile(oldGoModPath)
	if err != nil {
		return nil, fmt.Errorf("reading old go.mod %s: %w", oldGoModPath, err)
	}
	newData, err := os.ReadFile(newGoModPath)
	if err != nil {
		return nil, fmt.Errorf("reading new go.mod %s: %w", newGoModPath, err)
	}
	oldFile, err := modfile.Parse(oldGoModPath, oldData, nil)
	if err != nil {
		return nil, fmt.Errorf("parsing old go.mod: %w", err)
	}
	newFile, err := modfile.Parse(newGoModPath, newData, nil)
	if err != nil {
		return nil, fmt.Errorf("parsing new go.mod: %w", err)
	}
	oldReq := make(map[string]string, len(oldFile.Require))
	for _, r := range oldFile.Require {
		oldReq[r.Mod.Path] = r.Mod.Version
	}

	var changes []*ModuleChange
	for idx, r := range newFile.Require {
		// Include indirect modules for completeness
		newPath := r.Mod.Path
		newVer := r.Mod.Version
		if oldVer, ok := oldReq[newPath]; ok && oldVer != newVer { // only include changes dependencies, not new
			if changes == nil {
				changes = make([]*ModuleChange, 0, len(newFile.Require)-idx)
			}
			changes = append(changes, &ModuleChange{
				Name:         newPath,
				PriorVersion: oldReq[newPath],
				NewVersion:   newVer,
				Indirect:     r.Indirect,
			})
		}
	}
	return changes, nil
}

// AnalyzeModuleChanges loads all Go packages for a module between two versions and returns the functions
// that are new or whose definitions have changed. It also checks for go.mod differences to
// analyze dependency changes (if the dependency is also used in the project's go.mod).
//
// Both old and new module versions are loaded in parallel from the module cache. The returned
// changed functions contain the OLD version's Definition with LineChangeBitmap marking changed lines
// in the old definition.
//
// Returns:
//   - map[string][]*ModuleFunction: Changed functions by module (keyed by module name)
//   - map[string][]*packages.Package: NEW version packages for each module (keyed by module name)
//   - []*ModuleFunction: All changed functions (flat list)
//   - []string: Module names that were analyzed
//   - error: Any error during analysis
func AnalyzeModuleChanges(gomodcache string, includeTransitive bool, projectDir string, moduleChanges []*ModuleChange,
	neighbourRadius int) (map[string][]*ModuleFunction, map[string][]*packages.Package, error) {
	visited := make(map[string]bool)
	var indirectAnalysis []moduleChangeAnalyzeFunc

	allModuleData := make(map[string][]*ModuleFunction, len(moduleChanges))
	newVersionPackages := make(map[string][]*packages.Package, len(moduleChanges))

	for _, mc := range moduleChanges {
		cf, pkgs, recursiveCalls, err :=
			analyzeModuleChangesInternal(includeTransitive, mc, gomodcache, projectDir, neighbourRadius, visited)
		if err != nil {
			return nil, nil, err
		}
		indirectAnalysis = append(indirectAnalysis, recursiveCalls...)

		allModuleData[mc.Name] = cf
		if len(pkgs) > 0 {
			newVersionPackages[mc.Name] = pkgs
		}
	}

	// recursive calls are done in levels; we prefer versions found more directly depended on
	currentLevel := indirectAnalysis
	indirectAnalysis = nil
	for len(currentLevel) > 0 {
		for _, f := range currentLevel {
			cf, pkgs, recursiveCalls, err := f()
			if err != nil {
				return nil, nil, err
			}
			indirectAnalysis = append(indirectAnalysis, recursiveCalls...)

			for _, fn := range cf {
				modName := fn.Module.Name
				allModuleData[modName] = append(allModuleData[modName], fn)
				// Store packages using module name from the function's module reference
				if len(pkgs) > 0 && newVersionPackages[modName] == nil {
					newVersionPackages[modName] = pkgs
				}
			}
		}
		currentLevel = indirectAnalysis
		indirectAnalysis = nil
	}

	return allModuleData, newVersionPackages, nil
}

type moduleChangeAnalyzeFunc func() ([]*ModuleFunction, []*packages.Package, []moduleChangeAnalyzeFunc, error)

// analyzeModuleChangesInternal does the actual work and uses a visited map to prevent infinite recursion.
// Returns changed functions (OLD version), NEW version packages, and recursive analysis functions.
func analyzeModuleChangesInternal(includeTransitive bool, mc *ModuleChange, gomodcache, projectDir string,
	neighbourRadius int, visited map[string]bool) ([]*ModuleFunction, []*packages.Package, []moduleChangeAnalyzeFunc, error) {
	if visited[mc.Name] {
		return nil, nil, nil, nil
	}
	visited[mc.Name] = true
	log.Printf("Analyzing %s@%s -> %s", mc.Name, mc.PriorVersion, mc.NewVersion)

	if semver.IsValid(mc.NewVersion) && semver.IsValid(mc.PriorVersion) &&
		semver.Compare(mc.NewVersion, mc.PriorVersion) <= 0 {
		log.Printf("WARN: %s is not strictly newer than %s", mc.NewVersion, mc.PriorVersion)
	}

	// Load packages from the local (cached) directories for the old and new module versions
	type loadModuleResult struct {
		dir  string
		pkgs []*packages.Package
		err  error
	}
	resultCh := make(chan loadModuleResult)
	go func() {
		oldDir, oldPkgs, err := loadModulePackageFromCache(gomodcache, mc.Name, mc.PriorVersion)
		resultCh <- loadModuleResult{oldDir, oldPkgs, err}
	}()
	newDir, newPkgs, err := loadModulePackageFromCache(gomodcache, mc.Name, mc.NewVersion)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("failure loading module %s@%s: %w", mc.Name, mc.NewVersion, err)
	}
	oldLoadResult := <-resultCh
	if oldLoadResult.err != nil {
		return nil, nil, nil, fmt.Errorf("failure loading module %s@%s: %w", mc.Name, mc.PriorVersion, oldLoadResult.err)
	}
	oldDir, oldPkgs := oldLoadResult.dir, oldLoadResult.pkgs

	// Build a map of old packages keyed by their import path (PkgPath), or package name if PkgPath is empty
	oldPkgMap := make(map[string]*packages.Package, len(oldPkgs))
	for _, pkg := range oldPkgs {
		oldPkgMap[pkg.PkgPath] = pkg
	}

	// Iterate over new packages to determine changed functions
	var changes []*ModuleFunction
	for _, newPkg := range newPkgs {
		// Aggregate all functions in the new package
		newFuncMap, err := aggregateFunctions(mc, newPkg)
		if err != nil {
			return nil, nil, nil, err
		}
		oldPkg, exists := oldPkgMap[newPkg.PkgPath]
		var oldFuncMap map[string]*ModuleFunction
		if exists {
			oldFuncMap, err = aggregateFunctions(mc, oldPkg)
			if err != nil {
				return nil, nil, nil, err
			}
		}

		// Compare new functions to the old ones
		for funcKey, newFunc := range newFuncMap {
			if oldFuncMap == nil {
				// new functions can be ignored, we will focus on entry points to functions that already existed
			} else if oldFunc, ok := oldFuncMap[funcKey]; ok /* see above */ && oldFunc.Definition != newFunc.Definition {
				oldFunc.LineChangeBitmap = computeChangeLineBitmap(oldFunc.Definition, newFunc.Definition, false, neighbourRadius)
				changes = append(changes, oldFunc) // add the old function so that the module can accurately be referenced prior to the update
			}
		}
		// we don't iterate over old functions looking for removed functions
		// if a used public function was removed, it will be found in a compile failure
	}

	if !includeTransitive {
		return changes, newPkgs, nil, nil // early return to avoid transitive dependency build below
	}

	// Check for go.mod / go.work differences and recursively analyze changed dependencies
	oldDeps, errOld := parseProjectDeps(oldDir, false)
	newDeps, errNew := parseProjectDeps(newDir, true)
	if errOld != nil || errNew != nil {
		return nil, nil, nil, fmt.Errorf("could not read module files for %s: %w", mc.Name, errors.Join(errOld, errNew))
	}
	projectDeps, err := parseProjectDeps(projectDir, false)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("could not read project dependencies: %w", err)
	}
	var recursiveCalls []moduleChangeAnalyzeFunc
	for dep, newDepVer := range newDeps {
		if oldDepVer, existed := oldDeps[dep]; !existed || oldDepVer != newDepVer {
			if projVer, ok := projectDeps[dep]; ok && projVer != newDepVer {
				recursiveCalls = append(recursiveCalls, func() ([]*ModuleFunction, []*packages.Package, []moduleChangeAnalyzeFunc, error) {
					// Transitive module analysis
					return analyzeModuleChangesInternal(true,
						&ModuleChange{
							Name:         dep,
							PriorVersion: projVer,
							NewVersion:   newDepVer,
							Indirect:     true,
						}, gomodcache, projectDir, neighbourRadius, visited)
				})
			}
		}
	}

	return changes, newPkgs, recursiveCalls, nil
}

func loadModulePackageFromCache(gomodcache, modName, version string) (string, []*packages.Package, error) {
	dir, err := FindModulePathInCache(gomodcache, modName, version)
	if err != nil {
		return dir, nil, err
	}
	pkgs, err := packages.Load(&packages.Config{
		Dir: dir,
		Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedName |
			packages.NeedImports | packages.NeedTypes | packages.NeedTypesInfo,
		Env: append(os.Environ(), GoEnv("", gomodcache)...),
	}, "./...")
	if err != nil {
		return dir, nil, err
	} else if logModuleErrors && packages.PrintErrors(pkgs) > 0 {
		log.Printf("WARN: module contain errors for version %s@%s", modName, version)
	}
	return dir, pkgs, nil
}

// FindModulePathInCache attempts to locate a module@version in the local module cache.
// Returns the filesystem directory where the module source is located.
func FindModulePathInCache(gomodcache, modPath, version string) (string, error) {
	// Attempt to form the actual cache directory name. The local module cache
	// structure is typically: GOPATH/pkg/mod/<escaped module>@<version>.
	escapedMod, err := module.EscapePath(modPath)
	if err != nil {
		return "", err
	}
	modDirName := escapedMod + "@" + version
	dir := filepath.Join(gomodcache, modDirName)

	info, err := os.Stat(dir)
	if err != nil {
		return "", fmt.Errorf("failed to stat %s: %w", dir, err)
	} else if !info.IsDir() {
		return "", fmt.Errorf("not a directory: %s", dir)
	}
	return dir, nil
}

func parseGoMod(gomodPath string) (map[string]string, error) {
	goModData, err := os.ReadFile(gomodPath)
	if err != nil {
		return nil, fmt.Errorf("read %s failed: %w", gomodPath, err)
	}
	modFile, err := modfile.Parse(gomodPath, goModData, nil)
	if err != nil {
		return nil, fmt.Errorf("parse %s failed: %w", gomodPath, err)
	}
	deps := make(map[string]string, len(modFile.Require))
	for _, r := range modFile.Require {
		deps[r.Mod.Path] = r.Mod.Version
	}
	return deps, nil
}

// parseGoWork parses a go.work file and returns module directories relative to the workspace root.
// Globs and "..." are expanded.
func parseGoWork(workPath string) ([]string, error) {
	data, err := os.ReadFile(workPath)
	if err != nil {
		return nil, fmt.Errorf("read %s failed: %w", workPath, err)
	}
	wf, err := modfile.ParseWork(workPath, data, nil)
	if err != nil {
		return nil, fmt.Errorf("parse %s failed: %w", workPath, err)
	}
	workDir := filepath.Dir(workPath)

	seen := make(map[string]struct{})
	add := func(p string) {
		seen[filepath.Clean(p)] = struct{}{}
	}

	// helper to walk a tree for "..."
	walkEllipsis := func(prefix string) error {
		start := filepath.Join(workDir, prefix)
		return filepath.WalkDir(start, func(path string, d fs.DirEntry, err error) error {
			if err != nil || !d.IsDir() {
				return err
			} else if _, err := os.Stat(filepath.Join(path, "go.mod")); err == nil {
				add(path)
			}
			return nil
		})
	}

	for _, u := range wf.Use {
		raw := u.Path

		// Absolute entries are handled separately so we don’t break them with Rel()
		if filepath.IsAbs(raw) {
			switch {
			case strings.HasSuffix(raw, "..."):
				if err := walkEllipsis(strings.TrimSuffix(raw, "...")); err != nil {
					return nil, err
				}
			case strings.ContainsAny(raw, "*?[]"):
				matches, err := filepath.Glob(raw)
				if err != nil {
					return nil, err
				}
				for _, m := range matches {
					if fi, err := os.Stat(m); err == nil && fi.IsDir() {
						add(m)
					}
				}
			default:
				add(raw)
			}
			continue
		}

		// Relative path, evaluate against workDir
		switch {
		case strings.HasSuffix(raw, "..."):
			if err := walkEllipsis(strings.TrimSuffix(raw, "...")); err != nil {
				return nil, err
			}
		case strings.ContainsAny(raw, "*?[]"):
			matches, err := filepath.Glob(filepath.Join(workDir, raw))
			if err != nil {
				return nil, err
			}
			for _, m := range matches {
				if fi, err := os.Stat(m); err == nil && fi.IsDir() {
					rel, _ := filepath.Rel(workDir, m) // cannot fail
					add(rel)
				}
			}
		default:
			rel, _ := filepath.Rel(workDir, filepath.Join(workDir, raw))
			add(rel)
		}
	}

	out := slices.Sorted(maps.Keys(seen))
	return out, nil
}

// resolveGoModPath returns the absolute path to a go.mod file given a project directory and a module directory.
func resolveGoModPath(projectDir, dir string) string {
	if filepath.IsAbs(dir) {
		return filepath.Join(dir, "go.mod")
	}
	return filepath.Join(projectDir, dir, "go.mod")
}

// parseProjectDeps reads dependencies from either a single go.mod or a go.work workspace.
func parseProjectDeps(projectDir string, preferNewest bool) (map[string]string, error) {
	rootMod := filepath.Join(projectDir, "go.mod")
	workFile := filepath.Join(projectDir, "go.work")

	// versionsMap collects every version seen for each module path
	versionsMap := make(map[string][]string)

	if FileExists(rootMod) { // root module if present
		rootDeps, err := parseGoMod(rootMod)
		if err != nil {
			return nil, err
		}
		for modPath, ver := range rootDeps {
			versionsMap[modPath] = append(versionsMap[modPath], ver)
		}
	}

	if FileExists(workFile) { // workspace modules
		dirs, err := parseGoWork(workFile)
		if err != nil {
			return nil, err
		}
		for _, dir := range dirs {
			gm := resolveGoModPath(projectDir, dir)
			if _, err := os.Stat(gm); err != nil {
				continue // skip missing or unreadable module rather than failing the whole parse
			}
			mdeps, err := parseGoMod(gm)
			if err != nil {
				return nil, err
			}
			for modPath, ver := range mdeps {
				versionsMap[modPath] = append(versionsMap[modPath], ver)
			}
		}
	}

	// choose the min or max semver per module
	deps := make(map[string]string, len(versionsMap))
	for modPath, vers := range versionsMap {
		chosen := vers[0]
		for _, v := range vers[1:] {
			if preferNewest {
				if semver.Compare(v, chosen) > 0 {
					chosen = v
				}
			} else {
				if semver.Compare(v, chosen) < 0 {
					chosen = v
				}
			}
		}
		deps[modPath] = chosen
	}
	if len(deps) == 0 {
		return nil, fmt.Errorf("no go.mod or go.work found in %s", projectDir)
	}
	return deps, nil
}

// ProjectGoModFiles returns all go.mod files for the project directory, supporting workspaces via go.work.
func ProjectGoModFiles(projectDir string) ([]string, error) {
	rootMod := filepath.Join(projectDir, "go.mod")
	workFile := filepath.Join(projectDir, "go.work")
	rootExists := FileExists(rootMod)
	workExists := FileExists(workFile)

	if !rootExists && !workExists {
		return nil, fmt.Errorf("no go.mod or go.work in %s", projectDir)
	}

	modSet := make(map[string]bool)

	if rootExists {
		modSet[rootMod] = true
	}

	if workExists {
		dirs, err := parseGoWork(workFile)
		if err != nil {
			return nil, err
		}
		for _, dir := range dirs {
			gm := resolveGoModPath(projectDir, dir)
			if FileExists(gm) {
				modSet[gm] = true
			}
		}
	}

	result := slices.Sorted(maps.Keys(modSet))
	return result, nil
}

// ProjectPackagePatterns returns go test patterns for all modules in projectDir.
// Each pattern includes "/..." for recursive package loading.
func ProjectPackagePatterns(projectDir string) ([]string, error) {
	mods, err := ProjectGoModFiles(projectDir)
	if err != nil {
		return nil, err
	}
	patterns := make([]string, 0, len(mods))
	for _, gm := range mods {
		dir := filepath.Dir(gm)
		if filepath.Clean(dir) == filepath.Clean(projectDir) {
			patterns = append(patterns, "./...")
			continue
		}

		rel, err := filepath.Rel(projectDir, dir)
		if err == nil && !strings.HasPrefix(rel, "..") {
			patterns = append(patterns, "./"+filepath.ToSlash(filepath.Join(rel, "...")))
			continue
		}

		patterns = append(patterns, filepath.ToSlash(filepath.Join(dir, "...")))
	}
	return patterns, nil
}

// FindModuleVersion searches for modName across all go.mod files in projectDir.
func FindModuleVersion(projectDir, modName string) (string, bool, error) {
	mods, err := ProjectGoModFiles(projectDir)
	if err != nil {
		return "", false, err
	}
	for _, gm := range mods {
		ver, indirect, err := FindModuleVersionInGoMod(gm, modName)
		if err != nil {
			return "", false, err
		} else if ver != "" {
			return ver, indirect, nil
		}
	}
	return "", false, nil
}

// DiffModulesFromGoWorkFiles returns changed modules across all go.mod files referenced by a go.work workspace.
func DiffModulesFromGoWorkFiles(projectDir, newWorkPath string) ([]*ModuleChange, error) {
	oldDirs, err := parseGoWork(filepath.Join(projectDir, "go.work"))
	if err != nil {
		return nil, err
	}
	newDirs, err := parseGoWork(newWorkPath)
	if err != nil {
		return nil, err
	}

	dirSet := bulk.SliceToSet(oldDirs, newDirs)
	newRoot := filepath.Dir(newWorkPath)

	// resolve turns a workspace-relative entry into an absolute go.mod path
	resolve := func(root, dir string) string {
		if filepath.IsAbs(dir) {
			return filepath.Join(dir, "go.mod")
		}
		return filepath.Clean(filepath.Join(root, dir, "go.mod"))
	}

	all := make([]*ModuleChange, 0, len(dirSet))
	for dir := range dirSet {
		oldGM := resolve(projectDir, dir)
		newGM := resolve(newRoot, dir)

		if _, errOld := os.Stat(oldGM); errOld != nil {
			continue // directory is new only, not relevant to current project
		} else if _, errNew := os.Stat(newGM); errNew != nil {
			continue // directory was removed -> ignore
		}
		changes, err := DiffModulesFromGoModFiles(oldGM, newGM)
		if err != nil {
			return nil, err
		}
		all = append(all, changes...)
	}
	return all, nil
}

// aggregateFunctions aggregates functions from all AST files in the given package.
// It returns a map keyed by a normalized function key, which includes the package name and receiver type (if any),
// to the extracted Function.
func aggregateFunctions(mod *ModuleChange, pkg *packages.Package) (map[string]*ModuleFunction, error) {
	aggregated := make(map[string]*ModuleFunction)
	for _, file := range pkg.Syntax {
		funcs, err := extractFunctions(mod, file, pkg, pkg.Fset.File(file.Pos()).Name())
		if err != nil {
			return nil, err
		}
		for key, f := range funcs {
			aggregated[key] = f
		}
	}
	return aggregated, nil
}

// extractFunctions extracts function declarations from an ast.File and returns a map keyed by function name.
func extractFunctions(mod *ModuleChange, file *ast.File, pkg *packages.Package, filePath string) (functions map[string]*ModuleFunction, err error) {
	functions = make(map[string]*ModuleFunction)

	// Remove Comments (and Doc when inspecting) to reduce false positives
	file.Comments = nil

	var buf bytes.Buffer
	ast.Inspect(file, func(n ast.Node) bool {
		if funcDecl, ok := n.(*ast.FuncDecl); ok {
			funcDecl.Doc = nil // exclude from definition to avoid comparing docs

			p := &printer.Config{
				Mode:     printer.TabIndent,
				Tabwidth: 2,
			}
			buf.Reset()
			if err = p.Fprint(&buf, pkg.Fset, funcDecl); err != nil {
				return false
			}

			key := MakeFunctionIdent(pkg.PkgPath, funcDecl)
			entryLineNumber, returnPoints, endsInPanic := AnalyzeASTFunctionReturnPoints(pkg.Fset, funcDecl)
			functions[key] = &ModuleFunction{
				Function: Function{
					FilePath:        filePath,
					PackageName:     pkg.PkgPath,
					FunctionIdent:   key,
					FunctionName:    funcDecl.Name.Name,
					EntryLineNumber: entryLineNumber,
					ReturnPoints:    returnPoints,
					ReturnPanic:     endsInPanic,
				},
				Definition: buf.String(),
				Module:     mod,
			}
		}
		return true
	})

	return
}

// computeChangeLineBitmap compares two versions of a function's source.
// It returns a []bool where each index corresponds to one line in the chosen definition.
// If newFunc == true, the bitmap’s indices align with newDef’s lines; if newFunc == false,
// the indices align with oldDef’s lines.
func computeChangeLineBitmap(oldDef, newDef string, newFunc bool, neighbourRadius int) []bool {
	oldLines := strings.Split(oldDef, "\n")
	newLines := strings.Split(newDef, "\n")

	matcher := difflib.NewMatcher(oldLines, newLines)
	opcodes := matcher.GetOpCodes()

	var bitmap []bool
	if newFunc {
		bitmap = make([]bool, len(newLines))
	} else {
		bitmap = make([]bool, len(oldLines))
	}
	markChanged := func(idx int) {
		if idx >= 0 && idx < len(bitmap) {
			bitmap[idx] = true
		}
	}
	markWithRadius := func(idx int, radius int) {
		markChanged(idx)
		for r := 1; r <= radius; r++ {
			markChanged(idx - r)
			markChanged(idx + r)
		}
	}

	for _, code := range opcodes {
		if code.Tag == 'e' {
			continue // equal block, skip
		}
		// For non-equal blocks, determine which index range to mark
		if newFunc {
			for j := code.J1; j < code.J2; j++ {
				if code.Tag == 'i' {
					markWithRadius(j, neighbourRadius)
				} else {
					markChanged(j)
				}
			}
		} else {
			// focusing on the old definition
			if code.Tag != 'i' { // deletions or replacements – mark deleted range
				for i := code.I1; i < code.I2; i++ {
					markChanged(i)
				}
			}
			if code.Tag == 'i' {
				// For an insertion, we mark the neighboring lines only.
				// Radius is exclusive here (r < radius) so that with radius==1 we flag exactly
				// the line before and the line after the gap, matching expectations in unit-tests.
				for r := 0; r < neighbourRadius; r++ {
					markChanged(code.I1 - 1 - r) // line(s) before
					markChanged(code.I1 + r)     // line(s) after
				}
			}
		}
	}

	return bitmap
}

// ExtractModuleFunctionsFromPackages extracts function definitions from pre-loaded packages.
// Useful for extension configs that need to analyze module functions without re-parsing.
func ExtractModuleFunctionsFromPackages(pkgs []*packages.Package, moduleChange *ModuleChange) ([]*ModuleFunction, error) {
	if len(pkgs) == 0 {
		return nil, nil
	}

	var functions []*ModuleFunction
	var buf bytes.Buffer

	for _, pkg := range pkgs {
		// Skip packages with errors unless we have some valid files
		if len(pkg.Errors) > 0 && len(pkg.Syntax) == 0 {
			if logModuleErrors {
				log.Printf("Package %s has errors: %v", pkg.PkgPath, pkg.Errors)
			}
			continue
		}

		// Process each file in the package
		for _, file := range pkg.Syntax {
			filePath := pkg.Fset.File(file.Pos()).Name()

			// Walk the AST to find function declarations
			for _, decl := range file.Decls {
				funcDecl, ok := decl.(*ast.FuncDecl)
				if !ok {
					continue
				}

				// Extract function definition
				p := &printer.Config{
					Mode:     printer.TabIndent,
					Tabwidth: 2,
				}
				buf.Reset()
				if err := p.Fprint(&buf, pkg.Fset, funcDecl); err != nil {
					if logModuleErrors {
						log.Printf("Failed to print function %s: %v", funcDecl.Name.Name, err)
					}
					continue
				}

				// Analyze function return points
				entryLineNumber, returnPoints, endsInPanic := AnalyzeASTFunctionReturnPoints(pkg.Fset, funcDecl)

				// Create function identifier
				funcIdent := MakeFunctionIdent(pkg.PkgPath, funcDecl)

				functions = append(functions, &ModuleFunction{
					Function: Function{
						FilePath:        filePath,
						PackageName:     pkg.PkgPath,
						FunctionIdent:   funcIdent,
						FunctionName:    funcDecl.Name.Name,
						EntryLineNumber: entryLineNumber,
						ReturnPoints:    returnPoints,
						ReturnPanic:     endsInPanic,
					},
					Definition: buf.String(),
					Module:     moduleChange,
				})
			}
		}
	}

	return functions, nil
}
