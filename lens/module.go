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

// FindModuleVersionInGoMod parses the given go.mod file to find the version of modName.
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
func DiffModulesFromGoModFiles(oldGoModPath, newGoModPath string) ([]ModuleChange, error) {
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

	var changes []ModuleChange
	for idx, r := range newFile.Require {
		// Include indirect modules for completeness
		newPath := r.Mod.Path
		newVer := r.Mod.Version
		if oldVer, ok := oldReq[newPath]; ok && oldVer != newVer { // only include changes dependencies, not new
			if changes == nil {
				changes = make([]ModuleChange, 0, len(newFile.Require)-idx)
			}
			changes = append(changes, ModuleChange{
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
func AnalyzeModuleChanges(includeTransitive bool, gomodcache, projectDir string, moduleChanges []ModuleChange, neighbourRadius int) ([]*ModuleFunction, []string, error) {
	visited := make(map[string]bool)
	var changedFunctions []*ModuleFunction
	var indirectAnalysis []moduleChangeAnalyzeFunc
	for _, mc := range moduleChanges {
		cf, recursiveCalls, err := analyzeModuleChangesInternal(true, includeTransitive, gomodcache,
			mc.Name, mc.PriorVersion, mc.NewVersion, projectDir, neighbourRadius, visited)
		if err != nil {
			return nil, nil, err
		}
		changedFunctions = append(changedFunctions, cf...)
		indirectAnalysis = append(indirectAnalysis, recursiveCalls...)
	}

	// recursive calls are done in levels; we prefer versions found more directly depended on
	currentLevel := indirectAnalysis
	indirectAnalysis = nil
	for len(currentLevel) > 0 {
		for _, f := range currentLevel {
			cf, recursiveCalls, err := f()
			if err != nil {
				return nil, nil, err
			}
			changedFunctions = append(changedFunctions, cf...)
			indirectAnalysis = append(indirectAnalysis, recursiveCalls...)
		}
		currentLevel = indirectAnalysis
		indirectAnalysis = nil
	}

	checkedModules := slices.Collect(maps.Keys(visited))
	return changedFunctions, checkedModules, nil
}

type moduleChangeAnalyzeFunc func() ([]*ModuleFunction, []moduleChangeAnalyzeFunc, error)

// analyzeModuleChangesInternal does the actual work and uses a visited map to prevent infinite recursion.
func analyzeModuleChangesInternal(root, includeTransitive bool, gomodcache, modName, oldVer, newVer, projectDir string,
	neighbourRadius int, visited map[string]bool) ([]*ModuleFunction, []moduleChangeAnalyzeFunc, error) {
	if visited[modName] { // already analyzed as a root module
		return nil, nil, nil
	} else if root {
		visited[modName] = true
	} else {
		transitiveKey := modName + "@" + oldVer + "->" + newVer
		if visited[transitiveKey] {
			return nil, nil, nil
		}
		visited[transitiveKey] = true
	}
	log.Printf("Analyzing %s@%s -> %s", modName, oldVer, newVer)

	if semver.IsValid(newVer) && semver.IsValid(oldVer) && semver.Compare(newVer, oldVer) <= 0 {
		log.Printf("WARN: %s is not strictly newer than %s", newVer, oldVer)
	}

	// Load pacakges from the local (cached) directories for the old and new module versions
	type loadModuleResult struct {
		dir  string
		pkgs []*packages.Package
		err  error
	}
	resultCh := make(chan loadModuleResult)
	go func() {
		oldDir, oldPkgs, err := loadModulePackageFromCache(gomodcache, modName, oldVer)
		resultCh <- loadModuleResult{oldDir, oldPkgs, err}
	}()
	newDir, newPkgs, err := loadModulePackageFromCache(gomodcache, modName, newVer)
	if err != nil {
		return nil, nil, fmt.Errorf("failure loading module %s@%s: %w", modName, newVer, err)
	}
	oldLoadResult := <-resultCh
	if oldLoadResult.err != nil {
		return nil, nil, fmt.Errorf("failure loading module %s@%s: %w", modName, oldVer, oldLoadResult.err)
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
		newFuncMap, err := aggregateFunctions(newPkg)
		if err != nil {
			return nil, nil, err
		}
		oldPkg, exists := oldPkgMap[newPkg.PkgPath]
		var oldFuncMap map[string]*ModuleFunction
		if exists {
			oldFuncMap, err = aggregateFunctions(oldPkg)
			if err != nil {
				return nil, nil, err
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
		return changes, nil, nil // early return to avoid transitive dependency build below
	}

	// Check for go.mod / go.work differences and recursively analyze changed dependencies
	oldDeps, errOld := parseProjectDeps(oldDir, false)
	newDeps, errNew := parseProjectDeps(newDir, true)
	if errOld != nil || errNew != nil {
		return nil, nil, fmt.Errorf("could not read module files for %s: %w", modName, errors.Join(errOld, errNew))
	}
	projectDeps, err := parseProjectDeps(projectDir, false)
	if err != nil {
		return nil, nil, fmt.Errorf("could not read project dependencies: %w", err)
	}
	var recursiveCalls []moduleChangeAnalyzeFunc
	for dep, newDepVer := range newDeps {
		if oldDepVer, existed := oldDeps[dep]; !existed || oldDepVer != newDepVer {
			if projVer, ok := projectDeps[dep]; ok && projVer != newDepVer {
				recursiveCalls = append(recursiveCalls, func() ([]*ModuleFunction, []moduleChangeAnalyzeFunc, error) {
					return analyzeModuleChangesInternal(false, true, gomodcache,
						dep, projVer, newDepVer, projectDir, neighbourRadius, visited)
				})
			}
		}
	}

	return changes, recursiveCalls, nil
}

func loadModulePackageFromCache(gomodcache, modName, version string) (string, []*packages.Package, error) {
	dir, err := findModulePathInCache(gomodcache, modName, version)
	if err != nil {
		return dir, nil, err
	}
	pkgs, err := packages.Load(&packages.Config{
		Dir: dir,
		Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedName |
			packages.NeedImports | packages.NeedTypes | packages.NeedTypesInfo,
	}, "./...")
	if err != nil {
		return dir, nil, err
	} else if logModuleErrors && packages.PrintErrors(pkgs) > 0 {
		log.Printf("WARN: module contain errors for version %s@%s", modName, version)
	}
	return dir, pkgs, nil
}

// findModulePathInCache attempts to locate module@version in the local module cache.
func findModulePathInCache(gomodcache, modPath, version string) (string, error) {
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

	out := slices.Collect(maps.Keys(seen))
	slices.Sort(out)
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

	result := slices.Collect(maps.Keys(modSet))
	slices.Sort(result)
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
func DiffModulesFromGoWorkFiles(projectDir, newWorkPath string) ([]ModuleChange, error) {
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

	all := make([]ModuleChange, 0, len(dirSet))
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
func aggregateFunctions(pkg *packages.Package) (map[string]*ModuleFunction, error) {
	aggregated := make(map[string]*ModuleFunction)
	for _, file := range pkg.Syntax {
		funcs, err := extractFunctions(file, pkg, pkg.Fset.File(file.Pos()).Name())
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
func extractFunctions(file *ast.File, pkg *packages.Package, filePath string) (functions map[string]*ModuleFunction, err error) {
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
