package lens

import (
	"fmt"
	"log"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
)

const debugMutationTesting = false

var disabledMutations = []string{
	// LOW VALUE BEHAVIOR MUTATIONS
	// arithmetic/assignment - Replaces compound assignments with simple assignment (+= -> =).
	// These mutations often yield semantically equivalent code paths.
	"arithmetic/assignment",
	// numbers/decrementer - Subtracts one to each numeric literal. A very high mutation rate which significantly slows testing.
	"numbers/decrementer",
	// numbers/incrementer - Adds one to each numeric literal. Too frequent to generally include.
	"numbers/incrementer",

	// LOOPING LOGIC - may increase execution time
	// loop/break - Removes loop break conditions.
	"loop/break",
	// loop/condition - Alters loop conditions to constants (i<n -> 1<1).
	"loop/condition",
	// loop/range_break - Targets `for … range` loops, removing or inverting early exits.
	"loop/range_break",

	// REMOVE OPERATIONS - usually trivial mutations to detect
	// branch/case - Empties case bodies in switch statements.
	// Switch-case removals often collide with default or fall-through behavior, yielding false positives or trivial kills.
	"branch/case",
	// expression/remove - Strips entire expressions, which rarely reflects realistic regressions.
	"expression/remove",
	// statement/remove - Deletes whole statements, similar to expression/remove above.
	"statement/remove",
}

// RunMutationTesting runs mutation testing targeted to the module changes.
func RunMutationTesting(gopath, gomodcache, projectDir string, fastMutations, lineScopedMutations, runTargetedTests bool,
	moduleChanges []*ModuleFunction, testFunctions []*TestFunction) (MutationResult, error) {
	// Regex to parse the summary line:
	//   The mutation score is 0.750000 (6 passed, 2 failed, 0 duplicated, 0 skipped, total is 8)
	summaryRe := regexp.MustCompile(
		`The mutation score is .* \((\d+) passed, (\d+) failed, (\d+) duplicated, (\d+) skipped, total is (\d+)\)`)

	// TODO - FUTURE - should we do mutation testing against the new version? Would be more useful for full mutation strategy

	// Collect the set of files containing the changed functions this test covers
	fileToTests := make(map[string][]string)
	for _, testFunc := range testFunctions {
		for _, target := range testFunc.Targets {
			for _, change := range target.ChangeFunctions {
				abs, err := filepath.Abs(change.FilePath)
				if err != nil {
					return MutationResult{}, err
				}
				existing := fileToTests[abs]
				if !slices.Contains(existing, testFunc.FunctionName) {
					fileToTests[abs] = append(existing, testFunc.FunctionName)
				}
			}
		}
	}
	mutationFiles := make([]string, 0, len(moduleChanges))
	mutationFunctions := make([]string, 0, len(moduleChanges))
	if lineScopedMutations {
		// Disable mutation on unchanged lines by inserting the go-mutesting directive
		astEditor := &ASTModifier{}
		defer func() {
			errs := astEditor.Restore(GoEnv(gopath, gomodcache))
			if len(errs) > 0 {
				log.Printf("%sFailed to cleanup AST change (%d): %v", ErrorLogPrefix, len(errs), errs[0])
			}
		}()

		errGrp := ErrGroupLimitCPU()
		for _, change := range moduleChanges {
			if len(change.LineChangeBitmap) == 0 {
				return MutationResult{}, fmt.Errorf("bug: LineChangeBitmap not initialized: %s", change.FunctionIdent)
			} else if !slices.Contains(change.LineChangeBitmap, true) {
				continue // function only had additions, no changed logic to mutate (all lines would be excluded)
			}

			// add the function name to include in the mutation set
			mutationFunctions = append(mutationFunctions, change.FunctionName)
			abs, err := filepath.Abs(change.FilePath)
			if err != nil {
				return MutationResult{}, err
			}
			if !slices.Contains(mutationFiles, abs) {
				mutationFiles = append(mutationFiles, abs)
			}
			errGrp.Go(func() error {
				return astEditor.InsertFuncLines(&change.Function, func(i int, line string) (string, bool) {
					if i < len(change.LineChangeBitmap) && !change.LineChangeBitmap[i] {
						return "// mutator-disable-next-line *", true
					}
					return "", true
				})
			})
		}
		if err := errGrp.Wait(); err != nil {
			return MutationResult{}, err
		} else if err := astEditor.Commit(); err != nil {
			return MutationResult{}, err
		}
	} else {
		// add all functions names to be used for `--match`
		for _, change := range moduleChanges {
			mutationFunctions = append(mutationFunctions, change.FunctionName)

			if abs, err := filepath.Abs(change.FilePath); err != nil {
				return MutationResult{}, err
			} else if !slices.Contains(mutationFiles, abs) {
				mutationFiles = append(mutationFiles, abs)
			}
		}
	}

	patterns, err := ProjectPackagePatterns(projectDir)
	if err != nil {
		return MutationResult{}, err
	}

	// Build the appropriate exec script
	var execScript string
	if runTargetedTests {
		execScript, err = buildExecSelectTestsScript(fileToTests, patterns) // run targeted tests only for speed
	} else {
		execScript, err = buildExecAllTestsScript(patterns) // run all tests, but only mutate module changes
	}
	if err != nil {
		return MutationResult{}, fmt.Errorf("error building mutation script: %w", err)
	}
	defer func() { _ = os.Remove(execScript) }()

	args := []string{"--exec", execScript, "--match", "(" + strings.Join(mutationFunctions, "|") + ")"}
	args = append(args, mutationFiles...)
	if fastMutations {
		for _, test := range disabledMutations {
			args = append(args, "--disable", test)
		}
	}
	var outBytes []byte
	if debugMutationTesting {
		args = append([]string{"--verbose"}, args...)
		outBytes, err = NewProjectCapturedOutputExec(projectDir, GoEnv(gopath, gomodcache), "go-mutesting", args...)
	} else {
		cmd := NewProjectExec(projectDir, GoEnv(gopath, gomodcache), "go-mutesting", args...)
		outBytes, err = cmd.CombinedOutput()
	}
	if err != nil {
		return MutationResult{}, fmt.Errorf("error running mutation tests: %w", err)
	}

	// Parse the summary line for passed (killed) and total mutants
	out := string(outBytes)
	m := summaryRe.FindStringSubmatch(out)
	if m == nil {
		return MutationResult{}, fmt.Errorf("could not parse mutation summary:\n%s", out)
	}

	logMsg := strings.ReplaceAll(m[0], "The mutation score is", "Mutation score:")
	suffixIndex := strings.Index(logMsg, "failed")
	if suffixIndex > 0 {
		logMsg = logMsg[:suffixIndex] + "detected)"
	}
	logMsg = strings.ReplaceAll(logMsg, "passed", "alive")
	log.Println(logMsg)
	killed, _ := strconv.Atoi(m[2])
	total, _ := strconv.Atoi(m[5])

	// remove unnecessary report.json report (for now)
	go func() { _ = os.Remove(filepath.Join(projectDir, "report.json")) }()

	return MutationResult{
		MutationCount: total,
		SquashedCount: killed,
	}, nil
}

const scriptFinishCheck = `if [ "$MUTATE_DEBUG" = true ] || [ "$MUTATE_VERBOSE" = true ] ; then
	echo "$GOMUTESTING_TEST"
fi

case $GOMUTESTING_RESULT in
0) # tests passed -> FAIL
	echo "$GOMUTESTING_DIFF"
	exit 1
	;;
1) # tests failed -> PASS
	exit 0
	;;
2) # did not compile -> SKIP
	if [ "$MUTATE_VERBOSE" = true ] ; then
		echo "Mutation did not compile"
	fi
	exit 2
	;;
*) # Unknown exit code -> SKIP
	echo "Unknown exit code"
	echo "$GOMUTESTING_DIFF"
	exit $GOMUTESTING_RESULT
	;;
esac`

func buildExecSelectTestsScript(fileToTests map[string][]string, packages []string) (string, error) {
	file, err := os.CreateTemp("", "mutationexec-*.sh")
	if err != nil {
		return "", err
	}

	if _, err := file.WriteString(`#!/usr/bin/env bash

`); err != nil {
		return "", err
	}
	if _, err := fmt.Fprintf(file, "PKGS=\"%s\"\n", strings.Join(packages, " ")); err != nil {
		return "", err
	}

	// Declare the associative array. Map from absolute file‐path -> space‐separated list of test names
	if _, err := file.WriteString("declare -A FILE_TEST_MAP\n"); err != nil {
		return "", err
	}

	// Sort keys for reproducible output (in case of inter-test interactions)
	keys := slices.Sorted(maps.Keys(fileToTests))

	// Populate the associative array
	for _, fp := range keys {
		tests := fileToTests[fp]
		// Sort test names so the regex is deterministic
		sort.Strings(tests)
		// Escape any special characters by wrapping in quotes
		if _, err := fmt.Fprintf(file, `FILE_TEST_MAP["%s"]="%s"
`, fp, strings.Join(tests, " ")); err != nil {
			return "", err
		}
	}

	// The core logic: figure out which tests to run for this mutant
	// Identify which file was mutated (via MUTATE_ORIGINAL)
	if _, err := file.WriteString(`orig="$MUTATE_ORIGINAL"
# Look up the tests for that file
tests="${FILE_TEST_MAP[$orig]}"
# If no tests cover this file, skip (unexpected)
if [ -z "$tests" ]; then
  exit 2
fi
# Build a single -run regex from the space-separated test names
pattern="^($(echo "$tests" | tr ' ' '|'))$" # -> ^(TestA|TestB)$

# Back up the original file and overwrite it with the mutant
mv "$MUTATE_ORIGINAL" "$MUTATE_ORIGINAL.mbkp" || {
  echo "skip: cannot rename $MUTATE_ORIGINAL (tmpcopy enabled?)" 1>&2
  exit 2
}
trap 'mv "$MUTATE_ORIGINAL.mbkp" "$MUTATE_ORIGINAL"' EXIT
cp "$MUTATE_CHANGED" "$MUTATE_ORIGINAL" || { exit 2; }

# Run only the affected tests
export MUTATE_TIMEOUT=${MUTATE_TIMEOUT:-30}
GOMUTESTING_TEST=$(go test -count=1 -timeout=$(printf '%ds' $MUTATE_TIMEOUT) -run "$pattern" $PKGS 2>&1)
export GOMUTESTING_RESULT=$?

`); err != nil {
		return "", err
	} else if _, err := file.WriteString(scriptFinishCheck); err != nil {
		return "", err
	}

	if err := file.Close(); err != nil {
		return "", err
	} else if err := os.Chmod(file.Name(), 0o755); err != nil {
		return "", err
	}
	return file.Name(), nil
}

func buildExecAllTestsScript(packages []string) (string, error) {
	const scriptTmpl = `#!/usr/bin/env bash
PKGS="%s"
if [ -z ${MUTATE_CHANGED+x} ]; then echo "MUTATE_CHANGED is not set"; exit 1; fi
if [ -z ${MUTATE_ORIGINAL+x} ]; then echo "MUTATE_ORIGINAL is not set"; exit 1; fi
if [ -z ${MUTATE_PACKAGE+x} ]; then echo "MUTATE_PACKAGE is not set"; exit 1; fi

export GOMUTESTING_DIFF=$(diff -u $MUTATE_ORIGINAL $MUTATE_CHANGED)

mv $MUTATE_ORIGINAL $MUTATE_ORIGINAL.mbkp || {
 echo "skip: cannot rename $MUTATE_ORIGINAL (need to run with tmpcopy enabled?)" 1>&2
 exit 2
}
trap 'mv "$MUTATE_ORIGINAL.mbkp" "$MUTATE_ORIGINAL"' EXIT
cp $MUTATE_CHANGED $MUTATE_ORIGINAL || { exit 2; }

export MUTATE_TIMEOUT=${MUTATE_TIMEOUT:-30}

GOMUTESTING_TEST=$(go test -count=1 -timeout=$(printf '%%ds' $MUTATE_TIMEOUT) $PKGS 2>&1)
export GOMUTESTING_RESULT=$?

` + scriptFinishCheck

	file, err := os.CreateTemp("", "mutationexec-*.sh")
	if err != nil {
		return "", err
	} else if _, err = fmt.Fprintf(file, scriptTmpl, strings.Join(packages, " ")); err != nil {
		_ = file.Close()
		return "", err
	} else if err = file.Close(); err != nil {
		return "", err
	}
	return file.Name(), os.Chmod(file.Name(), 0o755)
}
