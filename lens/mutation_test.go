package lens

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestParseMutationSummary(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		name        string
		out         string
		expect      MutationResult
		expectLog   string
		expectError bool
	}{
		{
			name:      "partial_kills",
			out:       "The mutation score is 0.750000 (6 passed, 2 failed, 0 duplicated, 0 skipped, total is 8)",
			expect:    MutationResult{MutationCount: 8, SquashedCount: 6},
			expectLog: "Mutation score: 0.750000 (6 detected, 2 alive, 0 duplicated, 0 skipped, total is 8)",
		},
		{
			name:      "all_killed",
			out:       "The mutation score is 1.000000 (5 passed, 0 failed, 0 duplicated, 0 skipped, total is 5)",
			expect:    MutationResult{MutationCount: 5, SquashedCount: 5},
			expectLog: "Mutation score: 1.000000 (5 detected, 0 alive, 0 duplicated, 0 skipped, total is 5)",
		},
		{
			name:      "none_killed",
			out:       "The mutation score is 0.000000 (0 passed, 3 failed, 0 duplicated, 0 skipped, total is 3)",
			expect:    MutationResult{MutationCount: 3, SquashedCount: 0},
			expectLog: "Mutation score: 0.000000 (0 detected, 3 alive, 0 duplicated, 0 skipped, total is 3)",
		},
		{
			name:      "skipped_and_duplicated",
			out:       "The mutation score is 1.000000 (6 passed, 0 failed, 2 duplicated, 2 skipped, total is 8)",
			expect:    MutationResult{MutationCount: 8, SquashedCount: 6},
			expectLog: "Mutation score: 1.000000 (6 detected, 0 alive, 2 duplicated, 2 skipped, total is 8)",
		},
		{
			name: "embedded_in_full_output",
			out: `{"some": "json report"}
PASS github.com/example/pkg
The mutation score is 0.500000 (2 passed, 2 failed, 1 duplicated, 0 skipped, total is 4)
`,
			expect:    MutationResult{MutationCount: 4, SquashedCount: 2},
			expectLog: "Mutation score: 0.500000 (2 detected, 2 alive, 1 duplicated, 0 skipped, total is 4)",
		},
		{
			name:        "missing_summary",
			out:         "no summary here\n",
			expectError: true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result, logMsg, err := parseMutationSummary(tc.out)
			if tc.expectError {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tc.out)
				return
			}
			require.NoError(t, err)
			assert.Equal(t, tc.expect, result)
			assert.Equal(t, tc.expectLog, logMsg)
		})
	}
}
