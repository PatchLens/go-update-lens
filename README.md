# PatchLens

A Go dependency update analysis tool that detects behavior changes when updating module dependencies. PatchLens analyzes the interaction between your Go project and dependency updates by locating intersecting call sites and running execution analysis before and after updates to detect behavior changes. Mutation testing provides a confidence score on regression detection.

## Features

- **Static Analysis**: Identifies all call sites affected by dependency updates
- **Execution Monitoring**: Captures field states and method calls during test execution
- **Mutation Testing**: Validates test coverage quality for affected code
- **Performance Regression Detection**: Identifies performance changes in updated dependencies
- **Comprehensive Reporting**: Generates detailed JSON reports and visual charts
- **Workspace Support**: Analyzes go.work files for monorepo projects

## How It Works

1. Identify module updates via command flags or a provided `go.mod`/`go.work`
2. Compare old and new module versions to locate changed functions
3. Perform static analysis on the project to find callers of those changes
4. Discover tests exercising the calling functions
5. Run tests before and after the update while monitoring field and behavior changes
6. Mutate the changed functions and rerun tests to compute a confidence score
7. Generate a JSON report and overview chart summarizing the results

## Installation

### Setup

1. Clone the repository:
```bash
git clone https://github.com/PatchLens/go-update-lens.git
cd go-update-lens
```

2. Install dependencies and mutation testing tool:
```bash
make setup
```

3. Build the binaries:
```bash
make build
```

This creates two executables in the `bin/` directory:
- `modlens`: Main analysis tool
- `report`: Report json -> png visualization generator

## Usage

### Basic Analysis

Analyze a single module update:
```bash
bin/modlens -project /path/to/your/project -module github.com/example/lib@v1.2.3
```

Analyze multiple module updates:
```bash
bin/modlens -project /path/to/your/project -modules github.com/lib1@v1.0.0,github.com/lib2@v2.0.0
```

### Using go.mod or go.work Files

Analyze updates from an updated go.mod file:
```bash
bin/modlens -project /path/to/your/project -gomod /path/to/updated/go.mod
```

Analyze updates from an updated go.work file:
```bash
bin/modlens -project /path/to/your/project -gowork /path/to/updated/go.work
```

### Configuration Options

| Flag | Default | Description |
|------|---------|-------------|
| `-project` | (required) | Path to the project directory |
| `-module` | - | Single module@version to analyze |
| `-modules` | - | Comma-separated module@version pairs |
| `-gomod` | - | Path to updated go.mod file |
| `-gowork` | - | Path to updated go.work file |
| `-json` | `modreport.json` | Output file for analysis details |
| `-charts` | `modreport.png` | Output file for visual report |
| `-monitorport` | `44440` | Port for execution monitoring |
| `-fieldrecurse` | `20` | Maximum field recursion depth |
| `-fieldlen` | `1024` | Maximum slice/string length |
| `-cachemb` | `200` | Cache memory budget in MB |
| `-mutationscope` | `line` | Mutation scope: function, line, area, or none |
| `-mutationset` | `fast` | Mutation set: full or fast |
| `-mutationtests` | `targeted` | Test selection: full or targeted |
| `-tmpcopy` | `true` | Copy project to temp directory |
| `-timemultiplier` | `2` | Performance regression detection threshold |

### Generating Visual Reports

After running the analysis, generate a visual report from the JSON output:
```bash
bin/report -json modreport.json -charts modreport.png
```

## Output

PatchLens generates two types of output:

1. **JSON Report** (`modreport.json`): Detailed analysis data including:
   - Affected call sites
   - Field state changes
   - Mutation testing results
   - Performance metrics
   - Test coverage information

2. **Visual Chart** (`modreport.png`): Overview visualization showing:
   - Dependency update impact
   - Test coverage quality
   - Performance regression indicators

## License

This project is licensed under the GNU Affero General Public License v3.0 (AGPL-3.0). See the [LICENSE](LICENSE) file for details.

Please [contact us](https://patchlens.com/contact) for commercial licensing and access to premium features.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for legal and license requirements for external contributors.
