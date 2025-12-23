# Action Debug Script

## Configuration Setup

### Option 1: Use Existing Config Files (Recommended)
The script automatically discovers config files:
```bash
python debug.py  # Interactive mode - will show all config*.json files to choose from
```

### Option 2: Specify Config File
```bash
python debug.py --config path/to/your/config.json
```

### Required Configuration Fields
Your configuration file must include these fields:
```json
{
  "aoai_debug_model": "gpt-4",
  "aoai_model": "gpt-4",
  "aoai_endpoint": "https://your-endpoint.openai.azure.com/",
  "aoai_api_key": "your-api-key-here",
  "aoai_api_version": "2023-05-15",
  "aoai_max_retries": 3,
  "temperature": 1.0,
  "max_tokens": 4096,
  "timeout": 30,
  "example_path": "examples",
  "lemma_path": "lemmas",
  "verus_path": "/path/to/verus",
  "debug_mode": true,
  "verbose": false
}
```

## Usage

### Command-Line Interface

The script uses argparse for professional command-line handling:

```bash
# Get help and see all options
python debug.py --help

# Interactive mode (default when no action specified)
python debug.py                              # Config selection menu
python debug.py --config your_config.json   # Use specific config

# List all available actions (no config needed)
python debug.py --list

# Run sample tests
python debug.py --samples --config your_config.json

# Test specific action
python debug.py --test ACTION --config CONFIG [options]
```

### 1. Interactive Mode (Recommended)

**Default behavior when no action is specified:**

```bash
cd code/agents
python debug.py
```

**With pre-selected config:**
```bash
python debug.py --config your_config.json
```

**Enhanced Interactive Experience**:
1. **Smart Config Handling**: If `--config` provided, uses it directly; otherwise shows config selection menu
2. **Automatic Discovery**: Shows all `config*.json` files found in current directory, project root, and agents directory
3. **Action Selection**: Browse all available actions with descriptions
4. **Flexible Code Input**:
   - Use default sample code
   - Load from file (with smart path resolution)
   - Enter code manually
5. **Real Error Evaluation**: See if candidates actually fix the errors
6. **Detailed Results**: View success rates and error analysis

### 2. List All Actions

```bash
python debug.py --list
```

Shows all available actions with their descriptions, guidance templates, and acceptance criteria.
The output will be in `debug_output` dir.

### 3. Run Sample Tests with Real Errors

```bash
python debug.py --samples --config your_config.json
```

Runs tests using **real VEval** to find actual Verus errors in sample code, then tests actions against those real errors.

### 4. Test Specific Action

```bash
# Basic testing
python debug.py --test add_trigger_assert --config your_config.json

# Test with code from file
python debug.py --test add_trigger_assert --config your_config.json --file my_verus_code.rs

# Get complete output with error evaluation
python debug.py --test type_repair --config your_config.json --file my_code.rs --verbose

# Save detailed results with error analysis
python debug.py --test postcondition_repair --config your_config.json --file example.rs --save

# Full analysis (recommended)
python debug.py --test add_trigger_assert --config your_config.json --file test.rs --verbose --save
```

**Smart Error Handling**: If you forget required arguments, the script provides helpful guidance:

```bash
$ python debug.py --test add_trigger_assert
ERROR: --test requires --config CONFIG_FILE
Available config files:
  1. debug_config.json
  2. production_config.json

Use: python debug.py --test add_trigger_assert --config CONFIG_FILE
```

**File Search Enhancement**: The script intelligently searches for files:
- Exact path as specified
- Relative to current directory
- Relative to project root
- Automatically tries common extensions (.rs, .verus, .txt) if none provided

## Command-Line Options

| Option | Description |
|--------|-------------|
| `--test ACTION` | Test a specific action (e.g., add_trigger_assert, type_repair) |
| `--samples` | Run sample tests with real Verus errors |
| `--list` | List all available actions with descriptions |
| `--config PATH` | Path to configuration file (JSON or Python). Required for most operations |
| `--file PATH` | Load code from specified file (supports .rs, .verus, .txt) |
| `--verbose` | Show detailed execution info and complete candidate outputs |
| `--save` | Save detailed results to debug_output/ directory |
| `--help` | Show help message with examples |

## Error Evaluation Features

### Real-Time Candidate Analysis
For each generated candidate, the script shows:
- ✅ **Original Error Fixed**: Whether the candidate successfully resolves the original error
- 🔢 **New Errors Introduced**: Count of new errors the candidate introduces
- 📊 **Total Errors**: Total number of Verus errors in the candidate
- 🔧 **Compilation Status**: Whether the candidate compiles successfully
- 📝 **Error Details**: Specific error messages (up to 3 shown)

### Status Indicators
- ✅ **SUCCESS**: Fixed original error with no new errors
- ⚠️ **PARTIAL**: Fixed original error but introduced new errors
- ❌ **FAILED**: Original error not fixed

### Example Output with Error Evaluation
```
--- Error Evaluation for Candidate 1 ---
Original Error Fixed: True
New Errors Introduced: 0
Total Errors: 0
Compilation Status: Success
✅ CANDIDATE 1: SUCCESS - Fixed original error with no new errors

--- Error Evaluation for Candidate 2 ---
Original Error Fixed: True
New Errors Introduced: 2
Total Errors: 2
Compilation Status: Success
Error Details:
  1. PostCondFail: postcondition not satisfied
  2. AssertFail: assertion failed
⚠️ CANDIDATE 2: PARTIAL - Fixed original error but introduced 2 new errors
```

## Detailed Output and Logging

### Console Output with `--verbose`
```bash
python debug.py --test add_trigger_assert --config your_config.json --verbose
```
Shows:
- Complete action execution details
- Full candidate outputs (not truncated)
- Detailed error evaluation for each candidate
- Real Azure OpenAI API call information

### Saved Files with `--save`
```bash
python debug.py --test add_trigger_assert --config your_config.json --save
```
Creates files in `debug_output/` directory:
- `{action}_{timestamp}_summary.txt` - Complete test summary with error evaluation statistics
- `{action}_{timestamp}_candidate_1.rs` - Full candidate with error evaluation header
- `{action}_{timestamp}_candidate_2.rs` - Additional candidates with status
- Success rate summary in console output

### Enhanced File Headers
Each saved candidate file includes:
```rust
// Generated by add_trigger_assert
// Candidate 1 of 3
// Timestamp: 20241215_143022
//
// ERROR EVALUATION:
// Original Error Fixed: True
// New Errors Introduced: 0
// Total Errors: 0
// Compilation Status: Success
// STATUS: ✅ SUCCESS - Fixed original error with no new errors
//

// Your actual candidate code here...
```

## Real VEval Integration

The script uses **real Verus evaluation** throughout:

### Code Analysis
- When you provide code (from file or manual input), VEval analyzes it to find real Verus errors
- Uses actual `VerusError` objects with proper error types, locations, and traces
- No more mock or synthetic errors

### Candidate Evaluation
- Each generated candidate is evaluated with VEval
- Compares candidates against original errors using `VerusError.similar()` method
- Provides accurate assessment of whether fixes actually work

### Error Matching
Uses the built-in `VerusError.similar()` method for reliable error comparison based on:
- Error message text
- Trace information
- Proper error classification

## Example Complete Workflow

```bash
# 1. Ensure you have a configuration file
# Create your_config.json with real Azure OpenAI credentials and Verus path

# 2. Interactive testing
python debug.py
# Choose your config file, select action, provide code, see real results

# 3. Command-line testing with full analysis
python debug.py --test add_trigger_assert --config your_config.json --file problematic_code.rs --verbose --save
# Get complete analysis with error evaluation and saved results

# 4. Check results
ls debug_output/
# View saved candidates and summary with error analysis
```

## Built-in Help System

The script includes comprehensive help:

```bash
python debug.py --help
```

Shows:
- Complete usage information
- All available options with descriptions
- Practical examples for each mode
- Configuration requirements

## Troubleshooting

### Common Issues

**"Configuration is required"**: The script requires real Azure OpenAI config
- Solution: Create a config file with real Azure OpenAI credentials

**"No verus_path specified"**: VEval needs to know where Verus is installed
- Solution: Add `"verus_path": "/path/to/verus"` to your config

**"No VerusErrors found"**: The provided code has no Verus verification errors
- Solution: Provide code with actual Verus assertions/specifications that fail

**"Failed to evaluate candidate errors"**: VEval couldn't process a candidate
- Check that Verus is properly installed and accessible
- Verify the candidate code is valid Verus syntax

## Developing New Actions

When developing a new action:

1. Create your action class in the `actions/` directory
2. Register it in `actions/__init__.py`
3. Test during development:
   ```bash
   python debug.py --test your_new_action --config your_config.json --file test_case.rs --verbose
   ```
4. Use the error evaluation to verify your action actually fixes problems
5. Check success rates to optimize your action's effectiveness

The debug script provides immediate feedback on whether your action generates working solutions, making development much more efficient!
