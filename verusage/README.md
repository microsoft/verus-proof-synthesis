# VeruSAGE

**VeruSAGE** is an LLM-powered automated repair framework for [Verus](https://github.com/verus-lang/verus), a verification tool for Rust programs.

## Requirements

- Python 3.8+
- [Verus](https://github.com/verus-lang/verus)

```bash
pip install loguru openai anthropic azure-identity
```

## Quick Start

### 1. Create a Configuration File

Create a `config.json` file:

```json
{
    "aoai_api_base": ["https://api.openai.com/v1/"],
    "aoai_api_key": ["your-api-key-here"],
    "aoai_generation_model": "gpt-4",
    "aoai_debug_model": "gpt-4",
    "verus_path": "/path/to/verus",
    "debug_max_attempt": 3,
    "debug_temp": 1.0,
    "max_token": 8192
}
```

### 2. Run on a Single File

```bash
python main.py --config config.json --input your_file.rs --output repaired_file.rs
```

### 3. Run on a Batch of Files

```bash
python run_batch.py /path/to/input_dir config.json --output-dir results/
```

## Command Line Options

### Single File (`main.py`)

```bash
python main.py --config CONFIG --input INPUT [OPTIONS]
```

| Option | Description | Default |
|--------|-------------|---------|
| `--config` | Path to config JSON file | *Required* |
| `--input` | Path to input Verus file | `input.rs` |
| `--output` | Path to output file | `output.rs` |
| `--repair` | Maximum repair attempts | `20` |
| `--verus-args` | Additional arguments for Verus | `""` |
| `--func_name` | Target function to verify | `None` (all) |

### Batch Processing (`run_batch.py`)

```bash
python run_batch.py INPUT_DIR CONFIG_FILE [OPTIONS]
```

| Option | Description |
|--------|-------------|
| `--output-dir` | Output directory for results |
| `--verus-args` | Additional Verus arguments |
| `--continue-from` | Resume from previous run |

## Exit Codes

| Code | Meaning |
|------|---------|
| `0` | Verification successful |
| `233` | Repair attempted but verification still fails |

## Documentation

For detailed architecture and design, see [ARCHITECTURE.md](ARCHITECTURE.md).
