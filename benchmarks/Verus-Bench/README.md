# Verus-Bench

**Verus-Bench** is a benchmark suite for evaluating proof synthesis on algorithm-level verification tasks in [Verus](https://github.com/verus-lang/verus).

## Overview

Verus-Bench contains **150 verification tasks** from four different sources, covering classic algorithms, array programs, and loop invariant synthesis.

### Benchmark Statistics

| Source | Tasks | Description |
|--------|-------|-------------|
| **CloverBench** | 11 | Classic CS examples originally written for Dafny |
| **MBPP** | 78 | Translated from MBPP-DFY-153, problems with formal specifications |
| **Diffy** | 38 | Array and loop verification programs from SV-COMP-2021 |
| **Misc** | 23 | Sorting, searching, and nested loop examples from Verus tutorials |
| **Total** | **150** | |

## Key Features

- **Algorithm-Level Tasks**: Focus on individual functions and algorithms
- **Ground Truth Available**: Each task has a verified solution for reference
- **Multiple Domains**: Array manipulation, sorting, searching, mathematical proofs
- **Self-Contained**: Each task can be verified independently

## Directory Organization

Tasks are organized by source, each containing paired `unverified/` (input) and `verified/` (ground truth) directories:

- `CloverBench/` - 11 classic CS examples
- `MBPP/` - 78 MBPP problems
- `Diffy/` - 38 array/loop programs
- `Misc/` - 23 tutorial examples

## Benchmark Structure

```
Verus-Bench/
├── README.md                    # This file
├── tasks.jsonl                  # All tasks in JSONL format (for ML pipelines)
├── CloverBench/
│   ├── unverified/              # 11 tasks (INPUT)
│   └── verified/                # 11 solutions (GROUND TRUTH)
├── MBPP/
│   ├── unverified/              # 78 tasks
│   └── verified/                # 78 solutions
├── Diffy/
│   ├── unverified/              # 38 tasks
│   └── verified/                # 38 solutions
└── Misc/
    ├── unverified/              # 23 tasks
    └── verified/                # 23 solutions
```

## Data Format (JSONL)

For programmatic access and ML pipelines, we provide `tasks.jsonl` containing all tasks:

```python
import json

# Load all tasks
tasks = [json.loads(line) for line in open("tasks.jsonl")]

# Each task entry contains:
# {
#   "task_id": "cloverbench_binary_search",
#   "source": "CloverBench",
#   "name": "binary_search",
#   "task": "...",           # The unverified code (INPUT)
#   "ground_truth": "...",   # The verified code (EXPECTED ANSWER)
#   "task_path": "CloverBench/unverified/binary_search.rs",
#   "solution_path": "CloverBench/verified/binary_search.rs"
# }

# Filter by source
mbpp_tasks = [t for t in tasks if t["source"] == "MBPP"]
print(f"MBPP tasks: {len(mbpp_tasks)}")
```

### JSONL Schema

| Field | Type | Description |
|-------|------|-------------|
| `task_id` | string | Unique identifier (source_name format) |
| `source` | string | Source benchmark (CloverBench, MBPP, Diffy, Misc) |
| `name` | string | Task name |
| `task` | string | The unverified Rust/Verus code (INPUT) |
| `ground_truth` | string | The verified code with proof annotations (ANSWER) |
| `task_path` | string | Relative path to the unverified .rs file |
| `solution_path` | string | Relative path to the verified .rs file |

## Usage

### Verifying a Single Task

```bash
cd CloverBench/unverified
verus binary_search.rs
```

### Evaluating an LLM Agent

1. Select a task from `tasks.jsonl` or the `unverified/` directories
2. The `task` field contains the unverified code (INPUT)
3. Your system should synthesize proof annotations
4. Verify the solution using Verus
5. Compare against `ground_truth` for reference

## Source Information

| Source | Original Repository | Selection Criteria |
|--------|---------------------|-------------------|
| **CloverBench** | [ChuyueSun/Clover](https://github.com/ChuyueSun/Clover) | From 39 Verus translations, excluded 3 incompatible, 4 with weaker specs, 21 verifiable without annotations |
| **MBPP** | [Mondego/dafny-synthesis](https://github.com/Mondego/dafny-synthesis) | From 153 problems, excluded 67 requiring no annotations, 8 with unsupported features |
| **Diffy** | [SV-COMP-2021](https://figshare.com/articles/code/Diffy_Inductive_Reasoning_of_Array_Programs_using_Difference_Invariants/14509467) | From 69 C programs, excluded 31 requiring non-linear reasoning |
| **Misc** | Verus tutorials/libraries | Curated algorithmic problems and challenging examples |

## Comparison with VeruSAGE-Bench

| Aspect | Verus-Bench | VeruSAGE-Bench |
|--------|-------------|----------------|
| **Tasks** | 150 | 849 |
| **Scope** | Algorithm-level | Repository-level |
| **Complexity** | Single functions | Multi-file dependencies |
| **Domain** | Classic algorithms | Systems verification |
| **Ground Truth** | Included (`verified/`) | In `source-projects/` |

Verus-Bench is suitable for evaluating basic proof synthesis capabilities, while VeruSAGE-Bench tests repository-level reasoning on complex systems code.
