# VeruSAGE-Bench

**VeruSAGE-Bench** is a comprehensive benchmark suite for evaluating LLM-based agents on repository-level formal verification tasks in [Verus](https://github.com/verus-lang/verus).

## Overview

VeruSAGE-Bench contains **849 verification tasks** extracted from 8 real-world Verus projects, representing challenging proof synthesis problems from systems verification domains including distributed systems, operating systems, storage systems, and more.

### Benchmark Statistics

| Project | Tasks | Domain | Description |
|---------|-------|--------|-------------|
| **AL** (Anvil) | 104 | Distributed Systems | Kubernetes controller verification |
| **AC** (Anvil Advanced) | 63 | Distributed Systems | Advanced Kubernetes controller proofs |
| **IR** (IronKV) | 118 | Distributed Systems | Verified key-value store |
| **MA** (Memory Allocator) | 89 | Systems | Memory allocator verification |
| **NO** (Node Replication) | 29 | Distributed Systems | State machine replication |
| **NR** (NRKernel) | 204 | OS Kernel | Page table and memory management |
| **OS** (ATMO) | 157 | OS Kernel | Microkernel verification |
| **ST** (Storage) | 63 | Systems | Persistent storage verification |
| **VE** (Vest) | 22 | Verification | Serialization/deserialization combinator library |
| **Total** | **849** | | |

## Key Features

- **Real-World Complexity**: Tasks are extracted from production-grade verified systems
- **Repository-Level Context**: Each task requires understanding dependencies originally defined across a large codebase
- **Diverse Difficulty**: Ranges from simple lemmas to complex temporal logic and refinement proofs
- **Comprehensive Feature Coverage**: Tasks collectively cover all the key verification strategies and Verus features
- **Single-file Evaluation**: Eacn task is contained in a stand-alone compilable and verifiable Rust file

## Directory Organization

**Current Structure**: All 849 tasks are in a **flat directory** (`tasks/`) with filenames using project prefixes:
- `AL__*.rs` - 104 Anvil tasks
- `AC__*.rs` - 63 Anvil Advanced tasks  
- `IR__*.rs` - 118 IronKV tasks
- `MA__*.rs` - 89 Memory Allocator tasks
- `NO__*.rs` - 29 Node Replication tasks
- `NR__*.rs` - 204 NRKernel tasks
- `OS__*.rs` - 157 ATMO tasks
- `ST__*.rs` - 63 Storage tasks
- `VE__*.rs` - 22 Vest tasks

## Benchmark Structure

```
VeruSAGE-Bench/
├── README.md                           # This file
├── tasks.jsonl                         # All tasks in JSONL format (for ML pipelines)
├── benchmark-stats.csv                 # Summary statistics
├── source-projects/                    # Original verified projects (9 directories)
│   ├── anvil-library/                  # AL - Anvil library proofs
│   ├── anvil-controller/               # AC - Anvil controller proofs  
│   ├── ironkv/                         # IR - IronKV distributed key-value store
│   ├── memory-allocator/               # MA - Memory allocator verification
│   ├── node-replication/               # NO - Node replication proofs
│   ├── nrkernel/                       # NR - NRKernel page table proofs
│   ├── atmosphere/                     # OS - ATMO microkernel verification
│   ├── storage/                        # ST - Storage system verification
│   └── vest/                           # VE - Vest serialization library
├── tasks/                              # All 849 verification tasks
│   ├── AL__*.rs
│   ├── AC__*.rs
│   ├── IR__*.rs
│   ├── MA__*.rs
│   ├── NO__*.rs
│   ├── NR__*.rs
│   ├── OS__*.rs
│   ├── ST__*.rs
│   └── VE__*.rs
├── tasks-sampled-100/                  # Sampled subset of 100 tasks for quick evaluation
└── tasks-batches/                      # Tasks organized into batches
    ├── batch_001/                      # 100 tasks
    ├── batch_002/                      # 100 tasks
    ├── ...
    └── batch_008/                      # 49 tasks
```

### Source Project Structure

The source-projects folder groups tasks according to their source project.

Each source project directory follows this structure:

```
source-projects/<project>/
├── README.md                           # Project-specific documentation
├── mapping_XX.txt                      # Mapping file (XX = project code: st, nr, ma, etc.)
├── unverified/                         # Unverified task files (INPUT)
│   └── <task_name>.rs                  # The unverified task file
└── verified/                           # Verified solution files (GROUND TRUTH)
    └── <subdirectory>/
        └── <task_name>.rs              # The complete verified solution
```

The ground-truth proof was written by corresponding project developers.

### Mapping Files

Each project contains a `mapping_XX.txt` file that maps unverified task files to their verified counterparts:

```
# Example: mapping_st.txt
append_L_tentatively_append.rs -> verified/log_append/append_L_tentatively_append.rs
inv_L_active_metadata_set_after_crash.rs -> verified/log_inv/inv_L_active_metadata_set_after_crash.rs
...
```

These mapping files ensure consistency between `tasks.jsonl` and the files in source-projects.

## Data Format (JSONL)

For programmatic access and ML pipelines, we provide `tasks.jsonl` containing all 849 tasks. This format aligns with other Verus benchmarks like Verus-Bench.

```python
import json

# Load all tasks
tasks = [json.loads(line) for line in open("tasks.jsonl")]

# Each task entry contains:
# {
#   "task_id": "AL__always_double",
#   "project": "AL",
#   "project_name": "Anvil",
#   "module": "rules",
#   "target_function": "always_double",
#   "task": "use vstd::prelude::*;\n...",        # The unverified code (INPUT)
#   "ground_truth": "use vstd::prelude::*;\n...", # The verified solution (GROUND TRUTH)
#   "file_path": "tasks/AL__always_double.rs"
# }

# Filter by project
nr_tasks = [t for t in tasks if t["project"] == "NR"]
print(f"NRKernel tasks: {len(nr_tasks)}")
```

### JSONL Schema

| Field | Type | Description |
|-------|------|-------------|
| `task_id` | string | Unique identifier (filename without .rs) |
| `project` | string | Project abbreviation (AL, AC, IR, MA, NO, NR, OS, ST, VE) |
| `project_name` | string | Full project name |
| `module` | string | Module path within the project |
| `target_function` | string | The proof function to be synthesized |
| `task` | string | The unverified Rust/Verus code (INPUT). The body of the target function is stripped. |
| `ground_truth` | string | The fully verified Rust/Verus code (REFERENCE). |
| `file_path` | string | Relative path to the .rs file |

## Task Format

Each task is a standalone Rust file containing:
1. **Dependencies**: All necessary imports and type definitions
2. **Context**: Relevant verified functions and lemmas (marked with `#[verifier::external_body]`)
3. **Target**: A single proof function to be verified

### Example Task

```rust
// Task: AL__always_double.rs
use vstd::prelude::*;

verus! {
    // Context: Definitions from the original codebase
    pub struct Execution<T> { ... }
    pub struct TempPred<T> { ... }
    pub open spec fn always<T>(...) -> TempPred<T> { ... }
    
    // External lemmas (dependencies)
    #[verifier::external_body]
    proof fn always_unfold<T>(...) { unimplemented!() }
    
    // Target: Prove this function
    proof fn always_double<T>(ex: Execution<T>, p: TempPred<T>)
        requires always(p).satisfied_by(ex),
        ensures always(always(p)).satisfied_by(ex),
    {
        // Solution to be synthesized
    }
}
```

## Task Naming Convention

Tasks follow the naming pattern: `<PROJECT>__<module>__<submodule>__...__ <function_name>.rs`

- **PROJECT**: Two-letter project abbreviation (AL, AC, IR, MA, NO, NR, OS, ST, VE)
- **Module path**: Double-underscore-separated module hierarchy from the original project
- **Function name**: The target proof function to be verified

Example: `NR__spec_t__mmu__rl2__lemma_step_writenonneg_path_addrs_match.rs`
- Project: NR (NRKernel)
- Module path: `spec_t::mmu::rl2`
- Function: `lemma_step_writenonneg_path_addrs_match`

## Usage

### Verifying a Single Task

```bash
cd tasks
verus <task_file>.rs
```

> ⚠️ **Note for Storage (ST) tasks**: ST tasks require building dependencies first. See `source-projects/verified-storage/README.md` for setup instructions.

### Evaluating an LLM Agent

1. Select tasks from `tasks/` or use the sampled subset in `tasks-sampled-100/`
2. Provide the task file to your LLM agent
3. The agent should synthesize and add Verus proof annotations to the file
4. Verify the solution using Verus
5. A task is considered **solved** if Verus verification succeeds and there is no cheating

### Batch Evaluation

Use the pre-organized batches in `tasks-batches/` for systematic evaluation:

```bash
# Process batch_001 (100 tasks)
for task in tasks-batches/batch_001/*.rs; do
    # Run your agent on $task
    # Verify with: verus --crate-type=lib $task
done
```

## Comparison with Verus-Bench

VeruSage-Bench and **[Verus-Bench](../Verus-Bench/)** have different focus, with VeruSage-Bench focuses on verification in large system projects and Verus-Bench focuses on verification of algorithm examples, such as Fibonacci, binary search, and array operations.

The table below offers a brief comparison between these two benchmark suites based on the verified version of every task.

| Per-task Avg.  | Verus-Bench | VeruSAGEBench |
|----------------|-------------|---------------|
| Total LoC      |  ~30        |  ~950         |
| Spec. LoC      |  ~8         |  ~500         |
| Proof LoC      |  ~10        |  ~50          |
| &nbsp;&nbsp;&nbsp; Loop invariant proof | 8 | 1   |
| &nbsp;&nbsp;&nbsp;  Non-loop-inv. proof | 2 | ~50 |
| \# of loops    | 1.6         | < 0.1         |
| \# of helper lemmas |< 0.1   | 2.4           |

## Source Projects

The benchmark is derived from 8 verified Verus projects spanning distributed systems, OS kernels, and systems infrastructure:

| Project | Prefix | Tasks | Domain | Source Repository |
|---------|--------|-------|--------|-------------------|
| **Anvil** | AL | 104 | Distributed Systems | [anvil-verifier/anvil](https://github.com/anvil-verifier/anvil) |
| **Anvil-Advanced** | AC | 63 | Distributed Systems | [anvil-verifier/anvil](https://github.com/anvil-verifier/anvil) |
| **IronKV** | IR | 118 | Distributed Systems | [verus-lang/verified-ironkv](https://github.com/verus-lang/verified-ironkv) |
| **Memory Allocator** | MA | 89 | Systems | [verus-lang/verified-memory-allocator](https://github.com/verus-lang/verified-memory-allocator) |
| **Node Replication** | NO | 29 | Distributed Systems | [verus-lang/verified-node-replication](https://github.com/verus-lang/verified-node-replication) |
| **NRKernel** | NR | 204 | OS Kernel | [matthias-brun/verified-nrkernel](https://github.com/matthias-brun/verified-nrkernel) |
| **ATMO** | OS | 157 | OS Kernel | [mars-research/atmosphere](https://github.com/mars-research/atmosphere) |
| **Storage** | ST | 63 | Systems | [microsoft/verified-storage](https://github.com/microsoft/verified-storage) |
| **Vest** | VE | 22 | Verification | [secure-foundations/vest](https://github.com/secure-foundations/vest) |

Full source code and extraction details available in `source-projects/` (see individual README.md files).

## Leader Board

TO COME

