# Verus Benchmarks

This directory contains two benchmark suites for evaluating proof synthesis in [Verus](https://github.com/verus-lang/verus), the Rust-based formal verification language.

## Quick Start

```python
import json

# Load VeruSAGE-Bench tasks (repository-level)
verusage_tasks = [json.loads(l) for l in open("VeruSAGE-Bench/tasks.jsonl")]

# Load Verus-Bench tasks (algorithm-level)
verus_tasks = [json.loads(l) for l in open("Verus-Bench/tasks.jsonl")]
```

## Benchmark Comparison

| | **Verus-Bench** | **VeruSAGE-Bench** |
|---|---|---|
| **Tasks** | 150 | 849 |
| **Scope** | Algorithm-level | Repository-level |
| **Focus** | Classic algorithms, loops | Systems verification |
| **Complexity** | Single functions | Multi-file dependencies |
| **Sources** | 4 curated sources | 8 real-world projects |
| **Ground Truth** | Included | Included |
| **Best For** | Basic proof synthesis | Advanced agentic systems |

## Choose Your Benchmark

### 🔹 Verus-Bench (150 tasks)

**Use when**: Evaluating basic proof synthesis, loop invariants, algorithm verification

```
Verus-Bench/
├── CloverBench/    (11 tasks)  - Classic CS examples
├── MBPP/           (78 tasks)  - MBPP problems with specs
├── Diffy/          (38 tasks)  - Array/loop programs
└── Misc/           (23 tasks)  - Tutorial examples
```

Each folder has `unverified/` (input) and `verified/` (ground truth).

👉 **[Verus-Bench README](./Verus-Bench/README.md)**

---

### 🔸 VeruSAGE-Bench (849 tasks)

**Use when**: Evaluating repository-level reasoning, systems verification, agentic frameworks

```
VeruSAGE-Bench/
├── tasks/              (849 tasks)  - All verification tasks (flat)
├── tasks-sampled-100/  (100 tasks)  - Quick evaluation subset
├── tasks-batches/      (8 batches)  - Organized for batch runs
└── source-projects/    (8 projects) - Original verified codebases
```

Tasks come from 9 project categories:
| Prefix | Project | Domain | Tasks |
|--------|---------|--------|-------|
| AL | Anvil | Distributed Systems | 104 |
| AC | Anvil-Advanced | Distributed Systems | 63 |
| IR | IronKV | Distributed Systems | 118 |
| MA | Memory Allocator | Systems | 89 |
| NO | Node Replication | Distributed Systems | 29 |
| NR | NRKernel | OS Kernel | 204 |
| OS | ATMO | OS Kernel | 157 |
| ST | Storage | Systems | 63 |
| VE | Vest | Verification | 22 |

👉 **[VeruSAGE-Bench README](./VeruSAGE-Bench/README.md)**

## Data Format

Both benchmarks provide `tasks.jsonl` for programmatic access:

### Verus-Bench Schema
```json
{
  "task_id": "cloverbench_binary_search",
  "source": "CloverBench",
  "name": "binary_search",
  "task": "...",           // Unverified code (INPUT)
  "ground_truth": "...",   // Verified code (ANSWER)
  "task_path": "CloverBench/unverified/binary_search.rs",
  "solution_path": "CloverBench/verified/binary_search.rs"
}
```

### VeruSAGE-Bench Schema
```json
{
  "task_id": "AL__always_double",
  "project": "AL",
  "project_name": "Anvil",
  "module": "rules",
  "target_function": "always_double",
  "task": "...",           // Unverified code (INPUT)
  "ground_truth": "...",   // Verified code (ANSWER)
  "file_path": "tasks/AL__always_double.rs"
}
```

## Running Verification

```bash
# Verus-Bench
cd Verus-Bench/CloverBench/unverified
verus binary_search.rs

# VeruSAGE-Bench
cd VeruSAGE-Bench/tasks
verus AL__always_double.rs
```

> ⚠️ **Note**: VeruSAGE-Bench Storage (ST) tasks require building dependencies first. See `VeruSAGE-Bench/source-projects/verified-storage/README.md`.

## Directory Structure

```
benchmarks/
├── README.md              # This guide
├── Verus-Bench/           # Algorithm-level benchmark (150 tasks)
│   ├── README.md
│   ├── tasks.jsonl
│   ├── CloverBench/
│   ├── MBPP/
│   ├── Diffy/
│   └── Misc/
└── VeruSAGE-Bench/        # Repository-level benchmark (849 tasks)
    ├── README.md
    ├── tasks.jsonl
    ├── tasks/
    ├── tasks-sampled-100/
    ├── tasks-batches/
    └── source-projects/
```

## Evaluation Metrics

Recommended metrics for both benchmarks:

| Metric | Description |
|--------|-------------|
| **Solve Rate** | % of tasks where Verus verification succeeds |
| **Pass@k** | Success rate with k attempts per task |
| **Verus Runs** | Average verification attempts per task |
| **Time** | Average time per task |
| **Token Usage** | LLM tokens consumed |

## Related Resources

- [Verus Language](https://github.com/verus-lang/verus) - The verification framework
- [Verus Documentation](https://verus-lang.github.io/verus/guide/) - Language guide
- [vstd Library](https://verus-lang.github.io/verus/vstd/) - Standard library docs
