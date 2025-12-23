# AutoVerus Source Code Implementation

This directory contains the Python implementation of **AutoVerus**, our automated proof generation system for Rust/Verus code. The system uses a three-phase approach to generate formal proofs for Rust programs.

## 🏗️ Architecture Overview

AutoVerus follows a **three-phase proof synthesis approach**:

1. **Phase-1: Inference** - Generate initial proof candidates using few-shot examples
2. **Phase-2: Refinement** - Refine promising candidates with targeted improvements
3. **Phase-3: Repair** - Debug and fix remaining verification errors

```
Input Rust Code → Phase-1 → Phase-2 → Phase-3 → Verified Proof
                 (Inference) (Refinement) (Repair)
```

## 📁 Core Files Structure

### 🎯 **Entry Points**
- **`main.py`** - Primary entry point for single-file proof generation
- **`verify.py`** - Batch processing and benchmarking tool

### 🧠 **Core Generation Logic**
- **`generation.py`** (942 lines) - **Phase-1 & Phase-2**
  - `direct_inference()` - Basic loop invariant generation
  - `direct_full_inference()` - All-in-one proof generation (baseline)
  - `generate_with_proof_func()` - Main orchestration function
  - Various specialized inference methods for different proof patterns

- **`refinement.py`** (1,450 lines) - **Phase-3**
  - `repair_assertion_error()` - Fix assertion failures
  - `repair_precond_error()` - Fix precondition violations
  - `repair_invfail_front/end()` - Fix loop invariant issues
  - `repair_veval()` - Main repair orchestration
  - Error-specific repair strategies for 15+ Verus error types

### 🔧 **Supporting Components**
- **`infer.py`** - LLM interface and prompt management
- **`veval.py`** - Verus verification and error parsing
- **`utils.py`** - Code manipulation and safety checking utilities
- **`houdini.py`** - Houdini-style predicate inference
- **`lynette.py`** - Interface to Lynette parser for code analysis

### 📚 **Knowledge Base**
- **`examples/`** - Few-shot training examples organized by proof patterns
  - `input/` & `output/` - Core training examples (Phase-1)
  - `input-{category}/` & `output-{category}/` - Specialized examples for different error types
- **`lemmas/`** - Reusable proof lemmas and sequence operations

### ⚙️ **Configuration**
- **`config.json`** - Default configuration file
- **`config-artifact-*.json`** - Artifact evaluation configurations for different LLM providers

## 🔄 Execution Flow

### Single File Generation (`main.py`)
```bash
python main.py --input problem.rs --output solution.rs --config config.json
```

**Flow:**
1. Load input Rust file and configuration
2. **Phase-1:** Generate 5 proof candidates using few-shot examples
3. **Phase-2:** Rank candidates and apply refinement strategies
4. **Phase-3:** Iteratively repair verification errors (up to 10 rounds)
5. Output final verified proof

### Batch Processing (`verify.py`)
```bash
python verify.py --name experiment-name --config-file config.json
```

**Flow:**
1. Load benchmark suite from `../benchmarks/`
2. Process each problem through 3 iterations
3. Track success rates and timing statistics
4. Generate detailed logs and intermediate files

## 🎯 Key Classes and Methods

### `Generation` Class (generation.py)
**Purpose:** Phase-1 & Phase-2 proof candidate generation

**Key Methods:**
- `direct_inference()` - Generate loop invariants using few-shot learning
- `constantrefine_inference()` - Add constant bounds to invariants
- `arrayrefine_inference()` - Handle array access patterns
- `generate_with_proof_func()` - Main orchestration method

### `Refinement` Class (refinement.py)
**Purpose:** Phase-3 repair

**Key Methods:**
- `repair_veval()` - Main repair loop with error classification
- `repair_assertion_error()` - Fix assertion failures with proof blocks
- `repair_invfail_front()` - Fix loop invariant establishment
- `repair_invfail_end()` - Fix loop invariant maintenance

### `VEval` Class (veval.py)
**Purpose:** Verus verification and error analysis

**Key Methods:**
- `eval()` - Run Verus verification on code
- `get_failures()` - Extract and classify verification errors
- `get_score()` - Compute verification score (verified, errors)

## 🔍 Error Classification System

AutoVerus handles **15+ types of Verus errors** with specialized repair strategies:

| Error Type | Repair Strategy | Example |
|------------|----------------|---------|
| `AssertFail` | Add proof blocks with lemma calls | `proof { assert(condition); }` |
| `PreCondFail` | Strengthen preconditions or add checks | `requires i < arr.len()` |
| `InvFailFront` | Fix loop invariant establishment | Add invariant initialization |
| `InvFailEnd` | Fix loop invariant maintenance | Update invariant for loop body |
| `ArithmeticFlow` | Add overflow checks | `requires x < usize::MAX` |
| `MismatchedType` | Fix type casting issues | Convert `int` to `nat` |

## 🛠️ Usage Examples

### Basic Usage
```bash
# Generate proof for a single file
python main.py --input array_sum.rs --output array_sum_proved.rs

# Run baseline comparison
python main.py --input problem.rs --output solution.rs --is-baseline

# Adjust repair rounds
python main.py --input problem.rs --output solution.rs --repair 5
```

### Advanced Configuration
```bash
# Temperature control for LLM creativity
python main.py --input problem.rs --temp 0.7

# Phase ablation studies
python main.py --input problem.rs --phase1-examples 3 6  # Remove example 7
python main.py --input problem.rs --phase-uniform        # Merge Phase-1 & Phase-2
python main.py --input problem.rs --disable-ranking     # Disable candidate ranking
```

### Batch Experiments
```bash
# Run on specific benchmark suite
python verify.py --name gpt4o-mbpp --config-file config-artifact-openai.json

# Ablation studies
python verify.py --name few-shot-ablation --phase1-examples 3 6 --repair-num 0
python verify.py --name repair-ablation --repair-uniform --direct-repair
```

## 🔧 Extension Points

### Adding New Repair Strategies
1. **Identify Error Pattern:** Add new `VerusErrorType` in `veval.py`
2. **Implement Repair Method:** Add `repair_new_error()` in `refinement.py`
3. **Update Error Classifier:** Modify `repair_veval()` to route new errors

### Adding New Inference Patterns
1. **Create Examples:** Add input/output pairs in `examples/input-new/` and `examples/output-new/`
2. **Implement Inference:** Add `new_pattern_inference()` method in `generation.py`
3. **Integrate Pipeline:** Add to `default_refine_funcs` list

### Custom LLM Integration
1. **Update Configuration:** Add new model settings in config files
2. **Modify LLM Interface:** Update `infer.py` to support new API
3. **Test Integration:** Run with `--config custom-config.json`

## 📊 Output Structure

Each run generates:
- **Final proof file** (if successful)
- **Intermediate directory** with all generation attempts:
  - `X-X.rs` - Phase-1 candidates
  - `refine-X.rs` - Phase-2 refinements
  - `repair/*.rs` - Phase-3 repairs
- **Timing logs** with execution statistics and error traces
