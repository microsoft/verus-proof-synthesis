# <img src="assets/logo.png" alt="Project logo" width="40" /> AutoVerus - Artifact Evaluation

![Framework](assets/framework.png)

This repository contains code and artifacts for the paper "**AutoVerus: Automated Proof Generation for Rust Code**". This README guides you through reproducing the experimental results from our paper.

## 📁 Repository Structure

* **`benchmarks/`** - 150 Rust/Verus proof tasks (Verus-Bench) used in our evaluation
  * `CloverBench/` - Clover benchmark tasks  
  * `Diffy/` - Diffy benchmark tasks
  * `MBPP/` - MBPP benchmark tasks  
  * `Misc/` - Miscellaneous benchmark tasks
  * `ablation/` - Tasks for ablation studies
  * See [benchmarks README](benchmarks/README.md) for details
* **`code/`** - Python implementation of AutoVerus proof synthesis
  * See [code README](code/README.md) for details
* **`utils/lynette/`** - Verus parser supporting proof synthesis
* **`generated/`** - Pre-generated proof results
  * `autoverus-generated/` - Results from our AutoVerus approach
  * `baseline-generated/` - Results from baseline LLM approach  
  * `ablation-study/` - Results from ablation experiments

## 🚀 Quick Start (5 minutes)

**Step 1:** Build and run Docker container
```bash
docker build -t autoverus .
docker run -it autoverus /bin/bash
```

**Step 2:** Set up API key and run sample experiment
```bash
cd /home/appuser/verus-proof-synthesis/code
export OPENAI_API_KEY=<your-openai-api-key>

# Quick test on sampled benchmarks
python verify.py --name gpt4o-ab-sampled --config-file config-artifact-openai.json
```

**Expected output:** You should see progress logs and final results showing success rates for different benchmark categories. Results will be saved in `_output/gpt4o-ab-sampled/`.

## Our Generated Results

To avoid re-running the experiments (which can be time-consuming and costly), we provide all pre-generated results from our paper evaluation in the `generated/` directory. These results correspond to the experiments described in Sections 7.1, 7.2, and 7.4 of our paper.

### 📁 Generated Directory Structure

The `generated/` directory is organized into three main categories:

```
generated/
├── autoverus-generated/          # Results from our AutoVerus approach
│   ├── gpt4o-clover-1.0/        # AutoVerus on Clover benchmarks  
│   ├── gpt4o-diffy-1.0/         # AutoVerus on Diffy benchmarks
│   ├── gpt4o-mbpp-1.0/          # AutoVerus on MBPP benchmarks
│   └── gpt4o-misc-1.0/          # AutoVerus on Misc benchmarks
├── baseline-generated/           # Results from baseline LLM approach
│   ├── baseline-clover-1.0/     # Baseline on Clover benchmarks
│   ├── baseline-diffy-1.0/      # Baseline on Diffy benchmarks  
│   ├── baseline-mbpp-1.0/       # Baseline on MBPP benchmarks
│   └── baseline-misc-1.0/       # Baseline on Misc benchmarks
└── abalation-study/             # Results from ablation experiments
    ├── few-shot-ab-inference-without-3-1.0/
    ├── few-shot-ab-inference-without-6-1.0/
    ├── few-shot-ab-inference-without-7-1.0/
    ├── disable-ranking-ab-inference-1.0/
    ├── disable-ranking-ab-refinement-1.0/
    ├── merge-inference-refinement-ab-inference-1.0/
    ├── merge-inference-refinement-ab-refinement-1.0/
    ├── gpt35-ab-sampled-1.0/
    ├── gpt4turbo-ab-sampled-1.0/
    ├── deepseek-ab-sampled-1.0/
    ├── temp-ab-sampled-0.1/
    ├── temp-ab-sampled-0.4/
    ├── temp-ab-sampled-0.7/
    └── all-in-one-ab-repair-1.0/
```

### 📄 Result File Structure

Each experiment directory contains the following files for each benchmark:

```
benchmark-name/
├── 1-benchmark_name.rs          # Final generated proof (if successful)
├── 1-benchmark_name.time        # Execution timing and logging information
└── intermediate-1-benchmark_name/  # All intermediate attempts
    ├── 0-0.rs, 0-1.rs, ..., 1-0.rs, ...    # Phase-1 proof attempts (multiple candidates)
    ├── refine-0.rs, refine-1.rs, ...    # Phase-2 refinement attempts (if needed)
    └── repair/  # Phase-3 repair attempts (if needed)
```

**File Descriptions:**
- **`.rs` files** - Generated Verus proofs at each stage
- **`.time` files** - Detailed logs including execution time, API calls, and error messages
- **`intermediate-*/` folders** - Complete history of all proof generation attempts, organized by phase

### 🔍 How to Use Generated Results

**1. Quick Analysis:**
Browse the final `.rs` files to see successfully generated proofs for each benchmark.
Their verification score is shown in the end of the file.
For instance,
```
// Score: (1, 2)
// Safe: True
```
For the verified proofs, the score should be `(N, 0)` and `Safe: True`.

**2. Detailed Investigation:**
- Check `.time` files for execution statistics and error logs
- Explore `intermediate-*/` folders to see the iterative proof generation process
- Compare different approaches by examining corresponding directories

**3. Reproduce Paper Results:**
The generated results directly support the claims in our paper:
- **Section 7.1 & 7.3** (Overall Results): Compare success rates across `autoverus-generated/` directories
- **Section 7.2** (Baseline Comparison): Compare `autoverus-generated/` vs `baseline-generated/`  
- **Section 7.4** (Ablation Studies): Analyze results in `abalation-study/` directories

**4. Verification:**
All generated correct proofs have been verified by Verus to ensure correctness.

## 🧪 Full Experimental Reproduction

> **⚠️ Important:** 
> - All experiments run inside Docker under `/home/appuser/verus-proof-synthesis/code/`
> - Full reproduction requires time and OpenAI API costs
> - Consider running experiments in parallel or on subsets for faster evaluation

### 📊 Section 7.1: Overall Results

**What it does:** Evaluates AutoVerus on all four benchmark suites to demonstrate overall effectiveness.

```bash
# Run AutoVerus on each benchmark suite
python verify.py --name gpt4o-clover --config-file config-artifact-openai.json
python verify.py --name gpt4o-diffy --config-file config-artifact-openai.json
python verify.py --name gpt4o-mbpp --config-file config-artifact-openai.json
python verify.py --name gpt4o-misc --config-file config-artifact-openai.json
```

### 🔄 Section 7.2: Baseline Comparison

**What it does:** Compares AutoVerus against direct LLM baseline to show the benefit of our approach.

```bash
# Run baseline approach on each benchmark suite
python verify.py --name baseline-clover-simple --is-baseline
python verify.py --name baseline-diffy-simple --is-baseline
python verify.py --name baseline-mbpp-simple --is-baseline
python verify.py --name baseline-misc-simple --is-baseline
```

### 🔬 Section 7.4: Ablation Studies

#### 7.4.1: Phase Analysis

**What it does:** Studies the contribution of different components in our two-phase approach.

**1. Few-shot Example Ablation**
```bash
# Test impact of removing different few-shot examples
python verify.py --name few-shot-ab-inference-without-3 --phase1-examples 6 7 --repair-num 0
python verify.py --name few-shot-ab-inference-without-6 --phase1-examples 3 7 --repair-num 0  
python verify.py --name few-shot-ab-inference-without-7 --phase1-examples 3 6 --repair-num 0
```

**2. Phase Fusion Analysis**
```bash
# Test merging Phase-1 and Phase-2 vs. keeping them separate
python verify.py --name merge-inference-refinement-ab-inference --phase-uniform --repair-num 0
python verify.py --name merge-inference-refinement-ab-refinement --phase-uniform --repair-num 0
```

**3. Ranking Mechanism**
```bash
# Test impact of disabling our ranking mechanism
python verify.py --name disable-ranking-ab-inference --disable-ranking --repair-num 0
python verify.py --name disable-ranking-ab-refinement --disable-ranking --repair-num 0
```

#### 7.4.2: Phase-3 Analysis

**What it does:** Compares our targeted repair approach vs. all-in-one repair strategy.

```bash
# Test all-in-one repair approach
python verify.py --name all-in-one-ab-repair --repair-uniform --direct-repair
```

#### 7.4.3: LLM Model Analysis

**What it does:** Studies impact of different LLM choices and temperature settings.

**1. Different Models**

First, modify `config-artifact-openai.json`:
```json
{
  "aoai_generation_model": "gpt-4-turbo"  // or "gpt-3.5-turbo"
}
```

```bash
# Test different LLM models
python verify.py --name gpt4turbo-ab-sampled --config-file config-artifact-openai.json
python verify.py --name gpt35-ab-sampled --config-file config-artifact-openai.json
```

**2. Temperature Analysis**

Reset config to use `"gpt-4o"`, then:
```bash
# Test different temperature settings
python verify.py --name temp-ab-sampled --temp 0.1 --config-file config-artifact-openai.json
python verify.py --name temp-ab-sampled --temp 0.4 --config-file config-artifact-openai.json  
python verify.py --name temp-ab-sampled --temp 0.7 --config-file config-artifact-openai.json
```

## 🛠️ Running on Your Own Machine

### Prerequisites

**System Requirements:**
- Linux/macOS (Windows via WSL)
- 8GB+ RAM, 20GB+ free disk space
- Internet connection for OpenAI API

**Dependencies:**
1. **Verus** (specific commit required):
   ```bash
   git clone https://github.com/verus-lang/verus.git
   cd verus
   git checkout 33269ac6a0ea33a08109eefe5016c1fdd0ce9fbd
   ./tools/get-z3.sh && source tools/activate
   vargo build --release
   ```

2. **Additional tools:**
   ```bash
   cargo install verusfmt  # Verus formatter
   ```

### Setup

```bash
# Clone repository
git clone <repository-url>
cd verus-proof-synthesis

# Install Python dependencies  
pip install -r requirements.txt

# Set API key
export OPENAI_API_KEY=<your-openai-api-key>
```

### Usage

```bash
cd code
python main.py --input <input_file.rs> --output <output_file.rs> --config <config_file.json>
```

**Key Parameters:**
- `--input` - Input Rust file needing Verus proofs (default: `input.rs`)
- `--output` - Output file with generated proofs (default: `output.rs`)  
- `--config` - Configuration file (default: `config.json`)
- `--repair` - Max debugging rounds (default: 10)

**Output:** 
- Final proof in specified output file
- `intermediate-<timestamp>/` folder with all intermediate files
- Detailed logs showing the proof generation process

## 🚨 Troubleshooting

### Common Issues

**1. OpenAI API Errors**
```
Error: OpenAI API rate limit exceeded
```
**Solution:** Wait and retry, or use multiple API keys in config file.

**2. Verus Path Issues**  
```
Error: Verus binary not found
```
**Solution:** Update `verus_path` in config file to point to your Verus installation.

**3. Memory Issues**
```
Error: Out of memory during proof generation
```
**Solution:** Increase Docker memory limit or run fewer parallel processes.

**4. Docker Build Failures**
```
Error: Package installation failed
```
**Solution:** Ensure stable internet connection and retry `docker build`.

## 📝 Important Notes

- **Non-deterministic Results:** LLM outputs vary between runs; expect ~5-10% variance in success rates
- **API Costs:** Monitor your OpenAI usage during full reproduction
- **Runtime:** Full experiments are time-intensive; plan accordingly
- **Verification:** All generated proofs are automatically verified by Verus
