# <img src="assets/logo.png" alt="Project logo" width="40" /> AutoVerus: Verus Proof Synthesis

<p align="left">
    <a href="https://arxiv.org/abs/2409.13082"><img src="https://img.shields.io/badge/arXiv-2409.13082-b31b1b.svg?style=for-the-badge">
    <a href="https://sites.google.com/view/autoverus"><img src="https://img.shields.io/badge/Website-blue.svg?style=for-the-badge">
</p>

![Framework](assets/framework.png)

This repository contains code and artifacts for automated Verus proof synthesis using our AutoVerus approach.

## 📁 Repository Structure

* **`benchmarks/`** - 150 Rust/Verus proof tasks (Verus-Bench) used in evaluation
  * `CloverBench/`, `Diffy/`, `MBPP/`, `Misc/` - Different benchmark suites  
  * See [benchmarks README](benchmarks/README.md) for details
* **`code/`** - Python implementation of AutoVerus proof synthesis
* **`utils/lynette/`** - Verus parser supporting proof synthesis
* **`generated/`** - Pre-generated proof results from our experiments

## 🚀 Quick Start with Docker (Recommended)

**Step 1:** Build and run the Docker container
```bash
docker build -t autoverus .
docker run -it autoverus
```

**Step 2:** Set up your OpenAI API key and run AutoVerus
```bash
export OPENAI_API_KEY=<your-openai-api-key>

# Generate proof for a single file
python main.py --input <input_file.rs> --output <output_file.rs> --config config-artifact-openai.json

# Run on benchmark suite (small sample: 30 tasks)
python verify.py --name gpt4o-ab-sampled --config-file config-artifact-openai.json
```

## 🛠️ Local Installation

### Prerequisites

**System Requirements:**
- Linux (Windows via WSL)
- Internet connection for OpenAI API

**Dependencies:**
1. **Verus** (specific commit required if you want to run on the benchmarks):
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
git clone https://github.com/microsoft/verus-proof-synthesis.git
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
- Use `python main.py -h` for more options

**Output:** 
- Final proof in specified output file
- `intermediate-<timestamp>/` folder with all intermediate files
- Detailed logs showing the proof generation process

## 🔍 Configuration

The tool uses configuration files to set up API credentials and parameters:

- `config.json` - Default configuration **template**
- `config-artifact-openai.json` - OpenAI API configuration
- `config-artifact-azure.json` - Azure OpenAI configuration

Update the configuration file with your API credentials before running.

When running locally, you need to update the paths in the configuration file to point to the correct location of your Verus installation and the example folder.

## 📚 Further Reading

- [Our Paper](https://arxiv.org/abs/2409.13082)
- [Project Website](https://sites.google.com/view/autoverus)
- [Benchmarks README](benchmarks/README.md)
- [Artifact Evaluation](README-artifact-evaluation.md)

## Contributing

This project welcomes contributions and suggestions. Most contributions require you to agree to a Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us the rights to use your contribution. For details, visit https://cla.microsoft.com.

When you submit a pull request, a CLA-bot will automatically determine whether you need to provide a CLA and decorate the PR appropriately (e.g., label, comment). Simply follow the instructions provided by the bot. You will only need to do this once across all repositories using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/). For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

# Trademarks 

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft trademarks or logos is subject to and must follow Microsoft’s Trademark & Brand Guidelines. Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship. Any use of third-party trademarks or logos are subject to those third-party’s policies.

---

## Citation

If you find this work useful, please consider citing:

```bibtex
@article{autoverus,
  title={Autoverus: Automated Proof Generation for Rust Code},
  author={Chenyuan Yang and Xuheng Li and Md Rakib Hossain Misu and Jianan Yao and Weidong Cui and Yeyun Gong and Chris Hawblitzel and Shuvendu K. Lahiri and Jacob R. Lorch and Shuai Lu and Fan Yang and Ziqiao Zhou and Shan Lu},
  journal={Proceedings of the ACM on Programming Languages},
  volume={9},
  number={OOPSLA2},
  year={2025},
  publisher={ACM New York, NY, USA}
}
```