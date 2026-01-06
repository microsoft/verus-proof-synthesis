# Verus Proof Synthesis Leaderboard

A web-based leaderboard for tracking progress in LLM-based formal verification for Rust using Verus.

## 🌐 Live Website

Visit the leaderboard at: **[https://microsoft.github.io/verus-proof-synthesis/](https://microsoft.github.io/verus-proof-synthesis/)**

## 📁 Directory Structure

```
leaderboard/
├── index.html          # Main leaderboard page
├── submit.html         # Submission guidelines
├── about.html          # About page
├── css/
│   └── main.css        # Stylesheet
├── js/
│   └── leaderboard.js  # Interactive functionality
├── data/
│   ├── schema.json                 # JSON schema for submissions
│   ├── verus-bench-results.json    # Verus-Bench leaderboard data
│   └── verusage-bench-results.json # VeruSAGE-Bench leaderboard data
└── README.md           # This file
```

## 🚀 Running Locally

The leaderboard is a static website that can be served by any web server:

```bash
# Using Python
cd leaderboard
python -m http.server 8000
# Visit http://localhost:8000

# Using Node.js (if you have serve installed)
npx serve .

# Using PHP
php -S localhost:8000
```

## 📤 Submitting Results

### Quick Start

1. **Run evaluation** on Verus-Bench or VeruSAGE-Bench
2. **Format results** according to our [JSON schema](data/schema.json)
3. **Open a PR** adding your entry to the appropriate data file

### Submission Format

```json
{
  "submission_id": "your-system-model-version",
  "system_name": "Your System Name",
  "model": "LLM Model Used",
  "date": "YYYY-MM-DD",
  "results": {
    "solved": 135,
    "total": 150,
    "percent_solved": 90.0,
    "avg_time_seconds": 28.5,
    "avg_cost_usd": 0.25
  },
  "breakdown": [
    {"category": "CloverBench", "solved": 11, "total": 11}
  ],
  "paper_url": "https://arxiv.org/abs/...",
  "code_url": "https://github.com/...",
  "verified": false,
  "notes": "Brief description"
}
```

### Required Fields

| Field | Description |
|-------|-------------|
| `submission_id` | Unique identifier (e.g., "mysystem-gpt4-v1.0") |
| `system_name` | Name of your proof synthesis system |
| `model` | LLM model used |
| `date` | Submission date (YYYY-MM-DD) |
| `results.solved` | Number of tasks solved |
| `results.total` | Total tasks attempted |
| `results.percent_solved` | Percentage solved |

### Optional Fields

| Field | Description |
|-------|-------------|
| `results.avg_time_seconds` | Average time per task (Verus-Bench) |
| `results.avg_time_minutes` | Average time per task (VeruSAGE-Bench) |
| `results.avg_cost_usd` | Average cost per task in USD |
| `breakdown` | Per-source/project breakdown |
| `paper_url` | Link to paper |
| `code_url` | Link to code repository |
| `notes` | Additional information |

## ✅ Verification Status

Submissions are labeled with verification status:

- **Verified** — Results independently reproduced by maintainers

To expedite verification, please:
- Provide detailed reproduction instructions
- Make evaluation scripts publicly available
- Include exact Verus version used

## ⚠️ Rules

1. **No cheating**: Submissions using `assume false`, `#[verifier::external_body]`, or other trivial solutions will be rejected
2. **Use standard Verus**: Use the recommended Verus version in benchmark README
3. **Report honestly**: Results should be accurate and reproducible
4. **One entry per configuration**: Submit separate entries for different model/system combinations

## 🛠️ Development

### Modifying the Leaderboard

1. Edit HTML/CSS/JS files as needed
2. Test locally with a web server
3. Submit a PR with your changes

### Adding New Data

To add a new submission:

1. Edit `data/verus-bench-results.json` or `data/verusage-bench-results.json`
2. Add your entry to the `submissions` array
3. Ensure your entry follows the schema in `data/schema.json`
4. Submit a PR

## 📊 Benchmarks

### Verus-Bench (150 tasks)

Algorithm-level verification tasks from classic CS problems.

| Source | Tasks | Description |
|--------|-------|-------------|
| CloverBench | 11 | Classic CS examples |
| MBPP | 78 | Formal specification problems |
| Diffy | 38 | Array/loop programs |
| Misc | 23 | Verus tutorial examples |

### VeruSAGE-Bench (849 tasks)

Repository-level verification tasks from real-world systems.

| Project | Code | Tasks | Domain |
|---------|------|-------|--------|
| Anvil | AL | 104 | Distributed Systems |
| Anvil Advanced | AC | 63 | Distributed Systems |
| IronKV | IR | 118 | Key-Value Store |
| Memory Allocator | MA | 89 | Systems |
| Node Replication | NO | 29 | Distributed Systems |
| NRKernel | NR | 204 | OS Kernel |
| ATMO | OS | 157 | Microkernel |
| Storage | ST | 63 | Storage Systems |
| Vest | VE | 22 | Serialization |

## 📚 Citation

```bibtex
@article{autoverus,
  title={AutoVerus: Automated Proof Generation for Rust Code},
  author={Yang, Chenyuan and Li, Xuheng and Misu, Md Rakib Hossain and others},
  journal={PACMPL},
  volume={9},
  number={OOPSLA2},
  year={2025}
}

@misc{verusage,
  title={VeruSAGE: A Study of Agent-Based Verification for Rust Systems},
  author={Yang, Chenyuan and Neamtu, Natalie and Hawblitzel, Chris and others},
  year={2025},
  eprint={2512.18436},
  archivePrefix={arXiv}
}
```

## 📧 Contact

For questions or issues, please open an issue on the [main repository](https://github.com/microsoft/verus-proof-synthesis/issues).
