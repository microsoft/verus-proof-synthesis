"""
Use the whole pipeline to verify the problems in the unverified directory.

Usage:
    python verify.py --temp 1.0 --name gpt4o-mbpp --config_file config_cyy.json
"""

import argparse
import re
import subprocess
import time
from datetime import datetime
from pathlib import Path

import rich
from rich.progress import BarColumn, Progress, TaskProgressColumn, TextColumn, TimeRemainingColumn

OUTPUT_DIR = Path("_output")
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

UNVERIFIED = {
    "mbpp": Path(__file__).parent.parent / "benchmarks" / "MBPP" / "unverified",
    "misc": Path(__file__).parent.parent / "benchmarks" / "Misc" / "unverified",
    "diffy": Path(__file__).parent.parent / "benchmarks" / "Diffy" / "unverified",
    "clover": Path(__file__).parent.parent / "benchmarks" / "CloverBench" / "unverified",
    "ab-sampled": Path(__file__).parent.parent / "benchmarks" / "ablation" / "sampled",
    "ab-inference": Path(__file__).parent.parent / "benchmarks" / "ablation" / "inference",
    "ab-refinement": Path(__file__).parent.parent / "benchmarks" / "ablation" / "refinement",
    "ab-repair": Path(__file__).parent.parent / "benchmarks" / "ablation" / "repair",
}

special_words = ["assume(", "admit()"]


def is_correct(code_file_path):
    text = code_file_path.read_text()

    if "safe: false" in text.lower():
        return False

    if "havoc_inline_post" not in code_file_path.name:
        for word in special_words:
            if word in text:
                return False

    score = re.search(r"[Ss]core: \((\d+), (\d+)\)", text)
    if score:
        score = (int(score.group(1)), int(score.group(2)))
        return score[0] > 0 and score[1] == 0
    return False


def install_verusfmt():
    subprocess.run(["cargo", "install", "verusfmt"], check=True)


def run_experiment(
    name,
    unverified_dir,
    temp,
    config_file,
    disable_safe,
    phase1_examples,
    repair_uniform,
    repair_num,
    phase_uniform,
    disable_ranking,
    direct_repair,
    disable_one_refinement,
    is_baseline,
):
    # Get the current date
    date = datetime.now().strftime("%Y%m%d")
    dir_name = OUTPUT_DIR / f"{date}-{name}-{temp}"

    # Create the output directory if it doesn't exist
    dir_name.mkdir(parents=True, exist_ok=True)

    # List all unverified problems
    unverified_problems = [
        file_path for file_path in unverified_dir.iterdir() if file_path.is_file()
    ]
    unverified_problems.sort()

    # Set up the progress bar
    with Progress(
        TextColumn("[bold blue]{task.fields[filename]}", justify="right"),
        BarColumn(),
        TaskProgressColumn(),
        TimeRemainingColumn(),
    ) as progress:
        task = progress.add_task(
            "[green]Processing files...",
            total=3 * len(unverified_problems),
            filename="Starting...",
        )
        correct_problems = set()

        # Loop through 3 iterations
        for i in range(1, 4):
            for file_path in unverified_problems:
                progress.update(task, advance=1, filename=file_path.name)

                if file_path.is_file():
                    if file_path.name in correct_problems:
                        progress.console.log(
                            f"Skipping {file_path.name} Step {i} as it is already verified"
                        )
                        continue
                    output_file = dir_name / f"{i}-{file_path.name}"
                    time_file = output_file.with_suffix(".time")

                    # Check if the output file already exists
                    if output_file.exists():
                        progress.console.log(f"Skipping {file_path.name} Step {i}")
                        if is_correct(output_file):
                            correct_problems.add(file_path.name)
                            progress.console.log(f"{file_path.name} is verified at step {i}")
                        continue

                    progress.console.log(f"Running {file_path.name} Step {i}")

                    # Run the command and time it
                    with open(time_file, "w") as time_f:
                        command = [
                            "python",
                            "main.py",
                            "--temp",
                            temp,
                            "--mode",
                            "gen",
                            "--config",
                            config_file,
                            "--input",
                            str(file_path),
                            "--output",
                            str(output_file),
                            "--repair",
                            str(repair_num),
                            "--phase1-examples",
                            *phase1_examples,
                            "--disable-one-refinement",
                            str(disable_one_refinement),
                        ]
                        if disable_safe:
                            command.append("--disable-safe")
                        if repair_uniform:
                            command.append("--repair-uniform")
                        if phase_uniform:
                            command.append("--phase-uniform")
                        if disable_ranking:
                            command.append("--disable-ranking")
                        if direct_repair:
                            command.append("--direct-repair")
                        if is_baseline:
                            command.append("--is-baseline")

                        # Directly redirect the output to the file
                        subprocess.run(
                            command,
                            stdout=time_f,
                            stderr=subprocess.STDOUT,
                            check=True,
                            encoding="utf-8",
                        )
                        if is_correct(output_file):
                            correct_problems.add(file_path.name)
                            progress.console.log(f"{file_path.name} is verified at step {i}")


def main():
    parser = argparse.ArgumentParser(description="Run experiments with different configurations.")
    parser.add_argument(
        "--temp", type=str, default="1.0", help="Temperature setting for the experiment"
    )
    parser.add_argument("--name", type=str, default="gpt4o-mbpp", help="Name of the experiment")
    parser.add_argument(
        "--config-file",
        type=Path,
        default=Path("config-artifact-azure.json"),
        help="Configuration file for the experiment",
    )
    parser.add_argument("--disable-safe", action="store_true", help="Disable safe check for code")
    parser.add_argument("--repair-uniform", action="store_true", help="Ablation for uniform repair")
    parser.add_argument(
        "--phase1-examples", default=["3", "6", "7"], nargs="+", help="Examples for phase 1"
    )
    parser.add_argument("--repair-num", type=int, default=10, help="Number of repairs")
    parser.add_argument("--phase-uniform", action="store_true", help="Unify the first two phases")
    parser.add_argument("--disable-ranking", action="store_true", help="Disable ranking")
    parser.add_argument("--direct-repair", action="store_true", help="Directly repair the code")
    parser.add_argument(
        "--disable-one-refinement", type=int, default=-1, help="Disable one refinement"
    )
    parser.add_argument(
        "--is-baseline", action="store_true", help="Whether to run in baseline mode"
    )

    args = parser.parse_args()

    # Install verusfmt
    install_verusfmt()

    unverified_dir = None
    for benchmark_name, benchmark_dir in UNVERIFIED.items():
        if benchmark_name in args.name:
            unverified_dir = benchmark_dir
            break
    if unverified_dir is None:
        raise ValueError(f"Unknown benchmark name: {args.name}")

    start_time = time.time()
    # Run the experiment
    run_experiment(
        args.name,
        unverified_dir,
        args.temp,
        args.config_file,
        args.disable_safe,
        args.phase1_examples,
        args.repair_uniform,
        args.repair_num,
        args.phase_uniform,
        args.disable_ranking,
        args.direct_repair,
        args.disable_one_refinement,
        args.is_baseline,
    )

    rich.print(
        f"Experiment {args.name} with temperature {args.temp} finished in {time.time() - start_time:.2f} seconds"
    )


if __name__ == "__main__":
    main()
