#!/usr/bin/env python3
import argparse
import concurrent.futures
import glob
import json
import os
import subprocess
import sys
import threading
from pathlib import Path

# Default Configuration
repo_dir = Path(__file__).resolve().parent.parent
DEFAULT_BATCHES_DIR = repo_dir / "benchmarks/verusage-batches"
DEFAULT_CONFIG_FILE = None  # Required, no default
DEFAULT_PROJECT_CSV = repo_dir / "benchmarks/verusage-bench.csv"
DEFAULT_EMAIL_RECIPIENT = "user@example.com"
EMAIL_SENDER = "VeruSAGE <verusage@example.com>"

# Get the directory of this script to locate run_batch.py and config relatively
SCRIPT_DIR = Path(__file__).resolve().parent
RUN_BATCH_SCRIPT = SCRIPT_DIR / "run_batch.py"

# Lock for synchronizing progress updates and console output
progress_lock = threading.Lock()


def send_email(subject, body, recipient):
    """Send an email notification using the mail command."""
    try:
        # Construct the command
        # Use -a to append From header with display name
        cmd = ["mail", "-s", subject, "-a", f"From: {EMAIL_SENDER}", recipient]

        # Run the command with the body as stdin
        process = subprocess.Popen(
            cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        stdout, stderr = process.communicate(input=body)

        if process.returncode != 0:
            with progress_lock:
                print(f"Failed to send email: {stderr}")
        else:
            with progress_lock:
                print(f"Email sent to {recipient}")

    except Exception as e:
        with progress_lock:
            print(f"Error sending email: {e}")


def get_batch_summary(output_dir):
    """Read the summary.log file from the output directory."""
    summary_file = output_dir / "summary.log"
    if not summary_file.exists():
        # Try summary.txt as well, as run_batch.py seems to use summary.txt
        summary_file = output_dir / "summary.txt"
        if not summary_file.exists():
            return "Summary file not found."

    try:
        with open(summary_file) as f:
            return f.read()
    except Exception as e:
        return f"Error reading summary: {e}"


def load_project_totals(csv_path):
    """Load project totals from the CSV file."""
    totals = {}
    if not os.path.exists(csv_path):
        print(f"Warning: Project CSV not found at {csv_path}")
        return totals

    try:
        with open(csv_path) as f:
            lines = f.readlines()
            for line in lines:
                parts = line.strip().split()
                if len(parts) >= 2:
                    prefix = parts[0]
                    # Check if first part is a 2-letter code (or similar) and second is a number
                    if prefix.isupper() and parts[1].isdigit():
                        totals[prefix] = int(parts[1])
    except Exception as e:
        print(f"Error loading project totals: {e}")
    return totals


def update_project_progress(
    output_dir, processed_counts, project_totals, notified_projects, recipient, no_email
):
    """Update progress based on results.json and send notifications if projects complete."""
    results_file = output_dir / "results.json"
    if not results_file.exists():
        return

    try:
        with open(results_file) as f:
            data = json.load(f)

        tasks = data.get("tasks", [])

        # Update counts
        for task in tasks:
            task_name = task.get("file", "")  # run_batch.py uses "file" key
            if not task_name:
                task_name = task.get("task", "")

            # Extract prefix (assume it's the part before the first __)
            if "__" in task_name:
                prefix = task_name.split("__")[0]
                if prefix in project_totals:
                    processed_counts[prefix] = processed_counts.get(prefix, 0) + 1

        # Check for completions
        for prefix, total in project_totals.items():
            current = processed_counts.get(prefix, 0)
            if current >= total and prefix not in notified_projects:
                subject = f"PROJECT COMPLETED: {prefix}"
                body = f"Project {prefix} has completed all {total} tasks.\n\nCurrent Progress:\n"
                for p, t in project_totals.items():
                    c = processed_counts.get(p, 0)
                    pct = (c / t) * 100 if t > 0 else 0
                    body += f"{p}: {c}/{t} ({pct:.1f}%)\n"

                if not no_email:
                    send_email(subject, body, recipient)
                    print(f"Project {prefix} completed! Email sent.")
                else:
                    print(f"Project {prefix} completed! (Email skipped)")

                notified_projects.add(prefix)

    except Exception as e:
        print(f"Error updating project progress: {e}")


def process_batch(
    batch_dir,
    args,
    config_path,
    output_base_dir,
    project_totals,
    processed_counts,
    notified_projects,
):
    batch_name = os.path.basename(batch_dir)

    with progress_lock:
        print(f"Processing {batch_name}...")

    # Run the batch
    try:
        # Create a specific output directory for this batch inside the base output dir
        batch_output_dir = output_base_dir / f"results-{batch_name}"

        cmd = [
            sys.executable,
            args.runner_script,
            batch_dir,
            str(config_path),
            "--output-dir",
            str(batch_output_dir),
        ]

        with progress_lock:
            print(f"Running command for {batch_name}: {' '.join(cmd)}")

        # Run synchronously (in this thread)
        result = subprocess.run(cmd, capture_output=True, text=True)

        # Print stdout/stderr to console safely
        with progress_lock:
            print(f"\n--- Output for {batch_name} ---")
            print(result.stdout)
            if result.stderr:
                print("STDERR:", result.stderr)
            print(f"--- End Output for {batch_name} ---\n")

        if result.returncode != 0:
            with progress_lock:
                print(f"Batch {batch_name} failed with exit code {result.returncode}")
            subject = f"FAILED: VeruSAGE Batch {batch_name}"
            body = f"Batch {batch_name} failed.\n\nStdout:\n{result.stdout}\n\nStderr:\n{result.stderr}"
            if not args.no_email:
                send_email(subject, body, args.email)
        else:
            # Check if output directory exists and has results
            if batch_output_dir.exists():
                summary = get_batch_summary(batch_output_dir)
                subject = f"COMPLETED: VeruSAGE Batch {batch_name}"
                body = f"Batch {batch_name} completed successfully.\n\n{summary}"

                # Update project progress safely
                with progress_lock:
                    update_project_progress(
                        batch_output_dir,
                        processed_counts,
                        project_totals,
                        notified_projects,
                        args.email,
                        args.no_email,
                    )

                if not args.no_email:
                    send_email(subject, body, args.email)
            else:
                subject = f"COMPLETED: VeruSAGE Batch {batch_name} (No output dir)"
                body = f"Batch {batch_name} completed but output directory {batch_output_dir} not found."
                if not args.no_email:
                    send_email(subject, body, args.email)

    except Exception as e:
        with progress_lock:
            print(f"Error running batch {batch_name}: {e}")
        if not args.no_email:
            send_email(
                f"ERROR: VeruSAGE Batch {batch_name}",
                f"An error occurred while running batch {batch_name}: {e}",
                args.email,
            )


def main():
    parser = argparse.ArgumentParser(description="Run Verus repair on all batches.")
    parser.add_argument(
        "--batches-dir",
        default=DEFAULT_BATCHES_DIR,
        help="Directory containing batch subdirectories",
    )
    parser.add_argument("--config", required=True, help="Config file for repair")
    parser.add_argument("--csv", default=DEFAULT_PROJECT_CSV, help="Project CSV file")
    parser.add_argument("--email", default=DEFAULT_EMAIL_RECIPIENT, help="Email recipient")
    parser.add_argument("--no-email", action="store_true", help="Disable email notifications")
    parser.add_argument(
        "--output-base", default="all_batch_results", help="Base output directory for results"
    )
    parser.add_argument(
        "--runner-script", default=str(RUN_BATCH_SCRIPT), help="Path to the batch runner script"
    )
    parser.add_argument(
        "--parallel-batches", type=int, default=1, help="Number of batches to run in parallel"
    )

    args = parser.parse_args()

    # Resolve config path
    config_path = Path(args.config)
    if not config_path.is_absolute():
        config_path = SCRIPT_DIR / config_path

    if not config_path.exists():
        print(f"Error: Config file not found: {config_path}")
        sys.exit(1)

    # Check if batches directory exists
    if not os.path.exists(args.batches_dir):
        print(f"Error: Batches directory not found: {args.batches_dir}")
        sys.exit(1)

    # Determine output directory name with suffix
    config_stem = config_path.stem
    if config_stem.startswith("config_"):
        suffix = "-" + config_stem[7:]
    elif config_stem.startswith("config"):
        suffix = "-" + config_stem[6:]
    else:
        suffix = "-" + config_stem

    # Only append suffix if using the default output base, or if the user wants it always?
    # User request: "For the output, I want to have the same suffix as the config file"
    # I will append it to the output base.
    output_base_name = args.output_base
    if output_base_name == "all_batch_results":  # Only modify if it's the default
        output_base_name = f"{output_base_name}{suffix}"

    print(f"Output directory: {output_base_name}")

    # Load project totals
    project_totals = load_project_totals(args.csv)
    processed_counts = dict.fromkeys(project_totals, 0)
    notified_projects = set()

    print("Project Totals:")
    for p, t in project_totals.items():
        print(f"  {p}: {t}")

    # Get all batch directories
    batch_dirs = sorted(glob.glob(os.path.join(args.batches_dir, "batch_*")))

    if not batch_dirs:
        print(f"No batch directories found in {args.batches_dir}")
        sys.exit(1)

    print(f"Found {len(batch_dirs)} batches to process.")

    # Create base output directory
    output_base_dir = Path(output_base_name)
    output_base_dir.mkdir(parents=True, exist_ok=True)

    # Use ThreadPoolExecutor for parallel execution
    max_workers = args.parallel_batches
    print(f"Running with {max_workers} parallel workers.")

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = []
        for batch_dir in batch_dirs:
            futures.append(
                executor.submit(
                    process_batch,
                    batch_dir,
                    args,
                    config_path,
                    output_base_dir,
                    project_totals,
                    processed_counts,
                    notified_projects,
                )
            )

        # Wait for all futures to complete
        for future in concurrent.futures.as_completed(futures):
            try:
                future.result()
            except Exception as e:
                print(f"An unexpected error occurred in a worker thread: {e}")

    print("\nAll batches processed.")


if __name__ == "__main__":
    main()
