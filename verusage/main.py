import argparse
import json
import os
import shlex
import time
from pathlib import Path

import loguru
from global_config import GlobalConfig
from veval import verus

import utils
from utils import AttrDict


def main():
    # Parse arguments.
    parser = argparse.ArgumentParser(description="Verus Copilot")
    parser.add_argument("--config", required=True, help="Path to config file")
    parser.add_argument(
        "--mode",
        default="agent",
        help="Mode to run in (gen, repair, mutate, agent, debug)",
    )
    parser.add_argument(
        "--mutrnd",
        default="2",
        help="Rounds of mutation. It usually should NOT be larger than 3.",
    )
    parser.add_argument("--input", default="input.rs", help="Path to input file")
    parser.add_argument("--output", default="output.rs", help="Path to output file")
    parser.add_argument("--outdir", default=".", help="Directory of intermediate output files")
    parser.add_argument("--repair", default=20, type=int, help="Number of repair steps")
    parser.add_argument(
        "--merge", default=5, type=int, help="Number of invariant candidates to merge"
    )
    parser.add_argument(
        "--is-baseline", action="store_true", help="Whether to run in baseline mode"
    )
    parser.add_argument("--temp", default=1.0, type=float, help="The temperature for LLM")
    parser.add_argument("--disable-safe", action="store_true", help="Disable safe check for code")
    parser.add_argument("--repair-uniform", action="store_true", help="Ablation for uniform repair")
    parser.add_argument(
        "--phase1-examples",
        default=["3", "6", "7"],
        nargs="+",
        help="Examples for phase 1",
    )
    parser.add_argument("--phase-uniform", action="store_true", help="Unify the first two phases")
    parser.add_argument("--disable-ranking", action="store_true", help="Disable ranking")
    parser.add_argument("--direct-repair", action="store_true", help="Directly repair the code")
    parser.add_argument(
        "--disable-one-refinement", type=int, default=-1, help="Disable one refinement"
    )
    parser.add_argument("--func_name", default=None, help="The target function to be proved")
    parser.add_argument(
        "--verus-args",
        type=str,
        default="",
        help='Additional arguments to pass to Verus as a single string (e.g., "-L dependency=path --extern=name=path")',
    )
    parser.add_argument(
        "--ablation-mode",
        action="store_true",
        help="Enable ablation mode for repair_assert agent (merges all action prompts into one)",
    )
    parser.add_argument(
        "--tree-search",
        action="store_true",
        help="Enable tree search for repair attempts",
    )
    parser.add_argument(
        "--accept-rule",
        type=str,
        default="default",
        choices=["least", "most", "default"],
        help="Acceptance rule for repair attempts (default: default)",
    )
    parser.add_argument(
        "--swap-case-compute",
        action="store_true",
        help="Enable swapping CASE_ANALYSIS/COMPUTE priority (when CASE_ANALYSIS is primary and COMPUTE is secondary, try COMPUTE first)",
    )

    args = parser.parse_args()

    logger = loguru.logger
    # Check if config file exists
    if not os.path.isfile(args.config):
        logger.error("Config file does not exist")
        return
    config = json.load(open(args.config))
    config = AttrDict(config)

    verus.set_verus_path(config.verus_path)

    # Create temp_dir BEFORE logging setup
    inputfile = Path(args.input)
    inputfname = inputfile.name.replace(".rs", "")
    out_dir = Path(args.outdir)
    temp_dir_name = Path("o-" + inputfname + "-" + time.strftime("%Y%m%d-%H%M%S"))
    temp_dir = out_dir / temp_dir_name
    temp_dir.mkdir(parents=True, exist_ok=True)

    # Initialize global configuration FIRST before creating any components
    logger.info("Initializing global configuration...")
    GlobalConfig.initialize(config, logger, temp_dir)
    logger.info("Global configuration initialized successfully")

    print(f"Temp dir: {temp_dir}")
    # Set log to temp_dir
    logger.add(
        temp_dir / "verus-repair.log",
        rotation="100 MB",
        retention="10 days",
    )

    # Set additional verus arguments globally
    verus_args = []
    if args.verus_args:
        verus_args = shlex.split(args.verus_args)
    verus.set_additional_args(verus_args)

    # Config
    if args.disable_safe:
        logger.warning("Safe check for code is disabled!!!")
        utils.DEBUG_SAFE_CODE_CHANGE = True

    if args.mode == "agent":
        logger.info("Running in agent mode")
        from repair_runner import RepairRunner

        runner = RepairRunner(
            ablation_mode=args.ablation_mode,
            accept_rule=args.accept_rule,
            args=dict(args._get_kwargs()),
        )
    elif args.mode == "debug":
        logger.info("Running in debug mode")
        from repair_runner import RepairRunner

        runner = RepairRunner(
            ablation_mode=args.ablation_mode,
            accept_rule=args.accept_rule,
            args=dict(args._get_kwargs()),
        )
    else:
        logger.error("Invalid mode")
        return

    print(f"Arguments: {args}")
    exit_code = runner.run(args.input, args.output, dict(args._get_kwargs()))
    exit(exit_code)


if __name__ == "__main__":
    main()
