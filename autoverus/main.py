# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


import argparse
import json
import logging
import os

from veval import verus

import utils
from utils import AttrDict


def main():
    # Parse arguments.
    parser = argparse.ArgumentParser(description="Verus Copilot")
    parser.add_argument("--config", default="config.json", help="Path to config file")
    parser.add_argument("--mode", default="gen", help="Mode to run in (gen, repair)")
    parser.add_argument("--input", default="input.rs", help="Path to input file")
    parser.add_argument("--output", default="output.rs", help="Path to output file")
    parser.add_argument("--repair", default=10, type=int, help="Number of repair steps")
    # The arguments below were designed for ablation study; in most cases, you want to use the default value
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

    args = parser.parse_args()
    # Set log level.
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
    logger = logging.getLogger(__name__)

    # Check if config file exists
    if not os.path.isfile(args.config):
        logger.error("Config file does not exist")
        return

    # Check if input file exists
    if not os.path.isfile(args.input):
        logger.error("Input file does not exist")
        return

    config = json.load(open(args.config))
    config = AttrDict(config)
    verus.set_verus_path(config.verus_path)

    # Config
    if args.disable_safe:
        logger.warning("Safe check for code is disabled!!!")
        utils.DEBUG_SAFE_CODE_CHANGE = True

    logger.info("Phase 1 examples: %s", args.phase1_examples)

    # Run the appropriate mode.
    if args.mode == "gen":
        logger.info("Running in generation mode")
        logger.info("Repair steps: %d", args.repair)
        from generation import Generation

        runner = Generation(
            config,
            logger,
            phase1_examples=args.phase1_examples,
            repair_uniform=args.repair_uniform,
        )
    elif args.mode == "repair":
        logger.info("Running in repair mode")
        logger.info("Repair steps: %d", args.repair)
        from refinement import Refinement

        runner = Refinement(config, logger)
    else:
        logger.error("Invalid mode")
        return

    runner.run(args.input, args.output, args=dict(args._get_kwargs()))


if __name__ == "__main__":
    main()
