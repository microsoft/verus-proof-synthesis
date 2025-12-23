#!/usr/bin/env python3
"""
Build vstd index

One-time script to build the vstd library index.
Run this script whenever the vstd library is updated.

Usage:
    python -m vstd_library.build_index
    python -m vstd_library.build_index --vstd-path /path/to/vstd --output vstd_index.json
"""

import argparse
import logging
import sys
from pathlib import Path

from .indexer import VstdIndexer


def main():
    """Build vstd index from command line"""
    parser = argparse.ArgumentParser(description="Build vstd library index")
    parser.add_argument(
        "--vstd-path", type=str, required=True, help="Path to vstd directory (required)"
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Output path for index JSON (default: vstd_library/vstd_index.json)",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose logging")

    args = parser.parse_args()

    # Setup logging
    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=log_level, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )

    logger = logging.getLogger(__name__)

    # Determine output path
    if args.output:
        output_path = args.output
    else:
        # Default: save in vstd_library directory
        output_path = Path(__file__).parent / "vstd_index.json"

    logger.info("=" * 60)
    logger.info("Building vstd Index")
    logger.info("=" * 60)
    logger.info(f"vstd path: {args.vstd_path}")
    logger.info(f"Output: {output_path}")
    logger.info("")

    # Validate vstd path
    vstd_path = Path(args.vstd_path)
    if not vstd_path.exists():
        logger.error(f"ERROR: vstd path does not exist: {vstd_path}")
        sys.exit(1)

    if not vstd_path.is_dir():
        logger.error(f"ERROR: vstd path is not a directory: {vstd_path}")
        sys.exit(1)

    # Build index
    try:
        indexer = VstdIndexer(str(vstd_path))
        indexer.build_index()

        # Show statistics
        logger.info("")
        logger.info("=" * 60)
        logger.info("Index Statistics")
        logger.info("=" * 60)
        stats = indexer.get_statistics()
        for key, value in sorted(stats.items()):
            if isinstance(value, dict):
                logger.info(f"{key}:")
                for k, v in value.items():
                    logger.info(f"  {k}: {v}")
            else:
                logger.info(f"{key}: {value}")

        # Show sample data
        logger.info("")
        logger.info("=" * 60)
        logger.info("Sample Data")
        logger.info("=" * 60)

        # Seq functions
        seq_data = indexer.search_by_type("Seq")
        logger.info("\nSeq-related content:")
        logger.info(f"  Functions: {len(seq_data['functions'])}")
        logger.info(f"  Open specs: {len(seq_data['open_specs'])}")
        if seq_data["functions"]:
            logger.info(f"  Sample functions: {', '.join(seq_data['functions'][:5])}")
        if seq_data["open_specs"]:
            logger.info(f"  Sample open specs: {', '.join(seq_data['open_specs'][:5])}")

        # Set functions
        set_data = indexer.search_by_type("Set")
        logger.info("\nSet-related content:")
        logger.info(f"  Functions: {len(set_data['functions'])}")
        logger.info(f"  Open specs: {len(set_data['open_specs'])}")

        # Map functions
        map_data = indexer.search_by_type("Map")
        logger.info("\nMap-related content:")
        logger.info(f"  Functions: {len(map_data['functions'])}")
        logger.info(f"  Open specs: {len(map_data['open_specs'])}")

        # Save index
        logger.info("")
        logger.info("=" * 60)
        logger.info("Saving Index")
        logger.info("=" * 60)
        indexer.save_index(str(output_path))

        logger.info("")
        logger.info("=" * 60)
        logger.info("✓ Index built successfully!")
        logger.info("=" * 60)
        logger.info(f"Index saved to: {output_path}")
        logger.info(f"Total functions indexed: {stats['total_functions']}")
        logger.info(f"Total open specs indexed: {stats['total_open_specs']}")
        logger.info("")

        # Validate index can be loaded
        logger.info("Validating index can be loaded...")
        validator = VstdIndexer("")
        validator.load_index(str(output_path))
        logger.info("✓ Index validation passed")

        return 0

    except Exception as e:
        logger.error(f"ERROR: Failed to build index: {e}", exc_info=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
