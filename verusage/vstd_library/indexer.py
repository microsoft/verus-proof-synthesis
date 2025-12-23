"""
Indexer for vstd library

Builds a searchable index from parsed vstd files.
Index structure enables fast lookup by:
- Function name
- Module
- Data structure type (Seq, Set, Map, etc.)
- Keywords
"""

import json
import logging
from collections import defaultdict
from pathlib import Path

from .parser import VstdFunction, VstdOpenSpec, VstdParser


class VstdIndexer:
    """Builds searchable index from parsed vstd files"""

    def __init__(self, vstd_path: str):
        """Initialize indexer

        Args:
            vstd_path: Path to vstd directory
        """
        self.vstd_path = Path(vstd_path)
        self.parser = VstdParser()
        self.logger = logging.getLogger(__name__)

        # Index structure
        self.index = {
            "functions": {},  # name -> VstdFunction dict
            "open_specs": {},  # name -> VstdOpenSpec dict
            "by_module": {},  # module -> List[function names]
            "by_keyword": {},  # keyword -> List[function names]
            "by_type": {},  # data_type -> {"functions": [], "open_specs": []}
            "callers": {},  # function_name -> List[functions that call it]
        }

        # Statistics
        self.stats = {
            "total_files": 0,
            "total_functions": 0,
            "total_open_specs": 0,
            "functions_by_type": defaultdict(int),
        }

    def build_index(self):
        """Build complete index of vstd library"""
        self.logger.info(f"Building index from: {self.vstd_path}")

        if not self.vstd_path.exists():
            raise ValueError(f"vstd path does not exist: {self.vstd_path}")

        # Parse all files
        parsed_files = self.parser.parse_all_vstd(self.vstd_path)
        self.stats["total_files"] = len(parsed_files)

        # Build index from parsed data
        for file_data in parsed_files:
            self._index_file_data(file_data)

        # Build caller-callee relationships
        self._build_caller_index()

        # Compute statistics
        self._compute_statistics()

        self.logger.info("Index building complete")
        self.logger.info(f"  Total functions: {self.stats['total_functions']}")
        self.logger.info(f"  Total open specs: {self.stats['total_open_specs']}")
        self.logger.info(f"  Modules: {len(self.index['by_module'])}")
        self.logger.info(f"  Keywords: {len(self.index['by_keyword'])}")

    def _index_file_data(self, file_data: dict):
        """Index data from a single parsed file"""
        module = file_data["module"]

        # Index functions
        for func in file_data["functions"]:
            self._index_function(func, module)

        # Index open specs
        for spec in file_data["open_specs"]:
            self._index_open_spec(spec, module)

    def _index_function(self, func: VstdFunction, module: str):
        """Index a single function"""
        # Index by name
        # Handle name collisions by prefixing with module
        full_name = f"{module}::{func.name}"

        # If short name already exists, use full name
        if func.name in self.index["functions"]:
            # Use full name for both
            existing = self.index["functions"][func.name]
            if not existing["name"].startswith(existing["module"]):
                # Update existing to use full name
                old_name = existing["name"]
                existing["name"] = f"{existing['module']}::{old_name}"
            func_dict = func.to_dict()
            func_dict["name"] = full_name
            self.index["functions"][full_name] = func_dict
        else:
            self.index["functions"][func.name] = func.to_dict()

        # Index by module
        if module not in self.index["by_module"]:
            self.index["by_module"][module] = {"functions": [], "open_specs": []}
        self.index["by_module"][module]["functions"].append(func.name)

        # Index by keywords
        for keyword in func.keywords:
            if keyword not in self.index["by_keyword"]:
                self.index["by_keyword"][keyword] = []
            self.index["by_keyword"][keyword].append(func.name)

        # Index by data structure type
        for data_type in ["Seq", "Set", "Map", "Vec", "Multiset", "Array"]:
            if data_type in func.keywords:
                if data_type not in self.index["by_type"]:
                    self.index["by_type"][data_type] = {"functions": [], "open_specs": []}
                self.index["by_type"][data_type]["functions"].append(func.name)

        # Update statistics
        self.stats["total_functions"] += 1
        self.stats["functions_by_type"][func.type] += 1

    def _index_open_spec(self, spec: VstdOpenSpec, module: str):
        """Index a single open spec"""
        # Index by name
        if spec.name in self.index["open_specs"]:
            # Use full name
            full_name = f"{module}::{spec.name}"
            spec_dict = spec.to_dict()
            spec_dict["name"] = full_name
            self.index["open_specs"][full_name] = spec_dict
        else:
            self.index["open_specs"][spec.name] = spec.to_dict()

        # Index by module
        if module not in self.index["by_module"]:
            self.index["by_module"][module] = {"functions": [], "open_specs": []}
        self.index["by_module"][module]["open_specs"].append(spec.name)

        # Index by keywords
        for keyword in spec.keywords:
            if keyword not in self.index["by_keyword"]:
                self.index["by_keyword"][keyword] = []
            self.index["by_keyword"][keyword].append(spec.name)

        # Index by data structure type
        for data_type in ["Seq", "Set", "Map", "Vec", "Multiset", "Array"]:
            if data_type in spec.keywords:
                if data_type not in self.index["by_type"]:
                    self.index["by_type"][data_type] = {"functions": [], "open_specs": []}
                self.index["by_type"][data_type]["open_specs"].append(spec.name)

        # Update statistics
        self.stats["total_open_specs"] += 1

    def _build_caller_index(self):
        """Build caller index from callee information

        For each function, creates a reverse mapping showing which functions call it.
        Uses the 'callees' field from each function to build the 'callers' index.
        """
        self.logger.info("Building caller-callee relationships...")

        # Initialize callers dict for all functions
        for func_name in self.index["functions"]:
            self.index["callers"][func_name] = []

        # Build reverse mapping
        for func_name, func_data in self.index["functions"].items():
            callees = func_data.get("callees", [])

            for callee_name in callees:
                # Try to find the callee in the index
                # The callee might be a short name (e.g., "lemma_foo") or full name (e.g., "vstd::arithmetic::lemma_foo")

                # Try exact match first
                if callee_name in self.index["functions"]:
                    if func_name not in self.index["callers"][callee_name]:
                        self.index["callers"][callee_name].append(func_name)
                else:
                    # Try partial match - look for functions ending with ::callee_name
                    for full_name in self.index["functions"]:
                        if (
                            full_name.endswith("::" + callee_name)
                            or full_name.split("::")[-1] == callee_name
                        ):
                            if full_name not in self.index["callers"]:
                                self.index["callers"][full_name] = []
                            if func_name not in self.index["callers"][full_name]:
                                self.index["callers"][full_name].append(func_name)
                            break

        # Log statistics
        functions_with_callers = sum(1 for callers in self.index["callers"].values() if callers)
        self.logger.info(
            f"  Functions with callers: {functions_with_callers}/{len(self.index['functions'])}"
        )

    def _compute_statistics(self):
        """Compute index statistics"""
        # Already done during indexing
        pass

    def save_index(self, output_path: str):
        """Save index to JSON file

        Args:
            output_path: Path to output JSON file
        """
        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)

        # Create index with metadata
        index_data = {
            "metadata": {
                "vstd_path": str(self.vstd_path),
                "version": "0.1.0",
                "statistics": dict(self.stats),
            },
            "index": self.index,
        }

        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(index_data, f, indent=2)

        self.logger.info(f"Index saved to: {output_file}")
        self.logger.info(f"Index size: {output_file.stat().st_size / 1024 / 1024:.2f} MB")

    def load_index(self, index_path: str):
        """Load pre-built index from JSON file

        Args:
            index_path: Path to index JSON file
        """
        index_file = Path(index_path)

        if not index_file.exists():
            raise FileNotFoundError(f"Index file not found: {index_file}")

        with open(index_file, encoding="utf-8") as f:
            data = json.load(f)

        self.index = data["index"]
        if "metadata" in data:
            self.stats = data["metadata"].get("statistics", {})

        self.logger.info(f"Index loaded from: {index_file}")
        self.logger.info(f"  Total functions: {len(self.index['functions'])}")
        self.logger.info(f"  Total open specs: {len(self.index['open_specs'])}")

    def get_statistics(self) -> dict:
        """Get index statistics

        Returns:
            Dictionary with statistics
        """
        return {
            **self.stats,
            "modules": len(self.index["by_module"]),
            "keywords": len(self.index["by_keyword"]),
            "data_types": len(self.index["by_type"]),
        }

    def search_by_keyword(self, keyword: str) -> list[str]:
        """Search for functions by keyword

        Args:
            keyword: Keyword to search for

        Returns:
            List of function names matching keyword
        """
        return self.index["by_keyword"].get(keyword, [])

    def search_by_type(self, data_type: str) -> dict[str, list[str]]:
        """Search for functions and specs by data structure type

        Args:
            data_type: Data structure type (Seq, Set, Map, etc.)

        Returns:
            Dictionary with "functions" and "open_specs" lists
        """
        return self.index["by_type"].get(data_type, {"functions": [], "open_specs": []})

    def get_function(self, name: str) -> dict:
        """Get function by name

        Args:
            name: Function name

        Returns:
            Function dictionary or None
        """
        return self.index["functions"].get(name)

    def get_open_spec(self, name: str) -> dict:
        """Get open spec by name

        Args:
            name: Open spec name

        Returns:
            Open spec dictionary or None
        """
        return self.index["open_specs"].get(name)


def main():
    """Test indexer"""
    import sys

    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python indexer.py <path-to-vstd-dir>")
        return

    vstd_path = sys.argv[1]
    indexer = VstdIndexer(vstd_path)

    # Build index
    indexer.build_index()

    # Show statistics
    stats = indexer.get_statistics()
    print("\n=== Index Statistics ===")
    for key, value in stats.items():
        print(f"{key}: {value}")

    # Show sample search
    print("\n=== Sample Search: 'Seq' ===")
    seq_results = indexer.search_by_type("Seq")
    print(f"Functions: {len(seq_results['functions'])}")
    print(f"Open specs: {len(seq_results['open_specs'])}")
    print(f"Sample functions: {seq_results['functions'][:5]}")
    print(f"Sample open specs: {seq_results['open_specs'][:5]}")

    # Save index
    output_path = "vstd_index.json"
    indexer.save_index(output_path)
    print(f"\nIndex saved to: {output_path}")


if __name__ == "__main__":
    main()
