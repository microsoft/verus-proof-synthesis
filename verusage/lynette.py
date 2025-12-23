import os
import re
import subprocess
from pathlib import Path


class Lynette:
    lynette_path = Path(__file__).resolve().parent.parent / "utils" / "lynette" / "source"
    meta_command = ["cargo", "run", "--manifest-path", lynette_path / "Cargo.toml", "--"]
    env = os.environ.copy()
    env["RUSTFLAGS"] = "-Awarnings"

    # Run a command
    # @command: a list of lynette commands arguemnts, e.g. ["compare", "foo.rs", "bar.rs"]
    # @return: a CompletedProcess object(returned by subprocess.run(...))
    def run(self, command):
        command = self.meta_command + command
        return subprocess.run(command, env=self.env, capture_output=True, text=True)

    def code_unimpl(self, file):
        return self.run(["code", "unimpl", file])

    def func_add(self, file1, file2, replace=False, funcs=None):
        if funcs is None:
            funcs = []
        return self.run(
            ["func", "add", file1, file2, "--replace" if replace else ""] + ["--funcs"] + funcs
            if funcs
            else []
        )

    def code_merge(self, file1, file2, merge_mode):
        pass

    def code_merge_all(self, file1, file2):
        return self.run(["code", "merge", "--all", file1, file2])

    def code_merge_invariant(self, file1, file2):
        return self.run(["code", "merge", "--invariants", file1, file2])

    def code_detect_nonlinear(self, file):
        return self.run(["code", "detect-nl", file])

    def code_get_ghost(self, file):
        """Get all ghost code in a verus source code file.

        Returns a CompletedProcess with output format:
        <type>:((<start_line>, <start_column>), (<end_line>, <end_column>))
        """
        return self.run(["code", "get-ghost", file])

    def get_assertions(self, file):
        """Get assertion statements with their line numbers.

        Args:
            file: Path to the Verus source file

        Returns:
            List of dictionaries with assertion information:
            [
                {
                    'type': 'assert' or 'assert_forall',
                    'start_line': int,
                    'start_column': int,
                    'end_line': int,
                    'end_column': int
                },
                ...
            ]
        """
        result = self.code_get_ghost(file)
        if result.returncode != 0:
            return []

        assertions = []
        # Parse output lines like: assert:((32, 20), (32, 42))
        pattern = r"^(assert|assert_forall):\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)$"

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            match = re.match(pattern, line)
            if match:
                assertions.append(
                    {
                        "type": match.group(1),
                        "start_line": int(match.group(2)),
                        "start_column": int(match.group(3)),
                        "end_line": int(match.group(4)),
                        "end_column": int(match.group(5)),
                    }
                )

        return assertions

    def get_all_ghost_code(self, file):
        """Get all ghost code with their line numbers.

        Args:
            file: Path to the Verus source file

        Returns:
            List of dictionaries with ghost code information:
            [
                {
                    'type': str (e.g., 'assert', 'requires', 'ensures', etc.),
                    'start_line': int,
                    'start_column': int,
                    'end_line': int,
                    'end_column': int
                },
                ...
            ]
        """
        result = self.code_get_ghost(file)
        if result.returncode != 0:
            return []

        ghost_items = []
        # Parse output lines like: <type>:((<start_line>, <start_column>), (<end_line>, <end_column>))
        pattern = r"^([^:]+):\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)$"

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            match = re.match(pattern, line)
            if match:
                ghost_items.append(
                    {
                        "type": match.group(1),
                        "start_line": int(match.group(2)),
                        "start_column": int(match.group(3)),
                        "end_line": int(match.group(4)),
                        "end_column": int(match.group(5)),
                    }
                )

        return ghost_items


lynette = Lynette()
