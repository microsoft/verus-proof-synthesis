# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


import os
import subprocess
from typing import Literal


class Lynette:
    meta_command = [
        "cargo",
        "run",
        "--manifest-path=../utils/lynette/source/Cargo.toml",
        "--",
    ]
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

    def code_deghost(
        self,
        file,
        output_file,
        deghost_mode: Literal["raw", "unverified"] = "raw",
        run_fmt: bool = True,
    ):
        LYNETTE_PATH = os.environ.get("LYNETTE_PATH")
        if not LYNETTE_PATH:
            raise OSError("LYNETTE_PATH environment variable is not set.")
        command = [LYNETTE_PATH, "code", "deghost", file, "--mode", deghost_mode, "-o", output_file]
        subprocess.run(command)
        if run_fmt:
            subprocess.run(["verusfmt", output_file])


lynette = Lynette()
