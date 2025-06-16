# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


import os
import subprocess
import tempfile
import json
from enum import Enum


class VerusErrorType(Enum):
    PreCondFail = 1
    PostCondFail = 2
    InvFailEnd = 3
    InvFailFront = 4
    DecFailEnd = 5
    DecFailCont = 6
    SplitAssertFail = 7
    SplitPreFail = 8
    SplitPostFail = 9
    RecommendNotMet = 10
    AssertFail = 11
    ArithmeticFlow = 12
    MismatchedType = 13
    PreCondFailVecLen = 14
    Other = 15
    UnxProofBlock = 16
    RustAssert = 17
    ExecinGhost = 18


m2VerusError = {
    "precondition not satisfied": VerusErrorType.PreCondFail,
    "postcondition not satisfied": VerusErrorType.PostCondFail,
    "invariant not satisfied at end of loop body": VerusErrorType.InvFailEnd,
    "invariant not satisfied before loop": VerusErrorType.InvFailFront,
    "decreases not satisfied at end of loop": VerusErrorType.DecFailEnd,
    "decreases not satisfied at continue": VerusErrorType.DecFailCont,
    "split assertion failure": VerusErrorType.SplitAssertFail,
    "split precondition failure": VerusErrorType.SplitPreFail,
    "split postcondition failure": VerusErrorType.SplitPostFail,
    "recommendation not met": VerusErrorType.RecommendNotMet,
    "assertion failed": VerusErrorType.AssertFail,
    "possible arithmetic underflow/overflow": VerusErrorType.ArithmeticFlow,
    "mismatched types": VerusErrorType.MismatchedType,
    "unexpected proof block": VerusErrorType.UnxProofBlock,
    "panic is not supported (if you used Rust's `assert!` macro, you may have meant to use Verus's `assert` function)": VerusErrorType.RustAssert,
    "cannot call function with mode exec": VerusErrorType.ExecinGhost,
}

VerusError2m = {v: k for k, v in m2VerusError.items()}


class VerusErrorLabel(Enum):
    NullLabel = 0
    FailedThisPostCond = 1
    FailedThisPreCond = 2
    RecmdNotMet = 3
    EndOfFunc = 4


m2VerusErrorLabel = {
    None: VerusErrorLabel.NullLabel,
    "failed this postcondition": VerusErrorLabel.FailedThisPostCond,
    "failed precondition": VerusErrorLabel.FailedThisPreCond,
    "recommendation not met": VerusErrorLabel.RecmdNotMet,
    "at the end of the function body": VerusErrorLabel.EndOfFunc,
}

VerusErrorLabel2m = {v: k for k, v in m2VerusErrorLabel.items()}


class Verus:
    def __init__(self):
        self.verus_path = None

    def set_verus_path(self, path):
        self.verus_path = os.path.realpath(path)
        self.vstd_path = os.path.realpath(
            os.path.join(self.verus_path, "../../../vstd/")
        )
        # print(f"verus path: {self.verus_path}")
        # print(f"vstd path: {self.vstd_path}")


verus = Verus()
import shutil
verus.set_verus_path(shutil.which("verus"))

class ErrorText:
    def __init__(self, text):
        self.text = text["text"]
        self.hl_start = text["highlight_start"]
        self.hl_end = text["highlight_end"]


class ErrorTrace:
    def __init__(self, span):
        self.fname = span["file_name"]
        self.lines = (int(span["line_start"]), int(span["line_end"]))
        if span["label"] not in m2VerusErrorLabel:
            self.label = VerusErrorLabel.NullLabel
        else:
            self.label = m2VerusErrorLabel[span["label"]]
        self.text = [ErrorText(t) for t in span["text"]]
        self.vstd_err = self.fname.startswith(os.path.realpath(verus.vstd_path))
        self.strlabel = span["label"]

    def is_vstd_err(self):
        return self.vstd_err

    def get_text(self, snippet=True, pre=4, post=2):
        ret = (
            f"{VerusErrorLabel2m[self.label]}\n"
            if VerusErrorLabel2m[self.label]
            else ""
        )
        if not snippet or len(self.text) <= pre + post + 1:
            return ret + "\n".join([t.text for t in self.text])
        else:
            return ret + "\n".join(
                [t.text for t in self.text[:pre]]
                + ["..."]
                + [t.text for t in self.text[-post:]]
            )

    # TO be refined
    def get_highlights(self):
        return [t.text[t.hl_start - 1 : t.hl_end - 1] for t in self.text]

    def get_lines(self):
        return self.lines


class VerusError:
    def __init__(self, err):
        if err["message"] not in m2VerusError:
            self.error = VerusErrorType.Other
        else:
            self.error = m2VerusError[err["message"]]

        self.trace = [ErrorTrace(t) for t in err["spans"]]  # Bottom-up stack trace
        self.error_text = err["message"]
        self.spans = err["spans"] if "spans" in err else []

        # a subtype of precondfail that often requires separate treatment
        if self.error == VerusErrorType.PreCondFail:
            if "i < vec.view().len()" in self.trace[0].get_text():
                self.error = VerusErrorType.PreCondFailVecLen

    def get_text(self, snippet=True, pre=4, post=2, topdown=True):
        traces = []
        for t in self.trace:
            t_text = t.get_text(snippet, pre, post)
            if t_text and t_text not in traces:
                traces.append(t_text)

        if topdown:
            traces = traces[::-1]

        span_texts = []
        for span in self.spans:
            if "text" in span:
                highlights = []
                for t in span["text"]:
                    text = t["text"][t["highlight_start"] - 1 : t["highlight_end"] - 1]
                    highlights.append(text)
                highlight_text = " ".join(highlights)
                label = span["label"]
                span_texts += [f"{label}: {highlight_text}"]
        return "\n".join(traces) + "\n  " + "\n  ".join(span_texts)

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, VerusError):
            return False

        return (
            self.error_text == value.error_text and self.get_text() == value.get_text()
        )


class EvalScore:
    def __init__(
        self, verified: int, errors: int, compilation_error: bool, verus_errors: int = 0
    ):
        self.compilation_error = compilation_error
        self.verified = verified
        self.errors = errors
        if self.verified == self.errors == 0:
            self.compilation_error = True
            self.verified = -1
            self.errors = 999
        self.verus_errors = verus_errors

    @staticmethod
    def get_worst_score() -> object:
        return EvalScore(-1, 100, True, 100)

    def is_correct(self) -> bool:
        if self.verified < 0:
            return False
        return (
            self.verified > 0
            and self.errors == 0
            and not self.compilation_error
            and self.verus_errors == 0
        )

    def is_good_repair(self, value: object) -> bool:
        # Check whether self is a good repair to value
        if not isinstance(value, EvalScore):
            return False
        if self.compilation_error != value.compilation_error:
            return not self.compilation_error
        return self.verified >= value.verified

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, EvalScore):
            return False
        return (
            self.verified == value.verified
            and self.errors == value.errors
            and self.compilation_error == value.compilation_error
            and self.verus_errors == value.verus_errors
        )

    def __lt__(self, value: object) -> bool:
        if not isinstance(value, EvalScore):
            raise Exception("Invalid comparison")
        if self.compilation_error != value.compilation_error:
            return self.compilation_error
        if self.verified != value.verified:
            return self.verified < value.verified
        if self.errors != value.errors:
            return self.errors > value.errors
        if self.verus_errors != value.verus_errors:
            return self.verus_errors > value.verus_errors
        return False

    def __gt__(self, value: object) -> bool:
        if not isinstance(value, EvalScore):
            raise Exception("Invalid comparison")
        if self.compilation_error != value.compilation_error:
            return not self.compilation_error
        if self.verified != value.verified:
            return self.verified > value.verified
        if self.errors != value.errors:
            return self.errors < value.errors
        if self.verus_errors != value.verus_errors:
            return self.verus_errors < value.verus_errors
        return False

    def __str__(self) -> str:
        return (
            f"Compilation Error: {self.compilation_error},"
            f" Verified: {self.verified},"
            f" Errors: {self.errors},"
            f" Verus Errors: {self.verus_errors}"
        )


class VEval:
    def __init__(self, code, logger=None):
        self.logger = logger
        self.code = code
        # JSON reported by verus, does not include detailed erros(which is reported from rustc)
        self.verus_result = None
        # JSON reported by rustc, including any compliatoin errors and verus verification errors.
        # rustc reports multiple errors in multiple JSON objects to stderr.
        self.rustc_result = []
        # Parsed verus errors. Only verus exclusive errors(as listed in VerusErrorType) are parsed and stored. Compliation/sytanx/other errors are not stored.
        self.verus_errors = []
        self.verus_path = verus.verus_path
        self.compilation_error = False
        self.rustc_out = ""
        self.verus_out = ""

    def eval_and_get_score(
        self, max_errs=5, json_mode=True, func_name=None
    ) -> EvalScore:
        self.eval(max_errs, json_mode, func_name)
        return self.get_score()

    def get_score(self) -> EvalScore:
        verified = self.get_verified()
        errors = self.get_errors()
        return EvalScore(
            verified, errors, self.compilation_error, len(self.verus_errors)
        )

    # Run verus on the code and parse the output.
    def eval(self, max_errs=5, json_mode=True, func_name=None) -> None:
        with tempfile.NamedTemporaryFile(mode="w", delete=False) as f:
            f.write(self.code)
            code_path = f.name
        multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
        err_format = "--output-json --error-format=json" if json_mode else ""
        # cmd = (f"{self.verus_path} {multiple_errors} {err_format} {code_path}").split(" ")
        # Bug fix: code_path may contain white space
        cmd = (f"{self.verus_path} {multiple_errors} {err_format}").split(" ")
        cmd += [code_path]
        if func_name:
            cmd += ["--verify-function", func_name, "--verify-root"]
        # self.logger.info(f"Running command: {cmd}")
        m = subprocess.run(cmd, capture_output=True, text=True)
        verus_out = m.stdout
        rustc_out = m.stderr
        os.unlink(code_path)

        self.verus_out = verus_out
        self.rustc_out = rustc_out

        if not json_mode:
            return

        try:
            self.verus_result = json.loads(verus_out)
        except json.JSONDecodeError as e:
            self.verus_result = None

        # If verus succeed, but rustc failed, then it is a compilation error.
        if self.verus_succeed() and m.returncode != 0:
            self.compilation_error = True

        for rust_err in rustc_out.split("\n")[:-1]:
            try:
                e = json.loads(rust_err)
            except json.JSONDecodeError as e:
                continue
            if not isinstance(e, dict):
                self.logger.error(f"Unexpected rust err output: {e}")
                continue
            self.rustc_result.append(e)
            if "level" in e and e["level"] == "error":
                if "message" in e and "aborting due to" not in e["message"]:
                    self.verus_errors.append(VerusError(e))

    # Returns the number of verifed functions.
    def get_verified(self) -> int:
        if not self.verus_result:
            Exception("No Verus result")
        try:
            verified = self.verus_result["verification-results"]["verified"]
        except Exception as e:
            self.logger.error(f"Error: {e}")
            verified = -1
            self.compilation_error = True
        return verified

    # Returns the number of failed functions.
    def get_errors(self) -> int:
        if not self.verus_result:
            Exception("No Verus result")
        try:
            errors = self.verus_result["verification-results"]["errors"]
        except Exception as e:
            self.logger.error(f"Error: {e}")
            errors = 999
            self.compilation_error = True
        return errors

    # Returns True if verus verification succeeded. If the compilation fails, verus also reports success as True,
    # but we consider it as a failure.
    def verus_succeed(self) -> bool:
        if not self.verus_result:
            Exception("No Verus result")
        return (
            self.compilation_error
            and self.verus_result["verification-results"]["success"]
        )

    def score(self) -> tuple[int, int]:
        return (self.get_verified(), self.get_errors())

    # Returns a list of ErrorTrace for PostCondFail errors
    def get_failed_postconds(self) -> list[ErrorTrace]:
        if not self.verus_result:
            Exception("No Verus result")

        if self.compilation_error:
            return []

        ret = []
        for e in self.verus_errors:
            if e.error == VerusErrorType.PostCondFail:
                for t in e.trace:
                    if t.label == VerusErrorLabel.FailedThisPostCond:
                        ret.append(t)
                        break

        return ret

    def get_failures(self, error_type: VerusErrorType = None) -> list[VerusError]:
        if not self.verus_result:
            Exception("No Verus result")

        # if self.compilation_error:
        #     return []

        ret = []
        for e in self.verus_errors:
            if error_type and e.error == error_type:
                ret.append(e)
            elif error_type is None:
                ret.append(e)
        return ret

    # Returns a list of VerusError if the error is from vstd
    def get_vstd_errors(self):
        if not self.verus_result:
            Exception("No Verus result")

        if self.compilation_error:
            return []

        ret = []
        for e in self.verus_errors:
            for t in e.trace:
                if t.is_vstd_err():
                    ret.append(e)
                    break

        return ret


if __name__ == "__main__":
    import sys
    from utils import AttrDict
    import argparse

    # Parse arguments
    parser = argparse.ArgumentParser(description="Verus Copilot")
    parser.add_argument("--config", default="config.json", help="Path to config file")
    parser.add_argument("--mode", default="gen", help="Mode to run in (gen, refine)")
    parser.add_argument("--input", default="input.rs", help="Path to input file")
    parser.add_argument("--output", default="output.rs", help="Path to output file")
    args = parser.parse_args()

    # Check if config file exists
    if not os.path.isfile(args.config):
        print("Config file does not exist", file=sys.stderr)
        exit(1)

    config = json.load(open(args.config))
    config = AttrDict(config)
    verus.set_verus_path(config.verus_path)

    code = open(args.input).read()
    v = VEval(code)
    v.eval()
    print(
        f"Succeed: {v.verus_succeed()}, Verified: {v.get_verified()}, Errors: {v.get_errors()}"
    )
    print("Failed postconds:")
    for t in v.get_failed_postconds():
        print(t.get_text())
        print(t.get_lines())

    print("Failure from vstd:")
    for t in v.get_vstd_errors():
        print(t.get_text())
