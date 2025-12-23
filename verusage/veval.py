import json
import os
import subprocess
import tempfile
from enum import Enum
from time import time

from loguru import logger


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
    ExpectedParentheses = 19
    UnsupportedForBitVector = 20
    CannotProveTermination = 21
    MethodNotFound = 22
    LoopNoDec = 23
    BitVAssertFail = 24
    TerminationFail = 25


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
    "expected `)`": VerusErrorType.ExpectedParentheses,
    "unsupported for bit-vector": VerusErrorType.UnsupportedForBitVector,
    "no method named": VerusErrorType.MethodNotFound,
    "loop must have a decreases clause": VerusErrorType.LoopNoDec,
    "bitvector assertion not satisfied": VerusErrorType.BitVAssertFail,
    "could not prove termination": VerusErrorType.TerminationFail,
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
        self.additional_args = []

    def set_verus_path(self, path):
        self.verus_path = os.path.realpath(path)
        self.vstd_path = os.path.realpath(os.path.join(self.verus_path, "../../../vstd/"))
        # print(f"verus path: {self.verus_path}")
        # print(f"vstd path: {self.vstd_path}")

    def set_additional_args(self, args):
        """Set additional arguments to pass to Verus"""
        self.additional_args = args or []


verus = Verus()


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
        ret = f"{VerusErrorLabel2m[self.label]}\n" if VerusErrorLabel2m[self.label] else ""
        if not snippet or len(self.text) <= pre + post + 1:
            return ret + "\n".join([t.text for t in self.text])
        else:
            return ret + "\n".join(
                [t.text for t in self.text[:pre]] + ["..."] + [t.text for t in self.text[-post:]]
            )

    # TO be refined
    def get_highlights(self):
        return [t.text[t.hl_start - 1 : t.hl_end - 1] for t in self.text]

    def get_lines(self):
        return self.lines


class VerusError:
    def __init__(self, err):
        if err["message"] in m2VerusError:
            self.error = m2VerusError[err["message"]]
        elif err["message"].startswith("no method named"):
            self.error = VerusErrorType.MethodNotFound
        else:
            found = False
            for k in m2VerusError.keys():
                if k in err["message"]:
                    self.error = m2VerusError[k]
                    found = True
            if not found:
                logger.warning(f"Unknown error to fix: {err['message']}")
                self.error = VerusErrorType.Other

        self.message = err["message"]
        self.trace = [ErrorTrace(t) for t in err["spans"]]  # Bottom-up stack trace

        if self.error == VerusErrorType.MethodNotFound:
            self.error_text = err["rendered"]
        else:
            self.error_text = err["message"]
        self.spans = err["spans"] if "spans" in err else []

        # a subtype of precondfail that often requires separate treatment
        if self.error == VerusErrorType.PreCondFail:
            if "i < vec.view().len()" in self.trace[0].get_text():
                self.error = VerusErrorType.PreCondFailVecLen

        # expanded diagnostic information is mostly unavailable
        self.expand_spans = []
        self.expand_trace = []

        # trigger expression
        self.trigger_expr = []

        # Assertion location information from Lynette (to be populated later)
        self.assertion_locations = []  # List of assertion location dicts from Lynette

    def get_text(self, snippet=True, pre=4, post=2, topdown=True):
        # Start with the error message (e.g., "requires not satisfied", "assertion failed")
        result_parts = [f"Error: {self.message}"]

        traces = []
        for t in self.trace:
            t_text = t.get_text(snippet, pre, post)
            if t_text and t_text not in traces:
                traces.append(t_text)

        if topdown:
            traces = traces[::-1]

        if traces:
            result_parts.append("Location:\n" + "\n".join(traces))

        span_texts = []
        for span in self.spans:
            if "text" in span:
                for t in span["text"]:
                    full_line = t["text"]
                    hl_start = t["highlight_start"] - 1  # Convert to 0-indexed
                    hl_end = t["highlight_end"] - 1
                    # Create underline marker (spaces before, carets under highlight)
                    underline = " " * hl_start + "^" * (hl_end - hl_start)
                    span_texts.append(full_line)
                    span_texts.append(underline)
                # Add label if present
                label = span["label"]
                if label:
                    span_texts.append(f"({label})")

        if span_texts:
            result_parts.append("Details:\n  " + "\n  ".join(span_texts))

        return "\n".join(result_parts)

    def get_trace_text(self, snippet=True, pre=4, post=2, topdown=True):
        traces = []
        for t in self.trace:
            t_text = t.get_text(snippet, pre, post)
            if t_text and t_text not in traces:
                traces.append(t_text)

        if topdown:
            traces = traces[::-1]

        return "\n".join(traces)

    # Experimental Feature:
    # Add --expand-errors diagnostic information to a Verus Error
    # this helps if the error in Verus Error is a && clause, and now we can know which exact clause(s) are wrong
    def add_expanded_diagnostic(self, expand_error):
        # We now decide if expand_error is for self, by checking the file name and line-num information

        matched = False

        for self_t in self.trace:
            # We are not sure which trace in self we should match to,
            # so we enumerate every
            # But, if it matches, all traces in expand_error should be in range for that single trace in self
            matched_a_trace = True
            # print(f"Aiming to match File {self_t.fname} Line {self_t.lines[0]}--{self_t.lines[1]}")
            for t in expand_error.trace:
                # print(f"expanded error from File {t.fname} Line {t.lines[0]}--{t.lines[1]}")
                if not t.fname == self_t.fname:
                    matched_a_trace = False
                    break
                if not t.lines[0] >= self_t.lines[0]:
                    matched_a_trace = False
                    break
                if not t.lines[1] <= self_t.lines[1]:
                    matched_a_trace = False
                    break
            if matched_a_trace:
                matched = True
                # print("Found a matching diagnostic expand error information")
                self.expand_spans = expand_error.spans
                self.expand_trace = expand_error.trace
                # print(f"The expand trace now contains:\n {'\n'.join([t.get_text() for t in expand_error.trace])}")
                break
        return matched

    def add_trigger_expression(self, trigger_expr):
        """
        Add the trigger expression to the trigger_expr list
        """
        self.trigger_expr.append(trigger_expr)

    def enrich_with_assertion_locations(self, temp_file_path):
        """
        Use Lynette to get assertion locations for this error and add them to the error object.

        Args:
            temp_file_path: Path to temporary file containing the code being analyzed
        """
        try:
            from lynette import lynette

            # Get all assertions from the file
            all_assertions = lynette.get_assertions(temp_file_path)

            # Find assertions that are within the error trace line ranges
            relevant_assertions = []
            for assertion in all_assertions:
                assertion_line = assertion["start_line"]

                # Check if this assertion is within any of the error trace line ranges
                for trace in self.trace:
                    trace_start, trace_end = trace.lines
                    if trace_start <= assertion_line <= trace_end:
                        relevant_assertions.append(assertion)
                        break

            self.assertion_locations = relevant_assertions

        except Exception as e:
            logger.warning(f"Failed to enrich error with assertion locations: {e}")
            self.assertion_locations = []

    def get_assertion_ranges(self):
        """
        Get the line ranges of all assertions associated with this error.

        Returns:
            List of tuples (start_line, end_line) for each assertion
        """
        ranges = []
        for assertion in self.assertion_locations:
            ranges.append((assertion["start_line"], assertion["end_line"]))
        return ranges

    def contains_assertion_at_line(self, line_number):
        """
        Check if this error contains an assertion at the given line number.

        Args:
            line_number: Line number to check

        Returns:
            bool: True if there's an assertion at this line
        """
        for assertion in self.assertion_locations:
            if assertion["start_line"] <= line_number <= assertion["end_line"]:
                return True
        return False

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, VerusError):
            return False

        return self.error_text == value.error_text and self.get_text() == value.get_text()

    def similar(self, value: object) -> bool:
        if not isinstance(value, VerusError):
            return False

        return self.error_text == value.error_text and self.is_similar_text(
            self.get_trace_text(), value.get_trace_text()
        )

    @staticmethod
    def is_similar_text(trace_text1, trace_text2):
        # Check if trace_text1 and trace_text2 are similar
        # We use the following rules:
        # Find the comment and delete it
        # delete all the spaces and newlines in both trace_text1 and trace_text2
        trace_text1 = VerusError._truncate_by(trace_text1)
        trace_text1 = VerusError._delete_comment(trace_text1).replace(" ", "").replace("\n", "")

        trace_text2 = VerusError._truncate_by(trace_text2)
        trace_text2 = VerusError._delete_comment(trace_text2).replace(" ", "").replace("\n", "")

        return trace_text1 == trace_text2

    @staticmethod
    def _truncate_by(text: str):
        # If the text contains " by ", truncate the text by the first " by "
        if " by " in text:
            text = text.split(" by ")[0] + ";"
        return text

    @staticmethod
    def _delete_comment(text: str):
        # NOTE: This is not a perfect solution
        new_lines = []
        for line in text.splitlines():
            if "//" in line:
                new_lines.append(line.split("//")[0])
            else:
                new_lines.append(line)
        return "\n".join(new_lines)


class EvalScore:
    def __init__(
        self,
        verified: int,
        errors: int,
        compilation_error: bool,
        timeout: bool,
        verus_errors: int = 0,
    ):
        self.compilation_error = compilation_error
        self.verified = verified
        self.errors = errors
        self.timeout = timeout
        if self.verified == self.errors == 0:
            self.compilation_error = True
            self.verified = -1
            self.errors = 999
        self.verus_errors = verus_errors

        # We also need to track the dict {error_type: error_count}
        self.error_type_count = {}
        self.error_type_text = {}

    @staticmethod
    def get_worst_score() -> object:
        return EvalScore(-1, 100, True, False, 100)

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
    def __init__(self, code, logger=logger):
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
        self.timeout = False
        self.rustc_out = ""
        self.verus_out = ""

    def eval_and_get_score(self, max_errs=5, json_mode=True, func_name=None) -> EvalScore:
        self.eval(max_errs, json_mode, func_name)
        return self.get_score()

    def get_score(self) -> EvalScore:
        verified = self.get_verified()
        errors = self.get_errors()
        eval_score = EvalScore(
            verified,
            errors,
            self.compilation_error,
            self.timeout,
            len(self.verus_errors),
        )
        for e in self.verus_errors:
            eval_score.error_type_count[e.error] = eval_score.error_type_count.get(e.error, 0) + 1
            eval_score.error_type_text[e.error] = (
                eval_score.error_type_text.get(e.error, "") + "\n" + e.get_text()
            )
        return eval_score

    # Run verus on the code and parse the output.
    def eval(self, max_errs=5, json_mode=True, func_name=None, expand=False, rlimit=250) -> None:
        with tempfile.NamedTemporaryFile(mode="w", delete=False, encoding="utf-8") as f:
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
        if expand:
            cmd += ["--expand-errors"]

        cmd += ["--rlimit", str(rlimit)]
        # Add additional arguments if provided
        if verus.additional_args:
            cmd.extend(verus.additional_args)
        # self.logger.info(f"Running command: {cmd}")
        try:
            st_time = time()
            m = subprocess.run(cmd, capture_output=True, text=True, timeout=90)
            logger.info(f"Verus took {time() - st_time:.2f} seconds")

            verus_out = m.stdout
            # self.logger.info(f"Stdout: {verus_out}")
            rustc_out = m.stderr
            # self.logger.info(f"Stderr: {rustc_out}")

            self.verus_out = verus_out
            self.rustc_out = rustc_out

            if not json_mode:
                os.unlink(code_path)
                return

            try:
                self.verus_result = json.loads(verus_out)
            except json.JSONDecodeError:
                self.verus_result = None

            # If verus succeed, but rustc failed, then it is a compilation error.
            if self.verus_succeed() and m.returncode != 0:
                self.compilation_error = True

            for rust_err in rustc_out.split("\n")[:-1]:
                try:
                    e = json.loads(rust_err)
                except json.JSONDecodeError:
                    self.logger.warning("Failed to load an error entry in JSON")
                    continue

                if not isinstance(e, dict):
                    self.logger.error(f"Unexpected rust err output: {e}")
                    continue
                self.rustc_result.append(e)

                if "level" in e and e["level"] == "error":
                    if "message" in e and "aborting due to" not in e["message"]:
                        verus_error = VerusError(e)

                        # Enrich with assertion location information using Lynette
                        # Log the assertion locations
                        verus_error.enrich_with_assertion_locations(code_path)

                        self.verus_errors.append(verus_error)
                        # self.logger.warning(f"Verus error: {self.verus_errors[-1].get_text()}")
                elif expand and e["message"].startswith("diagnostics via expansion"):
                    # Experiment feature:
                    # Run verus w/ --expand-errors on the code and parse the output.
                    # Should only be invoked when one of the failing statement contains ``&&''
                    # self.logger.info("Processing an expand error entry now")
                    expand_err = VerusError(e)
                    # self.logger.error(f"Expand error: {expand_err.get_text()}")
                    if len(expand_err.trace) > 0:
                        for verus_error in self.verus_errors:
                            if verus_error.add_expanded_diagnostic(expand_err):
                                self.logger.info(
                                    "Successfully added expand-error information for a verification error"
                                )
                                # The diagnostic expansion should only be for one previously appeared verus error
                                break
                # elif "trigger" in e["message"]:
                #     # We need to log the automatically chosen trigger expressions
                #     self.logger.info("Handling trigger expression")
                #     for verus_error in self.verus_errors:
                #         if verus_error.error == VerusErrorType.AssertFail:
                #             verus_error.add_trigger_expression(e["rendered"])

            # Clean up temporary file after processing all errors
            os.unlink(code_path)

        except subprocess.TimeoutExpired:
            verus_out = None
            rustc_out = None
            self.verus_result = None
            self.compilation_error = False
            self.timeout = True
            self.logger.warning("Killed verification attempt after timer expired")
            # Clean up temporary file in case of timeout
            try:
                os.unlink(code_path)
            except OSError:
                pass  # File might already be deleted

    # Returns the number of verifed functions.
    def get_verified(self) -> int:
        if self.timeout:
            return -1
        if not self.verus_result:
            Exception("No Verus result")
        try:
            verified = self.verus_result["verification-results"]["verified"]
        except Exception as e:
            if self.logger:
                self.logger.error(f"Error: {e}")
            else:
                import sys

                sys.stderr.write(f"Error: {e}\n")
            verified = -1
            self.compilation_error = True
        return verified

    # Returns the number of failed functions.
    def get_errors(self) -> int:
        if self.timeout:
            return 999
        if not self.verus_result:
            Exception("No Verus result")
        try:
            errors = self.verus_result["verification-results"]["errors"]
        except Exception as e:
            if self.logger:
                self.logger.error(f"Error: {e}")
            else:
                import sys

                sys.stderr.write(f"Error: {e}\n")
            errors = 999
            self.compilation_error = True
        return errors

    # Returns True if verus verification succeeded. If the compilation fails, verus also reports success as True,
    # but we consider it as a failure.
    def verus_succeed(self) -> bool:
        if not self.verus_result:
            Exception("No Verus result")
        return self.compilation_error and self.verus_result["verification-results"]["success"]

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
    import argparse
    import sys

    from utils import AttrDict

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
    verus.set_additional_args(getattr(config, "verus_args", []))

    code = open(args.input).read()
    v = VEval(code, logger)
    v.eval()
    print(f"Succeed: {v.verus_succeed()}, Verified: {v.get_verified()}, Errors: {v.get_errors()}")
    print(v.verus_errors[0].error)

    for t in v.get_failures():
        print(t.get_text())

    print("Failure from vstd:")
    for t in v.get_vstd_errors():
        print(t.get_text())
