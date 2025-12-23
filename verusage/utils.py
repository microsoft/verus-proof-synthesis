"""
Utilities for Verus Code Repair System

This module contains utility functions for:
- Code formatting and safety checks
- Error processing and analysis
- Type error fixing
- Code transformation and manipulation
- Legacy test utilities
"""

import difflib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from loguru import logger
from lynette import lynette
from veval import VerusError, VEval

# ============================================================================
# CONSTANTS
# ============================================================================

UTIL_PATH = Path(__file__).parent.parent / "utils"

ERROR_RANGE = [
    "in the code before the first loop",
    "in the first loop",
    "in the second loop",
    "in the third loop",
    "in the fourth loop",
    "in the fifth loop",
    "in the last loop and code after",
]

DEBUG_SAFE_CODE_CHANGE = False
ERROR_SUFFIX = " // VERUS_ERROR_HERE"


# ============================================================================
# HELPER CLASSES
# ============================================================================


class AttrDict(dict):
    """Dictionary that allows attribute-style access to keys."""

    def __getattr__(self, name):
        return self[name]


# ============================================================================
# CODE FORMATTING FUNCTIONS
# ============================================================================


def verusfmt_code(code: str) -> str:
    """
    Format code using verusfmt (Verus formatter).

    Args:
        code: Verus source code to format

    Returns:
        Formatted code if successful, original code if formatting fails
    """
    # DEBUG: disable the verusfmt for now due to its bug
    return code
    code_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="verusfmt_", suffix=".rs", encoding="utf-8"
    )
    code_f.write(code)
    code_f.close()

    verusfmt_cmd = ["verusfmt", code_f.name]
    m = subprocess.run(verusfmt_cmd, capture_output=True, text=True)
    if m.returncode == 0:
        logger.info(f"Verusfmt success: {code_f.name}")
        with open(code_f.name, encoding="utf-8") as f:
            code = f.read()
    else:
        logger.error(f"Verusfmt failed: {code_f.name}")
    os.unlink(code_f.name)
    return code


# ============================================================================
# ERROR MARKING FUNCTIONS
# ============================================================================


def remove_error_comment(code: str) -> str:
    """
    Remove ERROR_SUFFIX comment from code.

    Args:
        code: Source code potentially containing error markers

    Returns:
        Code with all error markers removed
    """
    return code.replace(" " + ERROR_SUFFIX, "").replace(ERROR_SUFFIX, "")


def comment_code_with_error(code: str, error: VerusError) -> str:
    """
    Mark error lines in code with ERROR_SUFFIX to make them unique.

    Args:
        code: Source code
        error: VerusError object containing error trace information

    Returns:
        Code with error markers added to relevant lines
    """
    # Get the number of lines of the error code
    error_locations = []
    for trace in error.trace:
        error_locations.append((trace.lines[0], trace.lines[1]))

    lines = code.split("\n")
    # Remove the error suffix from the code
    for i in range(len(lines)):
        if lines[i].strip().endswith(ERROR_SUFFIX):
            lines[i] = lines[i][: -len(ERROR_SUFFIX)]

    # Add the ERROR_SUFFIX to the end of the error lines
    for st, ed in error_locations:
        for i in range(st - 1, ed):
            if lines[i].strip().endswith(ERROR_SUFFIX):
                continue
            lines[i] = lines[i] + ERROR_SUFFIX

    code = "\n".join(lines)
    return code


def remove_comment(code: str) -> str:
    """
    Remove single-line comments from code.

    Args:
        code: Source code with comments

    Returns:
        Code with single-line comments removed
    """
    new_code = ""
    for line in code.split("\n"):
        if line.strip().startswith("//"):
            continue
        new_code += line + "\n"
    return new_code


def parse_json_with_comments(json_text: str) -> dict:
    """
    Parse JSON text that may contain comments (common LLM output issue).

    LLMs sometimes include comments in JSON output which makes it invalid.
    This function strips both single-line (//) and multi-line (/* */) comments
    before parsing.

    Args:
        json_text: JSON string that may contain comments

    Returns:
        Parsed JSON as a dictionary

    Raises:
        json.JSONDecodeError: If the text is not valid JSON even after cleaning

    Example:
        >>> json_str = '{"key": "value" // this is a comment}'
        >>> result = parse_json_with_comments(json_str)
        >>> result
        {'key': 'value'}
    """
    # Strip single-line comments: // ...
    cleaned = re.sub(r"//[^\n]*", "", json_text)

    # Strip multi-line comments: /* ... */
    cleaned = re.sub(r"/\*.*?\*/", "", cleaned, flags=re.DOTALL)

    # Parse the cleaned JSON
    return json.loads(cleaned)


def extract_and_parse_json(text: str) -> dict | None:
    """
    Extract JSON object from text and parse it, handling comments.

    Useful for parsing LLM responses that may have JSON embedded in
    natural language text, and the JSON itself may contain comments.

    Args:
        text: Text that contains a JSON object

    Returns:
        Parsed JSON as a dictionary, or None if no JSON found

    Raises:
        json.JSONDecodeError: If JSON is found but cannot be parsed

    Example:
        >>> text = "Here's the result: {\"status\": \"ok\" // comment}"
        >>> result = extract_and_parse_json(text)
        >>> result
        {'status': 'ok'}
    """

    def _balanced_brace_substring(source: str, start_idx: int) -> str | None:
        """Return the shortest balanced-brace substring beginning at start_idx."""
        depth = 0
        in_string = False
        escape = False
        for idx in range(start_idx, len(source)):
            ch = source[idx]
            if in_string:
                if escape:
                    escape = False
                elif ch == "\\":
                    escape = True
                elif ch == '"':
                    in_string = False
                continue

            if ch == '"':
                in_string = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return source[start_idx : idx + 1]
        return None

    candidates: list[str] = []

    # Prefer fenced ```json blocks since they usually contain the structured output
    fenced_pattern = re.compile(r"```json\s*(\{.*?\})\s*```", re.IGNORECASE | re.DOTALL)
    candidates.extend(match.group(1) for match in fenced_pattern.finditer(text))

    # Fall back to scanning for balanced brace substrings
    if not candidates:
        idx = 0
        while idx < len(text):
            brace_idx = text.find("{", idx)
            if brace_idx == -1:
                break
            substring = _balanced_brace_substring(text, brace_idx)
            if substring:
                candidates.append(substring)
                idx = brace_idx + len(substring)
            else:
                idx = brace_idx + 1

    for candidate in candidates:
        try:
            return parse_json_with_comments(candidate)
        except json.JSONDecodeError:
            continue

    return None


# ============================================================================
# CODE ANALYSIS FUNCTIONS
# ============================================================================


def get_nonlinear_lines(code: str, logger) -> list[tuple[int, int, str]]:
    """
    Get all lines that contain nonlinear arithmetic operations.

    Uses the Lynette tool to detect nonlinear arithmetic in assert and invariant
    expressions.

    Args:
        code: Source code to analyze
        logger: Logger instance

    Returns:
        List of tuples (start_line, end_line, text) for lines with nonlinear arithmetic
    """
    code_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="verus_nonlinear_", suffix=".rs", encoding="utf-8"
    )
    code_f.write(code)
    code_f.close()

    m = lynette.code_detect_nonlinear(code_f.name)
    os.unlink(code_f.name)

    if m.returncode == 0:
        try:
            nl_lines = eval(m.stdout)
            output_lines = []
            code_lines = code.splitlines()
            for ex_type, (st, ed) in nl_lines:
                text = "\n".join(code_lines[st - 1 : ed])
                if ex_type == "assert" and "nonlinear_arith" not in text:
                    # Only return lines not already labeled with nonlinear_arith
                    output_lines.append((st, ed, text))
                elif ex_type == "invariant":
                    output_lines.append((st, ed, text))
            return output_lines
        except json.JSONDecodeError:
            logger.error(f"Error in decoding nonlinear arithmetic operations: {m.stdout}")
            return []
    else:
        return []


# ============================================================================
# CODE SAFETY CHECKING FUNCTIONS
# ============================================================================


def proof_completion_code_change_is_safe(
    origin: str,
    changed: str,
    logger=logger,
    util_path: Path = UTIL_PATH,
    debug: bool = True,
    debuginfo: bool = True,
) -> bool:
    """
    Check if code changes are safe for proof completion.

    Ensures that no admit(), assume(), or verifier attributes are added/removed.
    Uses Lynette to verify changes don't violate safety rules.

    Args:
        origin: Original source code
        changed: Modified source code
        logger: Logger instance
        util_path: Path to utility tools
        debug: If True, can skip checks in DEBUG_SAFE_CODE_CHANGE mode
        debuginfo: If True, log detailed error information

    Returns:
        True if changes are safe, False otherwise
    """
    if debug and DEBUG_SAFE_CODE_CHANGE:
        logger.warning("Debug mode is on, skip code change checking")
        return True

    # Check the number of admit(), assume(, #[verifier::external_body]
    # They should not be increased
    if origin.count("admit()") != changed.count("admit()"):
        logger.error("admit() calls have been added or removed")
        return False
    if origin.count("assume(") != changed.count("assume("):
        logger.error("assume(...) calls have been added or removed")
        return False
    if origin.count("#[verifier::external_body]") != changed.count("#[verifier::external_body]"):
        logger.error("#[verifier::external_body] annotations have been added or removed")
        return False
    if origin.count("#[verifier::admit]") != changed.count("#[verifier::admit]"):
        logger.error("#[verifier::admit] annotations have been added or removed")
        return False

    st_time = time.time()
    orig_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_orig", suffix=".rs", encoding="utf-8"
    )
    orig_f.write(origin)
    orig_f.close()

    changed_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_changed", suffix=".rs", encoding="utf-8"
    )
    changed_f.write(changed)
    changed_f.close()

    exepath = util_path / "lynette/source/target/debug/lynette.exe"

    if os.path.exists(exepath):
        verus_additions_cmd = [exepath, "additions", orig_f.name, changed_f.name]
    else:
        cargopath = util_path / "lynette/source/Cargo.toml"

        verus_additions_cmd = [
            "cargo",
            "run",
            "--manifest-path",
            str(cargopath),
            "--",
            "additions",
        ] + [orig_f.name, changed_f.name]

    logger.info(f"Run: {verus_additions_cmd} ")
    m = subprocess.run(verus_additions_cmd, capture_output=True, text=True)
    logger.info(f"Safe check took {time.time() - st_time:.2f} seconds")

    os.unlink(orig_f.name)
    os.unlink(changed_f.name)

    if m.returncode == 0:
        return True
    elif m.returncode == 1:
        err_m = m.stdout.strip()
        # lynette safety check could output more information than just `Disallowed changes detected'
        if "Disallowed changes detected" in err_m:
            logger.error("Disallowed changes detected by lynette")
            return False
        else:
            logger.error("Unknown errors during lynette safety check")
            if debuginfo:
                logger.error("Error in comparing code changes\n")
            return False
    else:
        err_m = m.stderr.strip()
        logger.error("Unknown errors during lynette safety check")
        logger.error(f"{err_m}")
        if "unwrap()" in err_m:
            if debuginfo:
                logger.error("Error in comparing code changes\n")
            return False

    return False


def code_change_is_safe(
    origin: str,
    changed: str,
    verus_path=None,
    logger=logger,
    target_mode: bool = True,
    util_path: Path = UTIL_PATH,
    inter: bool = False,
    debug: bool = True,
    debuginfo: bool = True,
) -> bool:
    """
    Check if code changes are safe using Lynette tool.

    Args:
        origin: Original source code
        changed: Modified source code
        verus_path: Path to Verus (unused, kept for backward compatibility)
        logger: Logger instance
        target_mode: If True, use target mode checking
        util_path: Path to utility tools
        inter: If True, use asserts-anno mode
        debug: If True, can skip checks in DEBUG_SAFE_CODE_CHANGE mode
        debuginfo: If True, log detailed error information

    Returns:
        True if changes are safe, False otherwise
    """
    if debug and DEBUG_SAFE_CODE_CHANGE:
        logger.warning("Debug mode is on, skip code change checking")
        return True

    orig_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_orig", suffix=".rs", encoding="utf-8"
    )
    orig_f.write(origin)
    orig_f.close()

    changed_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_changed", suffix=".rs", encoding="utf-8"
    )
    changed_f.write(changed)
    changed_f.close()

    cargopath = util_path / "lynette/source/Cargo.toml"

    opts = []
    if inter:
        opts = ["--asserts-anno"]
    elif target_mode:
        opts = ["-t"]

    verus_compare_cmd = (
        ["cargo", "run", "--manifest-path", str(cargopath), "--", "compare"]
        + opts
        + [orig_f.name, changed_f.name]
    )

    m = subprocess.run(verus_compare_cmd, capture_output=True, text=True)

    os.unlink(orig_f.name)
    os.unlink(changed_f.name)

    if m.returncode == 0:
        return True
    elif m.returncode == 1:
        err_m = m.stdout.strip()
        if err_m == "Files are different":
            return False
        else:
            if debuginfo:
                logger.error("Error in comparing code changes\n")
            return False
    else:
        err_m = m.stderr.strip()
        if "unwrap()" in err_m:
            if debuginfo:
                logger.error("Error in comparing code changes\n")
            return False

    return False


# ============================================================================
# CODE EXTRACTION & MANIPULATION FUNCTIONS
# ============================================================================


def get_func_body(code: str, fname: str, util_path: Path = UTIL_PATH) -> str:
    """
    Extract function body from code using Lynette.

    Args:
        code: Source code containing the function
        fname: Function name to extract
        util_path: Path to utility tools

    Returns:
        Function body as string, or empty string if extraction fails
    """
    orig_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="verus_copilot_", suffix=".rs", encoding="utf-8"
    )
    orig_f.write(code)
    orig_f.close()

    cargopath = util_path / "lynette/source/Cargo.toml"

    lynette_extract_cmd = [
        "cargo",
        "run",
        "--manifest-path",
        str(cargopath),
        "--",
        "func",
        "extract",
        "-b",
        "-f",
        fname,
        orig_f.name,
    ]

    m = subprocess.run(lynette_extract_cmd, capture_output=True, text=True)
    os.unlink(orig_f.name)

    if m.returncode == 0:
        return m.stdout.strip()
    return ""


def check_changed_code_v2(origin: str, changed: str) -> bool:
    """
    Check if changes are only in invariant, assert, requires/ensures blocks.

    Args:
        origin: Original source code
        changed: Modified source code

    Returns:
        True if all changes are in safe locations, False otherwise
    """
    diff = list(difflib.ndiff(origin.splitlines(), changed.splitlines()))
    diff = [x for x in diff if not x.startswith("?") and x[1:].strip()]
    safe_lines = []
    # invariant
    safe = False
    use_parentheses = False
    for i, d in enumerate(diff):
        if not safe:
            if d[1:].strip().startswith("invariant"):
                safe = True
                indent = len(d[1:]) - len(d[1:].lstrip())
                next_indent = len(diff[i + 1][1:]) - len(diff[i + 1][1:].lstrip())
                if next_indent <= indent:
                    use_parentheses = True
        else:
            new_indent = len(d[1:]) - len(d[1:].lstrip())
            if not use_parentheses and new_indent <= indent:
                safe = False
            if use_parentheses and d[1:].strip() == "{":
                safe = False
        if safe:
            safe_lines.append(i)

    # assert
    for i, d in enumerate(diff):
        if d[1:].strip().startswith("assert"):
            safe_lines.append(i)

    # require/ensure
    safe = False
    use_parentheses = False
    for i, d in enumerate(diff):
        if safe:
            new_indent = len(d[1:]) - len(d[1:].lstrip())
            if not use_parentheses and new_indent <= indent:
                safe = False
            if use_parentheses and d[1:].strip() == "{":
                safe = False
        # ensures have same indent with requires
        if not safe:
            if d[1:].strip().startswith("requires") or d[1:].strip().startswith("ensures"):
                safe = True
                indent = len(d[1:]) - len(d[1:].lstrip())
                next_indent = len(diff[i + 1][1:]) - len(diff[i + 1][1:].lstrip())
                if next_indent <= indent:
                    use_parentheses = True
        if safe:
            safe_lines.append(i)

    # new functions
    safe = False
    for i, d in enumerate(diff):
        if not safe:
            if (d.startswith("-") or d.startswith("+")) and "fn " in d[1:].strip():
                safe = True
                safe_lines.append(i)
        else:
            safe_lines.append(i)
            if (d.startswith("-") or d.startswith("+")) and d[1:].strip() == "}":
                safe = False

    for i, d in enumerate(diff):
        if d.startswith("-") or d.startswith("+"):
            if i not in safe_lines:
                return False
    return True


def check_syntaxerr_inv(code: str) -> bool:
    """
    Check if the generated invariants have wrong syntax.

    Args:
        code: Source code to check

    Returns:
        True if syntax errors found, False otherwise
    """
    codelines = code.split("\n")
    for i, line in enumerate(codelines):
        sline = line.strip()
        if sline.startswith("invariant"):
            if sline.endswith(";"):
                return True
            elif sline.endswith("["):
                return True
            elif codelines[i + 1].strip().startswith("["):
                return True
    return False


# ============================================================================
# LOOP HANDLING & ERROR SPLITTING FUNCTIONS (Legacy - mainly used in tests)
# ============================================================================


def split_code_by_loop(code: str) -> list[int]:
    intervals = [1]
    for i, line in enumerate(code.split("\n")):
        if re.match(r"(while|for)(\(| )", line.strip()) and not line.strip().startswith("for all"):
            intervals.append(i + 1)
    intervals.append(len(code.split("\n")) + 1)
    return intervals


def split_origin_error_by_interval(error, intervals):
    if len(intervals) <= 3:  # less than two loops
        return [error]
    new_error = [""] * (
        len(intervals) - 1
    )  # before fist loop (mostly spec), first loop, second loop, ..., last loop and after
    cur_error = ""
    idx = -1
    error_lines = error.split("\n")
    for i, line in enumerate(error_lines):
        if line.startswith("error") and "aborting due to" not in line:
            new_error[idx] += cur_error
            cur_error = line + "\n"
            line_num = int(re.findall(r":(\d+):", error_lines[i + 1])[0])
            for i, interval in enumerate(intervals):
                if line_num < interval:
                    idx = i - 1
                    break
        else:
            cur_error += line + "\n"
    new_error[idx] += cur_error
    return new_error


def count_origin_error_by_interval(error, intervals):
    if len(intervals) <= 3:  # less than two loops
        cnt = 0
        for line in error.split("\n"):
            if line.startswith("error") and "aborting due to" not in line:
                cnt += 1
        return [cnt]
    error_cnt = [0] * (
        len(intervals) - 1
    )  # before fist loop (mostly spec), first loop, second loop, ..., last loop and after
    idx = -1
    error_lines = error.split("\n")
    for i, line in enumerate(error_lines):
        if line.startswith("error") and "aborting due to" not in line:
            line_num = int(re.findall(r":(\d+):", error_lines[i + 1])[0])
            for i, interval in enumerate(intervals):
                if line_num < interval:
                    idx = i - 1
                    error_cnt[idx] += 1
                    break
    return error_cnt


def compare_and_choose_by_loop(code1, code2, m1, m2):
    int1 = split_code_by_loop(code1)
    int2 = split_code_by_loop(code2)
    if len(int1) != len(int2):
        return code1
    e1 = count_origin_error_by_interval(m1, int1)
    e2 = count_origin_error_by_interval(m2, int2)
    if len(e1) == 1:
        if e1[0] >= e2[0]:
            return code2
        return code1
    code = ""
    for i, (c1, c2) in enumerate(zip(e1, e2)):
        if c1 >= c2:
            st, ed = int2[i], int2[i + 1]
            for line_id in range(st, ed):
                code += code2.split("\n")[line_id - 1] + "\n"
        else:
            st, ed = int1[i], int1[i + 1]
            for line_id in range(st, ed):
                code += code1.split("\n")[line_id - 1] + "\n"
    return code


# ============================================================================
# VERIFICATION & EVALUATION FUNCTIONS
# ============================================================================


def evaluate(
    code: str, verus_path: str, func_name: str | None = None
) -> tuple[tuple[int, int], subprocess.CompletedProcess]:
    fn = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_eval", suffix=".rs", encoding="utf-8"
    )
    fn.write(code)
    fn.close()

    commands = [verus_path, fn.name]
    if func_name:
        commands += ["--verify-function", func_name, "--verify-root"]
    m = subprocess.run(commands, capture_output=True, text=True)
    temp = 0
    chunks = m.stderr.split("\n\n")
    for ch in chunks:
        if ch.startswith("error") and "aborting due to" not in ch:
            temp += 1
    try:
        score = re.findall(r"(\d+) verified, (\d+) errors", m.stdout)[0]
    except IndexError:
        score = (0, max(1, temp))
    if score[0] == "0" and score[1] == "0":
        score = (0, temp)
    score = (int(score[0]), max(int(score[1]), temp))
    return score, m


def proved_by_verus(code, verus_path):
    # TODO: is this correct?
    score, msg = evaluate(code, verus_path)
    if score[1] == 0:
        print("Verus succeeded!!")
        return True
    else:
        return False


def choose_best(codes, verus_path):
    best_score = (-1, 100)
    for code in codes:
        score, _ = evaluate(code, verus_path)
        if score[0] > best_score[0] or (score[0] == best_score[0] and score[1] < best_score[1]):
            best_score = score
            best_code = code
    return best_code


def compress_nl_assertion(code: str) -> str:
    """
    Compress nonlinear arithmetic assertions into single lines.

    Args:
        code: Source code with nonlinear arithmetic assertions

    Returns:
        Code with compressed nonlinear assertions
    """
    lines = code.split("\n")
    inside = False
    tmp_line = ""
    new_code = ""
    for line in lines:
        if not inside:
            if line.strip().startswith("assert") and "by" in line and "nonlinear_arith" in line:
                inside = True
                tmp_line += line
            else:
                new_code += line + "\n"
        else:
            if "{}" in line:
                tmp_line += " " + line.strip() + "\n"
                inside = False
                new_code += tmp_line
                tmp_line = ""
            else:
                tmp_line += " " + line.strip()
    return new_code


# ============================================================================
# PROOF ANNOTATION REMOVAL FUNCTIONS
# ============================================================================


def get_invariant_lines(code: str) -> list[int]:
    """
    return the total number of invariant lines in a code
    TODO: can be improved by a parser-based impl
    """
    lines = []

    invariants = False

    for index, line in enumerate(code.split("\n")):
        if invariants:
            if line.strip().startswith("{"):
                invariants = False
            else:
                lines.append(index)
        else:
            if line.strip().startswith("invariant"):
                invariants = True

    return lines


def get_assert_lines(code):
    """
    return the total number of assert lines in a code
    TODO: can be improved by a parser-based impl
    """
    lines = []

    for index, line in enumerate(code.split("\n")):
        if "assert(" in line or "assert (" in line:
            if not line.strip().startswith("//"):
                lines.append(index)

    return lines


def remove_redundant_loopinv(code):
    """
    remove redundant loop invariants in code
    here, redundant only means same-string-content if comments are not considered
    """
    new_code = ""
    invariants = False
    invariantlist = []
    for line in code.split("\n"):
        remove = False
        if invariants:
            if line.strip().startswith("{"):
                invariants = False
            else:
                thisinv = re.sub(r"//.*", "", line).strip()
                for inv in invariantlist:
                    if thisinv == inv:
                        remove = True
                if not remove:
                    invariantlist.append(thisinv)
        else:
            if line.strip().startswith("invariant"):
                invariantlist = []
                invariants = True
        if not remove:
            new_code += line + "\n"
    return new_code


def comment_out_a_line(code, line):
    """
    comment out the line-th line from code
    """
    lines = code.split("\n")
    oldline = lines[line]
    lines[line] = "// // // _comment_out_" + oldline
    return "\n".join(lines), oldline


def remove_unnecessary_lines(code, logger, util_path, candidates=None, correctproof=True):
    """
    Given a program, code, that Verus can (correctproof-True) or cannot (correctproof-False) verify.
    going through the ghost-code line numbers in candidates array.
    check one by one to see if any of them can be removed without hurting the verification.

    this function only goes through candidates array once. the caller may decide to call this function multiple times until it converges

    return: the resulting code, the number of unnecessary annotations identified
    """
    if candidates is None:
        candidates = []
    veval = VEval(code, logger)
    score = veval.eval_and_get_score()
    if correctproof and not score.is_correct():
        return code, 0

    if len(candidates) == 0:
        return code, 0

    if "// // // _comment_out_" in code:
        return code, 0

    changed = 0
    workingset = candidates

    veval = VEval(code)
    veval.eval()
    old_failures = veval.get_failures()

    for line_num in workingset:
        new_code, oldline = comment_out_a_line(code, line_num)
        if not code_change_is_safe(
            code, new_code, "", logger, util_path=util_path, debuginfo=False
        ):
            continue
        # debug
        # print("Trying to remove line {}: {}".format(l, oldline))
        veval = VEval(new_code)
        score = veval.eval_and_get_score()
        new_failures = veval.get_failures()
        if score.is_correct():
            sys.stderr.write(f"Unnecessary proof annotation @ Line-{line_num}: {oldline}\n")
            changed = changed + 1
            code = new_code
            continue
        if correctproof and not score.is_correct():
            continue
        # Now, we need to check if the new failures are the same as the old ones

        # print(f"{len(old_failures)} old failures: ")
        # print(f"{len(new_failures)} new failures: ")
        if len(old_failures) != len(new_failures):
            continue

        sameimperfectly = True
        for i, ofail in enumerate(old_failures):
            if not ofail.similar(new_failures[i]):
                sameimperfectly = False
                break

        if sameimperfectly:
            sys.stderr.write(f"Unnecessary proof annotation @ Line-{line_num}: {oldline}\n")
            changed = changed + 1
            code = new_code

    if changed > 0:
        lines = code.split("\n")
        code = "\n".join([x for x in lines if not x.startswith("// // // _comment_out_")])

    return code, changed


def remove_unnecessary_annotation(code, logger, util_path, an_type="assert", correctproof=True):
    """
    remove loop invariants or assert that are unnecessary for Verus proof
    correctproof (True): this function only works for code that Verus can already prove
    correctproof (False): this function works for code that Verus cannot yet prove
    """
    veval = VEval(code, logger)
    score = veval.eval_and_get_score()
    if correctproof and not score.is_correct():
        return code, -1

    changed = True
    changed_num = 0
    rnd = 0
    maxround = 10

    while changed and rnd < maxround:
        changed = False
        if an_type == "inv":
            lines = get_invariant_lines(code)
        elif an_type == "assert":
            lines = get_assert_lines(code)
        else:
            lines = []
        if len(lines) == 0:
            break
        code, changed_inc = remove_unnecessary_lines(
            code, logger, util_path, candidates=lines, correctproof=correctproof
        )
        changed_num += changed_inc
        if changed_inc > 0:
            changed = True
        rnd = rnd + 1

    return code, changed_num


def remove_redundant_req(code, fname, verus_path):
    """
    remove redundant pre-conditions of function fname
    """

    if not proved_by_verus(code, verus_path):
        print("[remove_redundant_req] Error: this input code is not proved yet")
        return code

    new_code = ""
    requires = False
    infunction = False
    done = False
    codelines = code.split("\n")
    totlines = len(codelines)
    for i, line in enumerate(codelines):
        remove = False

        if done:
            new_code += line + "\n"
            continue

        if requires:
            if "{" in line or "ensures" in line:
                # not all { means the end of requires, but I don't handle more complicated cases now
                done = True
            else:
                # Let's try remove this line and see if it still works
                j = i + 1
                tmp = new_code
                while j < totlines:
                    tmp += codelines[j] + "\n"
                    j = j + 1
                if proved_by_verus(tmp, verus_path):
                    print("[remove_redundant_req] Found a redundant require line:")
                    print(line)
                    remove = True

        elif infunction:
            if line.strip().startswith("requires"):
                requires = True
        else:
            # look for target function
            if "fn" in line and fname in line:
                infunction = True

        if not remove:
            new_code += line + "\n"
    return new_code


# ============================================================================
# PRECONDITION ERROR PROCESSING
# ============================================================================


def process_precondition_error(
    error: str, code: str
) -> tuple[list[str], list[str], list[str], list[str]]:

    err_callnnum = []
    err_call = []
    err_prefun = []
    err_precond = []

    codelines = code.split("\n")
    errlines = error.split("\n")
    for i, line in enumerate(errlines):
        if line == "error: precondition not satisfied":
            # this is either the invocation line or precondition line
            if "precondition" in errlines[i + 4]:
                preline = errlines[i + 3]
                callline = errlines[i + 6]
                vline = errlines[i + 7]
            else:
                preline = errlines[i + 6]
                callline = errlines[i + 3]
                vline = errlines[i + 4]

            j = callline.find("|")
            if j < 0:
                print("Fatal error: did not find | in the precondition error line:")
                print(callline)
                exit()
            err_callnnum.append(callline.split("|")[0].strip())
            tmpcall = callline[j + 1 :].strip()
            # This is the line where callee's precondition is not satisfied
            err_call.append(tmpcall)
            # Now, we want to get the callee's name
            j = vline.find("^")
            tmpcall = callline[j:]
            err_fname = tmpcall.split("(")[0].strip()
            # if the call is obj.f, we want to just get f
            if err_fname.find(".") >= 0:
                err_fname = err_fname.split(".")[1]

            j = preline.find("|")
            if j < 0:
                print("Fatal error: did not find | in the precondition error line:")
                print(preline)
                exit()
            err_precond.append(preline[j + 1 :].strip())
            err_prefuncln = preline.split("|")[0].strip()

            err_prefunlist = []
            codeindex = int(err_prefuncln) - 1
            codeindexend = 0
            while codeindex >= 0:
                if "requires" in codelines[codeindex]:
                    codeindexend = codeindex
                if err_fname in codelines[codeindex] and "fn" in codelines[codeindex]:
                    break
                codeindex = codeindex - 1
            if codeindexend == 0:
                print("Error: did not find key word `requies'")
                codeindexend = int(err_prefuncln)

            while codeindex < codeindexend:
                err_prefunlist.append(codelines[codeindex].strip())
                codeindex = codeindex + 1
            err_prefun.append(" ".join(err_prefunlist))

    return err_callnnum, err_call, err_prefun, err_precond


def get_unexpected_error(code, verus_path, expects):
    _, msg = evaluate(code, verus_path)
    chunks = msg.stderr.split("\n\n")
    error = ""
    for ch in chunks:
        add = False
        for x in ch.split("\n"):
            if not add and x.startswith("error"):
                for ex in expects:
                    if ex in x:
                        break
                else:
                    add = True
            if add:
                error += x + "\n"
        # error_line = [x for x in ch.split("\n") if x.startswith("error")]
        # if not error_line:
        #     continue
        # error_line = error_line[0]
        # for ex in expects:
        #     if ex in error_line:
        #         break
        # else:
        #     error += ch + "\n\n"
    return error


# ============================================================================
# TYPE ERROR FIXING FUNCTIONS
# ============================================================================


def fix_one_type_error(oldline: str, cstart: int, cend: int, newtype: str) -> str:
    """
    Fix a type error on a single line by adding type cast.

    Args:
        oldline: The original line of code
        cstart: Starting index of the problematic expression
        cend: Ending index of the problematic expression
        newtype: The expected type

    Returns:
        Fixed line with appropriate type cast added
    """
    prefix = oldline[:cstart]
    mid = oldline[cstart : cend + 1]
    suffix = oldline[cend + 1 :]

    oldtype_pos = mid.rfind(" as ")

    if oldtype_pos > -1:
        if " " in mid[oldtype_pos + 4 :].strip():
            # there was not a cast type for the whole expression
            # instead it is something like x as int - 1
            oldtype_pos = -1

    if oldtype_pos == -1:
        # the old expression does not have "as oldtype"
        if re.match(r"^\(*\)$", mid.strip()):
            # already in parentheses
            newmid = mid + " as " + newtype
        #####some times code is written like j-1 and hence needs ()
        # elif mid.strip().find(" ") == -1:
        # mid is one variable, no need for parentheses
        #    newmid = mid + " as " + newtype
        else:
            newmid = "( " + mid + " ) as " + newtype
    else:
        # replace the old as type
        newmid = mid[:oldtype_pos] + " as " + newtype

    return prefix + newmid + suffix


# This function uses veval's ErrTrace type, which allows
# the skip of get_typeerror
def fix_one_type_error_in_code(code, err_trace, verbose=True):
    # note that linenum, cstart, cend indices all start from 0
    err_label = err_trace.strlabel
    if err_label is None or "`" not in err_label:
        sys.stderr.write("Fatal error: err_trace does not have a label")
        sys.stderr.write(code)
        return code
    newtype = err_label.split("`")[1]

    err_lnum = err_trace.get_lines()[0]
    linenum = err_lnum - 1

    line = err_trace.get_text()
    cstart = err_trace.text[0].hl_start - 1
    cend = err_trace.text[0].hl_end - 2
    err_exp = line[cstart : cend + 1]

    newlines = []
    for i, line in enumerate(code.split("\n")):
        if i != linenum:
            newlines.append(line)
        else:
            if err_exp not in line:
                sys.stderr.write("Fatal error: `" + err_exp + "' does not exist in " + line)
                exit()
            if err_exp != line[cstart : cend + 1]:
                sys.stderr.write(
                    "Fatal error. Expected expression is `"
                    + err_exp
                    + "'; Get expression `"
                    + line[cstart : cend + 1]
                )

            newline = fix_one_type_error(line, cstart, cend, newtype)

            # Sometimes, we may encounter non-fixable type error
            # for example if one expects ..i or [i] to be int, ..i as int or [i] as int will return the same type error
            # so, we return "" to warn the caller
            # otherwise, the caller may hang
            if line == newline:
                return ""

            if verbose:
                sys.stderr.write(
                    "[fix_one_type_error_in_code] changed the type of `"
                    + line[cstart : cend + 1]
                    + "'"
                    + "as `"
                    + newline.strip()
                    + "'"
                )
            newlines.append(newline)

    return "\n".join(newlines) + "\n"


#    return fix_one_type_error_in_code(code, err_lnum-1, err_cstart-1, err_cend-2, err_newtype, err_exp)


# get detailed information about one type error from error message
# TODO: this function can be replaced later when json format error is available
# Note: all index number starts from 0
# Return: linenum, col_start, col_end, expected type, linestr
def get_typeerror(error, verbose=True):

    if "[E0308]" not in error:
        print("Fatal error: function get_typeerror is invoked to process non-type error.")
        return None

    errorlines = error.split("\n")

    linenum = -1

    for i, eline in enumerate(errorlines):
        if "[E0308]" in eline:
            # to refine errorlines[i+3] based on ^s in errorlines[i+4]
            # the line showing the original program code with type errors
            targetline = errorlines[i + 3]
            # the line with - and ^ indicating where the errors are
            referline = errorlines[i + 4]

            j = targetline.find("|")
            if j < 0:
                print("Fatal error: did not find | in the type error line:")
                print(targetline)
                return None

            linenum = targetline.split("|")[0].rstrip()
            targetline[j + 1 :].strip()

            # search for the line that explains the type error
            expline_idx = i + 4
            while "expected `" not in errorlines[expline_idx]:
                expline_idx += 1
                if expline_idx > i + 10:
                    # I doubt the explanation line will appear so late
                    print("Fatal error: did not find expected type in the type error message about")
                    print(targetline)
                    return None

            # the line that explains what type is expected and what is found instead
            expline = errorlines[expline_idx]
            e = expline.find("expected `")
            newtype = expline[e:].split("`")[1]

            if expline_idx != i + 4:
                # explanation is not the same as the reference line
                col_end = e
                while col_end + 1 < len(referline) and referline[e] == referline[col_end + 1]:
                    col_end = col_end + 1
                col_start = e
                while col_start > 0 and referline[col_end] == referline[col_start - 1]:
                    col_start = col_start - 1
            else:
                # explanation is in the same line as the reference line
                # the line is like: - expected `int` or ^ expected `int`
                col_end = e - 2
                col_start = col_end
                while col_start > 0 and referline[col_end] == referline[col_start - 1]:
                    col_start = col_start - 1

            badexpr = targetline[col_start : col_end + 1]

            if verbose:
                print(
                    "[get_typeerror] `"
                    + badexpr
                    + "` in `"
                    + targetline[j + 1 :].strip()
                    + "`"
                    + f" of Line {col_start - (j + 1)} should has type "
                    + newtype
                )
            break

    # Needs to minus j+1, because the error message prepend the code line with line number and '|'
    return int(linenum) - 1, col_start - (j + 2), col_end - (j + 2), newtype, badexpr


# ============================================================================
# CODE CLEANING & FORMATTING UTILITIES
# ============================================================================


def clean_code(code: str) -> str:
    might_code = re.findall(r"```rust(.*)```|```verus(.*)```", code, flags=re.DOTALL)
    if might_code:
        code = might_code[0][0] if might_code[0][0] else might_code[0][1]

    lines = []
    for line in code.split("\n"):
        if line.strip() == "```":
            continue

        # This is ad-hoc, but somehow GPT often generates ```use ... on first line
        if line.startswith("```"):
            line = line[3:]

        lines.append(line)
    code = "\n".join(lines)
    return code


def clean_reflection(content: str) -> str:
    """
    Clean reflection content by keeping only specific lines.

    Args:
        content: Content with reflection comments

    Returns:
        Cleaned content
    """
    lines = []
    for line in content.split("\n"):
        if (
            line.strip() == ""
            or line.strip().startswith("//Action")
            or line.strip().startswith("//Reflection")
        ):
            lines.append(line)
    code = "\n".join(lines)
    return code


# ============================================================================
# EXAMPLE LOADING FUNCTIONS
# ============================================================================


def get_examples(example_path: str, example_dir_name: str) -> list[dict[str, str]]:
    """
    Load examples from input/output directories.

    Args:
        example_path: Base path to examples directory
        example_dir_name: Name of the example subdirectory

    Returns:
        List of dictionaries with 'query' and 'answer' keys
    """
    examples = []
    for f in sorted(os.listdir(os.path.join(example_path, f"input-{example_dir_name}"))):
        if f.endswith(".rs") and f.startswith("ex"):
            input_file = os.path.join(example_path, f"input-{example_dir_name}", f)
            output_file = os.path.join(example_path, f"output-{example_dir_name}", f)
            input_content = open(input_file).read()
            output_content = open(output_file).read()
            examples.append({"query": input_content, "answer": output_content})
    with open(f"example-{example_dir_name}.txt", "w") as f:
        for example in examples:
            f.write("Query:\n" + example["query"])
            f.write("\n\nAnswer:\n" + example["answer"])
            f.write("\n\n")
    return examples


def get_text_examples(example_path: str, example_dir_name: str) -> list[str]:
    """
    Load text examples from a directory.

    Args:
        example_path: Base path to examples directory
        example_dir_name: Name of the example subdirectory

    Returns:
        List of example file contents
    """
    examples = []
    for f in sorted(os.listdir(os.path.join(example_path, example_dir_name))):
        if f.endswith(".rs") and f.startswith("ex"):
            input_file = os.path.join(example_path, example_dir_name, f)
            input_content = open(input_file).read()
            examples.append(input_content)
    return examples
