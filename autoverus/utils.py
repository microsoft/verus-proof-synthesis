# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


import difflib
import json
import os
import re
import subprocess
import sys
import tempfile

from lynette import lynette

DEBUG_SAFE_CODE_CHANGE = False


class AttrDict(dict):
    def __getattr__(self, name):
        return self[name]


def remove_comment(code):
    """
    remove single-line comments in code
    """
    new_code = ""
    for line in code.split("\n"):
        if line.strip().startswith("//"):
            continue
        new_code += line + "\n"
    return new_code


def get_nonlinear_lines(code, logger):
    """
    Get all lines that contain nonlinear arithmetic operations
    """
    code_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="veurs_nonlinear_", suffix=".rs"
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
            # TODO: the first element of the tuple is the type of the expression(currently limited to "invariant" or "assert")
            for ex_type, (st, ed) in nl_lines:
                text = "\n".join(code_lines[st - 1 : ed])
                if ex_type == "assert" and "nonlinear_arith" not in text:
                    # Only return the lines unlabelled with nonlinear_arith
                    output_lines.append((st, ed, text))
                elif ex_type == "invariant":
                    output_lines.append((st, ed, text))
            return output_lines
        except json.JSONDecodeError:
            logger.error(f"Error in decoding nonlinear arithmetic operations: {m.stdout}")
            return []
    else:
        return []


def code_change_is_safe(
    origin,
    changed,
    verus_path,
    logger,
    target_mode=True,
    util_path="../utils",
    inter=False,
    debug=True,
):
    if debug and DEBUG_SAFE_CODE_CHANGE:
        logger.warning("Debug mode is on, skip code change checking")
        return True

    orig_f = tempfile.NamedTemporaryFile(mode="w", delete=False, prefix="llm4v_orig", suffix=".rs")
    orig_f.write(origin)
    orig_f.close()

    changed_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_changed", suffix=".rs"
    )
    changed_f.write(changed)
    changed_f.close()

    cargopath = util_path + "/lynette/source/Cargo.toml"

    opts = []
    if inter:
        opts = ["--asserts-anno"]
    elif target_mode:
        opts = ["-t"]

    verus_compare_cmd = (
        ["cargo", "run", "--manifest-path", cargopath, "--", "compare"]
        + opts
        + [orig_f.name, changed_f.name]
    )

    m = subprocess.run(verus_compare_cmd, capture_output=True, text=True)
    # os.unlink(orig_f.name)
    # os.unlink(changed_f.name)

    if m.returncode == 0:
        return True
    elif m.returncode == 1:
        err_m = m.stdout.strip()
        if err_m == "Files are different":
            return False
        else:
            logger.error(f"Error in comparing code changes: {err_m}")
            return False
    else:
        err_m = m.stderr.strip()
        if "unwrap()" in err_m:
            logger.error(f"Error in comparing code changes: {err_m}")
            return False

    return None


def get_func_body(code, fname, util_path=None):
    orig_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="veurs_copilot_", suffix=".rs"
    )
    orig_f.write(code)
    orig_f.close()

    cargopath = util_path + "/lynette/source/Cargo.toml"

    lynette_extract_cmd = [
        "cargo",
        "run",
        "--manifest-path",
        cargopath,
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


def check_changed_code_v2(origin, changed):
    """
    check if any change is made in non-invariant, non-assert, non require/ensure code blocks, if exists then invalid
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


def evaluate(code, verus_path, func_name=None):
    fn = tempfile.NamedTemporaryFile(mode="w", delete=False, prefix="llm4v_eval", suffix=".rs")
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


def compress_nl_assertion(code):
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


def remove_redundant_loopinv(code):
    """
    remove redundant loop invariants in code
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


def same_code_verus(code1, code2, verus_path):
    """
    Check if two code snippets return the same Verus err results
    """
    _, msg1 = evaluate(code1, verus_path)
    _, msg2 = evaluate(code2, verus_path)
    err1 = msg1.stderr + msg1.stdout
    err2 = msg2.stderr + msg2.stdout
    return err1 == err2


def remove_unnecessary_assert(code):
    """
    Any assert whose existence does not affect Verus proof result will be removed
    """
    # TO Be Implemented
    return


def load_jsonl(filename):
    with open(filename) as f:
        return [json.loads(line) for line in f]


def dump_jsonl(data, filename):
    with open(filename, "w") as f:
        for line in data:
            json.dump(line, f)
            f.write("\n")


def fix_one_type_error(oldline, cstart, cend, newtype):
    # cstart: the starting index of the problematic expression
    # cend: the ending index of the problematic expression

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


# this function uses veval's ErrTrace type, which allows
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


def clean_code(code):
    might_code = re.findall(r"```rust(.*)```|```verus(.*)```", code, flags=re.DOTALL)
    if might_code:
        code = might_code[0][0] if might_code[0][0] else might_code[0][1]

    lines = []
    for line in code.split("\n"):
        if line.strip() == "```":
            continue

        # this is ad-hoc, but somehow GPT often generates ```use ... on first line
        if line.startswith("```"):
            line = line[3:]

        lines.append(line)
    code = "\n".join(lines)
    return code


def insert_loop_isolation(code):
    """Insert #[verifier::loop_isolation(false)]"""
    lines = code.splitlines()
    verus_line = -1
    for i, line in enumerate(lines):
        if "verus!" in line:
            verus_line = i
            break
    if verus_line == -1:
        print("No verus! found in the code.")
        return code
    insert_line = "\n#[verifier::loop_isolation(false)]"
    new_code = "\n".join(lines[: verus_line + 1] + [insert_line] + lines[verus_line + 1 :])
    return new_code


def insert_lemma_func(code, lemma_names, lemma_path):
    """Insert existing already-proved lemmas"""
    for lemma_name in lemma_names:
        name = lemma_name
        if not name.endswith(".rs"):
            name = name + ".rs"
        input_file = os.path.join(lemma_path, name)
        lemma_code = open(input_file).read()
        lemma_func_dict = {lemma_name: lemma_code}
        code = insert_proof_func(code, lemma_func_dict)
    return code


def insert_proof_func(code, proof_func_dict):
    """Insert the proof functions into the code."""
    lines = code.splitlines()
    verus_line = -1
    for i, line in enumerate(lines):
        if "verus!" in line:
            verus_line = i
            break
    if verus_line == -1:
        return code
    proof_func_code = "\n\n".join(proof_func_dict.values())
    new_code = "\n".join(lines[: verus_line + 1] + [proof_func_code] + lines[verus_line + 1 :])
    return new_code
