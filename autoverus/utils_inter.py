# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


# Content in this file is mainly used to support inter-procedural inference    #
# It is quite a bit hack and should be replaced by parser-backed implementation#


import difflib
import re
import sys

from veval import VEval

from utils import code_change_is_safe

##Utility functions for inter-procedural inference


def split_code_by_func(code, oprefix, tofile=False):
    intervalstart = []
    intervalend = []
    names = []
    ofiles = []
    totalline = len(code.split("\n"))
    findex = 0
    for i, line in enumerate(code.split("\n")):
        if line.strip().startswith("fn ") or line.strip().startswith("pub fn "):
            # getting this function's code
            fcode = line
            # get starting line number
            intervalstart.append(i)

            # get function name
            tmp = re.sub(r"\(.+", "", line)
            name = re.sub(r".+fn ", "", tmp)
            names.append(name)

            # check if the function is empty
            if line.strip().endswith("{}"):
                intervalend.append(i)
                if tofile:
                    output_file = oprefix + f"_{findex}_" + name + "_.rs"
                    ofiles.append(output_file)
                    with open(output_file, "w") as wf:
                        wf.write(fcode)
                findex += 1
                continue

            # get function ending line number
            ident = len(line) - len(line.lstrip())
            j = i + 1
            foundend = False
            while j < totalline:
                jline = code.split("\n")[j]
                fcode = fcode + "\n" + jline
                jident = len(jline) - len(jline.lstrip())
                if jident == ident and jline.strip().startswith("}"):
                    intervalend.append(j)
                    foundend = True
                    break
                j = j + 1
            if not foundend:
                print("Warning: did not find a matching end of function" + name)
                intervalend.append(totalline)
            if tofile:
                output_file = oprefix + f"_{findex}_" + name + "_.rs"
                ofiles.append(output_file)
                with open(output_file, "w") as wf:
                    wf.write(fcode)
            findex += 1
    return intervalstart, intervalend, ofiles


def get_indentstr(indent):
    i = 0
    istr = ""
    while i < indent:
        istr += " "
        i += 1
    return istr


def highlight_code_by_func(code, oprefix, tofile=False):
    intervalstart = []
    intervalend = []
    names = []
    ofiles = []
    code = code.replace("\t", "    ")
    totalline = len(code.split("\n"))
    findex = 0

    for i, line in enumerate(code.split("\n")):
        if line.strip().startswith("fn ") or line.strip().startswith("pub fn "):
            # getting this function's code
            fcode = line
            # get starting line number
            intervalstart.append(i)

            # get function name
            tmp = re.sub(r"\(.+", "", line)
            name = re.sub(r".+fn ", "", tmp)
            names.append(name)

            # get function ending line number
            ident = len(line) - len(line.lstrip())
            j = i + 1
            foundend = False
            while j < totalline:
                jline = code.split("\n")[j]
                fcode = fcode + "\n" + jline
                jident = len(jline) - len(jline.lstrip())
                if jident == ident and jline.strip().startswith("}"):
                    intervalend.append(j)
                    foundend = True
                    break
                j = j + 1
            if not foundend:
                print("Warning: did not find a matching end of function" + name)
                intervalend.append(totalline)
            findex += 1

    for i, fname in enumerate(names):
        # generate the highlighted file just for function fname
        print(
            "Generating a file highlighting function "
            + fname
            + f" (L{intervalstart[i] + 1} --- L{intervalend[i] + 1})"
        )

        newcode = ""
        mystart = intervalstart[i]
        myend = intervalend[i]
        currentident = -1
        insidef = False
        unimplemented = False
        currentfunc = ""

        for k, oldline in enumerate(code.split("\n")):

            if oldline.strip().startswith("fn ") or oldline.strip().startswith("pub fn "):
                if insidef:
                    print(
                        "Fatal error: did not find the finish bracket for function " + currentfunc
                    )
                tmp = re.sub(r"\(.+", "", oldline)
                tmpname = re.sub(r".+fn ", "", tmp)
                currentfunc = tmpname

            if k <= myend and k >= mystart:
                # in the function to be highlighted
                #    print("...L{} in highlighted function ...".format(k))
                newcode += "\n" + oldline
            elif oldline.strip().startswith("fn ") or oldline.strip().startswith("pub fn "):
                # entering a function that is not to be highlighted
                #                print("...in a non-highlighted function " + tmpname + "...")
                currentident = len(oldline) - len(oldline.lstrip())
                #                print(".....indentation {}".format(currentident))
                newcode += "\n" + get_indentstr(currentident) + "#[verifier::external_body]"
                newcode += "\n" + oldline
                insidef = True
                if re.search(r"{", oldline):
                    #                    print("found { in the same line as function name for " + currentfunc)
                    unimplemented = True
                    newcode += "\n" + get_indentstr(currentident + 4) + "unimplemented!()"
            elif insidef:
                myindent = len(oldline) - len(oldline.lstrip())
                if (currentident == myindent) and oldline.lstrip().startswith("{"):
                    newcode += "\n" + oldline
                    unimplemented = True
                    newcode += "\n" + get_indentstr(currentident + 4) + "unimplemented!()"
                #                    print("found { in different line from f name for " + currentfunc)
                elif not unimplemented:
                    #                    print("in function head block waiting for bracket with indent {}".format(currentident))
                    #                    print("indent {}".format(myindent) + "..." + oldline)
                    newcode += "\n" + oldline
                elif (currentident == myindent) and oldline.lstrip().startswith("}"):
                    #                    print("found } for " + currentfunc)
                    newcode += "\n" + oldline
                    insidef = False
                    if not unimplemented:
                        print(
                            "Fatal error: did not find starting bracket for function: "
                            + currentfunc
                        )
                    unimplemented = False
            else:
                newcode += "\n" + oldline

        if "#![verifier::loop_isolation(false)]" not in newcode:
            newcode = "#![verifier::loop_isolation(false)]\n" + newcode

        if tofile:
            output_file = oprefix + f"_{i}_" + fname + "_.rs"
            ofiles.append(output_file)
            with open(output_file, "w") as wf:
                wf.write(newcode)
            print("... into file " + output_file)

    return ofiles, names


def merge_with_highlight(codeA, codeB, hfunc):
    # merge codeB's hfunc into codeA, keep everything else unchanged

    codeA = codeA.replace("\t", "    ")
    codeB = codeB.replace("\t", "    ")

    # get codeB's hfunc into hfcode
    hstart, hend = get_fun_range(codeB, hfunc)
    bi = hstart
    hfcode = ""
    while bi <= hend:
        hfcode += codeB.split("\n")[bi]
        hfcode += "\n"
        bi += 1

    # replace hfunc's implementation in codeA with hfcode
    hstartA, hendA = get_fun_range(codeA, hfunc)

    if hstartA >= hendA:
        print("Fatal Error")

    ai = 0
    merged = ""
    codeAlines = codeA.split("\n")
    codeBlines = codeB.split("\n")

    # just in case ...
    if (
        codeAlines[hstartA - 1].strip() == "#[verifier::external_body]"
        and not codeBlines[hstart - 1].strip() == "#[verifier::external_body]"
    ):
        print("[Warning] A verifier external body " + hfunc + " will become non external body")
        hstartA = hstartA - 1

    while ai < len(codeAlines):
        if ai == hstartA:
            merged += hfcode
        elif ai <= hstartA or ai > hendA:
            merged += codeAlines[ai]
            merged += "\n"
        ai += 1
    return merged


# merge hfunc and any function's new post-condition in codeB into codeA
# return merged code and line numbers (in returned code) of those added post conditions
def merge_with_highlight_post(codeA, codeB, hfunc):
    codeA = codeA.replace("\t", "    ")
    codeB = codeB.replace("\t", "    ")
    merge1 = merge_with_highlight(codeA, codeB, hfunc)
    diff = list(difflib.ndiff(merge1.splitlines(), codeB.splitlines()))
    #   print("Here are the changed pre/post conditions of non-highlight functions:")
    #    print("\n".join(diff))
    newdiff = []
    newpostlines = []
    inensure = False
    infunchead = False
    findent = 0
    newi = 0
    for _i, x in enumerate(diff):
        myindent = len(x[2:]) - len(x[2:].lstrip())
        if x.find(" fn ") != -1:
            findent = myindent
            infunchead = True
            if x.endswith("{"):
                infunchead = False
                inensure = False
        elif x.find("{") != -1 and myindent == findent:
            inensure = False
            infunchead = False
        elif x.find("ensures") != -1 and infunchead:
            inensure = True

        if x.startswith("?"):
            continue
        elif x.startswith("-"):
            # I would keep every line of code in the old version
            newdiff.append(x)
        elif x.startswith("+"):
            # Only take the new post condition
            if inensure:
                newpostlines.append(newi)
                newdiff.append(x)
            else:
                continue
        else:
            newdiff.append(x)

        newi += 1

    return "\n".join([x[2:] for x in newdiff]), newpostlines


def get_fun_range_inner(code, hfunc):

    len(code.split("\n"))

    inhf = False
    foundend = False
    startl = -1
    endl = -1

    for i, line in enumerate(code.split("\n")):
        if line.strip().startswith("fn ") or line.strip().startswith("pub fn "):
            # getting this function's code

            # get function name
            tmp = re.sub(r"\(.+", "", line)
            nametmp = re.sub(r".+fn ", "", tmp)
            name = re.sub(r"fn ", "", nametmp)
            # print("find function "+name + " while looking for function " + hfunc)

            if name == hfunc:
                startl = i
                # print(hfunc + "starts at L {}".format(startl+1))
                ident = len(line) - len(line.lstrip())
                inhf = True

        elif inhf:
            dent = len(line) - len(line.lstrip())
            if dent == ident and line.strip().startswitch("{"):
                startl = i

            if dent == ident and line.strip().startswith("}"):
                endl = i
                foundend = True
                # print(hfunc + "ends at L {}".format(endl+1))
                break

    if not foundend or not inhf:
        print("Warning: did not find (a matching end of) function " + hfunc)

    return startl, endl


# An ad-hoc way of getting a function from a file w/o parser support
def get_fun_range(code, hfunc):

    len(code.split("\n"))

    inhf = False
    foundend = False
    startl = -1
    endl = -1

    for i, line in enumerate(code.split("\n")):
        if line.strip().startswith("fn ") or line.strip().startswith("pub fn "):
            # getting this function's code

            # get function name
            tmp = re.sub(r"\(.+", "", line)
            nametmp = re.sub(r".+fn ", "", tmp)
            name = re.sub(r"fn ", "", nametmp)
            # print("find function "+name + " while looking for function " + hfunc)

            if name == hfunc:
                startl = i
                # print(hfunc + "starts at L {}".format(startl+1))
                ident = len(line) - len(line.lstrip())
                inhf = True

        elif inhf:
            dent = len(line) - len(line.lstrip())
            # print(dent)
            if dent == ident and line.strip().startswith("}"):
                endl = i
                foundend = True
                # print(hfunc + "ends at L {}".format(endl+1))
                break

    if not foundend or not inhf:
        print("Warning: did not find (a matching end of) function " + hfunc)

    return startl, endl


def check_syntaxerr_inv(code):
    """
    Check if the generated invariants have wrong syntax
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


########The next few functions work on removing redundant or unnecessary proof annotations#######
def get_invariant_lines(code):
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


def remove_unnecessary_lines(code, logger, util_path, candidates=None):
    """
    Given a program, code, that Verus can verify.
    going through the ghost-code line numbers in candidates array.
    check one by one to see if any of them can be removed without hurting the verification.

    if code cannot be verified, nothing will be done

    this function only goes through candidates array once. the caller may decide to call this function multiple times until it converges

    return: the resulting code, the number of unnecessary annotations identified
    """
    if candidates is None:
        candidates = []
    veval = VEval(code, logger)
    score = veval.eval_and_get_score()
    if not score.is_correct():
        return code, 0

    if len(candidates) == 0:
        return code, 0

    if "// // // _comment_out_" in code:
        return code, 0

    changed = 0
    workingset = candidates

    for line_num in workingset:
        new_code, oldline = comment_out_a_line(code, line_num)
        if not code_change_is_safe(
            code, new_code, "", logger, util_path=util_path, debuginfo=False
        ):
            continue
        veval = VEval(new_code)
        score = veval.eval_and_get_score()
        if score.is_correct():
            sys.stderr.write(f"Unnecessary proof annotation @ Line-{line_num}: {oldline}\n")
            changed = changed + 1
            code = new_code

    if changed > 0:
        lines = code.split("\n")
        code = "\n".join([x for x in lines if not x.startswith("// // // _comment_out_")])

    return code, changed


def remove_unnecessary_annotation(code, logger, util_path, an_type="assert"):
    """
    remove loop invariants or assert that are unnecessary for Verus proof
    this function only works for code that Verus can already prove
    """
    veval = VEval(code, logger)
    score = veval.eval_and_get_score()
    if not score.is_correct():
        return code, 0

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
        code, changed_inc = remove_unnecessary_lines(code, logger, util_path, lines)
        changed_num += changed_inc
        if changed_inc > 0:
            changed = True
        rnd = rnd + 1

    return code, changed_num


def remove_redundant_req(code, fname, verus_path):
    """
    remove redundant pre-conditions of function fname
    """

    if not proved_by_verus(code):
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
                if proved_by_verus(tmp):
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


def proved_by_verus(code):
    veval = VEval(code)
    score = veval.eval_and_get_score()
    if not score.is_correct():
        return False
    else:
        return True
