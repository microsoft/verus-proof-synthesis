# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #

import difflib
import tempfile

from lynette import lynette
from veval import VerusError, VerusErrorType, VEval

from utils import compress_nl_assertion


class houdini:
    def __init__(self, config):
        self.config = config
        self.verification_path = config.verus_path

    def merge_code(self, code1, code2):
        code1 = "\n".join(code1.split("\n"))
        code2 = "\n".join(code2.split("\n"))
        code1 = code1.replace("\t", "    ")
        code2 = code2.replace("\t", "    ")
        diff = list(difflib.ndiff(code1.splitlines(), code2.splitlines()))

        newdiff = []
        for i, x in enumerate(diff):
            if (
                not x[2:].strip().startswith("//")
                and not x.startswith("?")
                and not x.startswith("-")
            ):
                newdiff.append(x)
            elif x.startswith("-"):
                toappend = True
                if x[2:].find(" fn ") != -1:
                    # code2 changed function prototype. should replace instead of merge
                    # TODO: how do we know we are getting the right function prototype???
                    print("Diff error at function prototype. Adjusted.")
                    toappend = False

                if i + 1 < len(diff):
                    if diff[i + 1].startswith("+") and x[2:].strip() == diff[i + 1][2:].strip():
                        # this - is immediately followed by a + with only white space difference
                        # it is ok to keep both in case of loop invariants, but not ok to keep both for function prototypes
                        print("Diff error at white spaces. Adjusted.")
                        toappend = False

                if toappend:
                    newdiff.append(x)
        code = "\n".join([x[2:] for x in newdiff])
        # print("Merged code:" + code)
        return code

    def merge_invariant(self, code1, code2):
        with (
            tempfile.NamedTemporaryFile(mode="w", prefix="merge_inv_orig", suffix=".rs") as f1,
            tempfile.NamedTemporaryFile(mode="w", prefix="merge_new_inv", suffix=".rs") as f2,
        ):
            f1.write(code1)
            f1.flush()
            f2.write(code2)
            f2.flush()

            path1 = f1.name
            path2 = f2.name

            m = lynette.code_merge_invariant(path1, path2)

        if m.returncode == 0:
            return m.stdout
        else:
            raise Exception(f"Error in merging invariants:{m.stderr}")

    # the input is a list of Veval list[VerusError]
    def get_error_line(self, failures: list[VerusError], considerassert=True):
        ret = []
        for f in failures:
            # if we don't want Houdini to remove assert, we skip assert errors
            if considerassert and f.error == VerusErrorType.AssertFail:
                ret.append(f.trace[0].lines[0])
            elif f.error == VerusErrorType.InvFailEnd or f.error == VerusErrorType.InvFailFront:
                ret.append(f.trace[0].lines[0])
            elif f.error == VerusErrorType.RustAssert:
                ret.append(f.trace[0].lines[0])
            elif f.error == VerusErrorType.ExecinGhost:
                ret.append(f.trace[0].lines[0])
            else:
                # It is dangerous to let Houdini remove any random line
                # In general, it is safe to remove any ghost code line
                continue
        return ret

    def get_ensure_error_line(self, failures: list[VerusError]):
        ret = []
        for f in failures:
            if f.error == VerusErrorType.PostCondFail:
                ret.append(f.trace[0].lines[0])

        return ret

    def run(self, code, verbose=False):
        code = compress_nl_assertion(code)
        for _ in range(100):
            # score, msg = evaluate(code, self.verification_path)
            # if score[1] == 0:
            #    break
            veval = VEval(code)
            veval.eval()
            failures = veval.get_failures()

            if len(failures) == 0:
                break

            lines = self.get_error_line(failures)

            if len(lines) == 0:
                # cannot find a correct answer
                break
            code = code.split("\n")
            for line in lines:
                #                print("to delete [{}]".format(line))
                if line == 0:
                    continue
                code[line - 1] = "// // //" + code[line - 1]
            code = "\n".join([x for x in code if not x.startswith("// // //")])
        return failures, code

    # this Houdini run function was developed to be part of the inter-procedural Houdini
    # If Houdini is able to find a correct version, the correct version is returned
    #           and the score is the correct version's verification result
    # Otherwise, the last version of the Houdini changed code is returend, and the corresponding score
    #
    # considerassert: if false, it cannot be removed by houdini
    #
    # Return: failures, code
    def run_interproc(self, code, verbose=False, removPost=False, considerassert=True):
        #        code = compress_nl_assertion(code)
        # TODO: we do not consider nl for now
        print("Houdini processing:")
        print(code)

        # Here, we remove all the incorrect invariants or asserts, assuming function pre-condition is correct
        # TODO: is 10 a good bound?
        for _ in range(10):
            veval = VEval(code)
            veval.eval()
            failures = veval.get_failures()

            if len(failures) == 0:
                print("Houdini: found a correct version")
                return failures, code

            lines = self.get_error_line(failures, considerassert)

            if len(lines) == 0:
                print(
                    "Houdini: cannot find a correct version ... will try removing post conditions ..."
                )
                # cannot find a correct answer
                break
            code = code.split("\n")
            for line in lines:
                print(f"Houdini: going to remove error line {line}:" + code[line - 1])
                code[line - 1] = "// // //" + code[line - 1]
            code = "\n".join([x for x in code if not x.startswith("// // //")])

        # Here, we remove function post-conditions that cannot be satisifed (TODO: should this be done later?)
        veval = VEval(code)
        veval.eval()
        failures = veval.get_failures()

        if len(failures) == 0:
            print("Houdini: found a correct version")
            return failures, code

        if len(failures) > 0 and removPost:
            # we will try removing function post conditions
            lines = self.get_ensure_error_line(failures)

            if len(lines) == 0:
                print("Houdini: no function post-conditio violated. Cannot find a correct version")
                return failures, code

            for line in lines:
                print("Houdini: going to remove unsatisfied post conditions:")
                print(code[line - 1])
                code[line - 1] = "// // //" + code[line - 1]
            code = "\n".join([x for x in code if not x.startswith("// // //")])

            # another round of intra-proc houdini, just in case moving post-condition left syntax errors and others
            for _ in range(100):
                veval = VEval(code)
                veval.eval()
                failures = veval.get_failures()

                if len(failures) == 0:
                    print("Houdini: found a correct version")
                    return failures, code

                lines = self.get_error_line(failures)

                if len(lines) == 0:
                    print("Houdini: cannot find a correct version")
                    # cannot find a correct answer
                    return failures, code

                code = code.split("\n")
                for line in lines:
                    print("Houdini: going to remove error line:")
                    print(code[line - 1])
                    code[line - 1] = "// // //" + code[line - 1]
                code = "\n".join([x for x in code if not x.startswith("// // //")])

            veval = VEval(code)
            veval.eval()
            failures = veval.get_failures()
            if len(failures) == 0:
                print("Houdini: found a correct version")
                return failures, code

        return failures, code
