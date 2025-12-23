# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #

# Very preliminary inter-procedural version#


import os
import re

from generation import Generation
from houdini import houdini
from infer import LLM
from refinement import Refinement
from utils_inter import (
    check_syntaxerr_inv,
    merge_with_highlight,
    merge_with_highlight_post,
    remove_redundant_loopinv,
    remove_redundant_req,
)
from veval import VerusError, VerusErrorType, VEval


class interGeneration:
    def __init__(self, config, logger, phase1_examples=None):
        if phase1_examples is None:
            phase1_examples = ["3", "6", "7"]
        self.config = config
        self.llm = LLM(config, logger)
        self.logger = logger
        self.hdn = houdini(config)
        self.generation = Generation(config, logger)
        self.refinement = Refinement(config, logger)

        self.infer_funcs = [
            self.generation.direct_inference,
            self.generation.constantrefine_inference,
            self.generation.arraylen_inference,
            self.generation.arrayrefine_inference,
        ]

        self.phase1_examples = phase1_examples

        self.logger.warning("Generation initialized with phase1_examples: %s", self.phase1_examples)

    # TODO: this function was a bit a hack.
    #   It is different from the generic repair agents we usually have, because we want it to leave `hints' for potential follow-up function specification refinement
    #   More systematic thinking is needed.
    def aritherror_inference(self, code, temp=0.2, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        if errors == []:
            print("Aritherror_inference called without error input. To Abort ...")
            exit()

        # only handle one error at a time
        error = errors[0]

        error_trace = error.trace[0]
        errlinenum = error_trace.lines[0]
        errline = error_trace.get_text()
        errexp = error_trace.get_highlights()[0]

        print(f"arithmetic overflow at Line {errlinenum}: {errline}, the expression is {errexp}")

        if errlinenum == -1:
            print("Fail to extract arithmetic overflow errors from error message:")
            exit()

        # TODO: this two instructions should both be used
        # instruction = "Verus reports an error for the statement " + errline + " in line " + errlinenum + " of the following program. Your mission is to add loop invariants so that Verus verification can go through. Specifically, Verus thinks there may be arithmetic overflow or underflow of the expression " + errexp +" in that statement. You can either specify a proper upper bound and a proper lower bound for this expression " + errexp + " as loop invariants, or you can specify lower bounds and upper bounds for every variable involved in this expression. After you add a loop invariant (e.g., E < 10000 as a new loop invariant), please also add an assert right before the loop (e.g., assert(E<10000)). Remember do NOT use Rust-style assert!(..). Please use Verus-style assert(...), without the exclamation mark. Please make sure you add loop invariant, not just assert."

        # Using Rust style assert! actually is good, as they can be removed by Houdini afterwards...
        instruction = (
            "For each variable x involved in the expression `"
            + errexp
            + "' in line "
            + str(errlinenum)
            + " of the following program, please specify a constant lower bound (i.e. x> ...) and a constant upper bound (i.e., x < ...) as a loop invariant and an assert right before the loop (e.g., assert!(N)). If the program does not offer a bound, you can add a constant bound like 10000. Do not miss any variable in `"
            + errexp
            + ", and do NOT add bound information related to any other variables. Please do not change function post-conditions."
        )

        instruction += """
        Response requirements:
        Respond with the verus code only, do not include any explanation.
        You should only add loop invariants, and you should NOT make any other changes to the program.
        """

        examples = []
        # TODO: example 2 expresses bound for the whole expression
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input-aritherr"))):
            if f.endswith(".rs") and f[2] in ["1"]:
                input_file = os.path.join(self.config.example_path, "input-aritherr", f)
                output_file = os.path.join(self.config.example_path, "output-aritherr", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        print("\n[Error-guided inference] instruction:")
        print(instruction)

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    ##Inter Procedural##
    def direct_spec_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        instruction = """Your mission is to add function pre- and post- conditions to the given Rust code in the form of `requires' (for pre-condition) and `ensures' (for post-condition), so that Verus can
        (1) verify all loop invariants and assert specified in the function are guaranteed to be true.
        (2) verify the post-condition is guaranteed to satisfy at the end of its execution whenever the pre-condition is satisfied at the beginning of the function,
        (3) verify that there will be no arithmetic underflow or overflow in the function,
        (4) verify that there will be no array index underflow or overflow in the function,

        Keep in mind that, `requires' indicates what condition should be satisfied before the function's execution, and `ensures' indicates what should be true at the end of the function's execution. Please do not mix these two up.

Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
Please add `requires' and `ensures' at the beginning of every function.
You should never EVER add new variables, NEVER!
You should never change or delete any existing code.
Again, you should NEVER add new variables, NEVER!
"""

        examples = []
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_spec"))):
            if f.endswith(".rs") and f[2] in ["1", "2", "3", "5"]:
                input_file = os.path.join(self.config.example_path, "input_spec", f)
                output_file = os.path.join(self.config.example_path, "output_spec", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    # TODO: need parser support to reject changes beyond require clause
    def direct_require_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        instruction = """Your mission is to add function pre-conditions to the given Rust code in the form of `requires'.

        Your first task is to add `requires' to any implemented function, if it does not already have one.
        If you decide not to add `requires' to a function, please use comment to explain why.
        Do NOT add function post-conditions (i.e., `ensures')!

        Next, to figure out what pre-conditions to put under the `requires' block, please make sure that we
        want to help Verus to
        (1) verify all loop invariants and assert specified in the function are guaranteed to be true.
        (2) verify the post-condition is guaranteed to satisfy at the end of its execution whenever the pre-condition is satisfied at the beginning of the function,
        (3) verify that there will be no arithmetic underflow or overflow in the function,
        (4) verify that there will be no array index underflow or overflow in the function,

        Keep in mind that, `requires' indicates what condition should be satisfied before the function's execution.


Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
Please add `requires' at the beginning of every function! This is a MUST!
You should NOT add any `ensures' for any function.
You should never EVER add new variables, NEVER!
You should never change or delete any existing code.
"""

        print("Direct Require Inference ...")
        examples = []
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_require"))):
            if f.endswith(".rs") and f[2] in ["1", "3", "5"]:
                input_file = os.path.join(self.config.example_path, "input_require", f)
                output_file = os.path.join(self.config.example_path, "output_require", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    ##Inter Procedural##
    def spec2assert_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        if errors == []:
            instruction = """Your mission is to add assert statement right before each function call to reflect every
            callee function's pre-condition. Specifically, every function's pre-condition is specified in the form of
            `requires' at the beginning of the function. These pre-conditions must be satisfied before this function
            executes. You should identify every place a function (e.g., foo()) is called in the given Rust code, and
            add an assert statement right before the call site to reflect foo's pre-condition.

            Here are some principles that you have to follow:
            Response with the Rust code only, do not include any explanation.
            You should never EVER add new variables, NEVER!
            You should never change or delete any existing code.
            Again, you should NEVER add new variables, NEVER!
            """
        else:
            # Get detailed information about which exact function's which exact precondition is violated at which line
            self.logger.info("spec2assert infernece guided by error messages")

            err_calllnnum, err_call, err_prefun, err_precond = [], [], [], []

            for f in errors:
                if f.error == VerusErrorType.PreCondFail:
                    err_calllnnum.append(f.trace[1].lines[0])
                    err_call.append(f.trace[1].get_text())
                    err_prefun.append(f.trace[1].get_highlights()[0].split("(")[0])
                    err_precond.append(f.trace[0].get_highlights()[0])

            instruction = "Verus verification finds potential pre-condition violation(s) at some call site(s). Your mission is to add assert statement(s) right before those call site(s) to reflect those condition(s) that Verus failed to prove. Please do not add assertions that Verus does not complain about. Here is the list of potential violations:\n"

            for i, line in enumerate(err_calllnnum):
                instruction += f"{i+1}) the pre-condition {err_precond[i]} of function {err_prefun[i]} may be violated by the function invocation {err_call[i]} at line {line} of the input file;\n"

            instruction += """
            Here are some principles that you have to follow:
            Response with the Rust code only, do not include any explanation.
            You should never EVER add new variables, NEVER!
            You should never change or delete any existing code.
            Again, you should NEVER add new variables, NEVER!
            """
            print(instruction)

        examples = []
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_spec2a"))):
            if f.endswith(".rs") and f[2] in ["1"]:
                input_file = os.path.join(self.config.example_path, "input_spec2a", f)
                output_file = os.path.join(self.config.example_path, "output_spec2a", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    # Please add loop invariants to reflect the assert inside the loop
    def assert2inv_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        #        instruction = """Your mission is to add loop invariants to the given Rust code so that Verus can prove every assert inside loops to be correct. Specifically, for every assert statement inside a loop like `assert!(E)', please add E as a loop invariant, inserted into the existing invariant block of the loop.

        instruction = """For every loop in the program, check if there exists any assert statement in it like `assert!(E)'. If there is, make sure that `E' is an invariant to that loop (you don't need to change E) and use a comment to explain the invariant you added, as shown by the example. If the assert is inside a nested loop, make sure that E is added as an invariant to every level of the loop. Please do NOT add any other loop invariants. If you choose not to turn an assert! statement into a loop invariant, please use comments to explain why.

Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
You should never EVER add new variables, NEVER!
You should never change or delete any existing code.
Again, you should NEVER add new variables, NEVER!
"""

        examples = []

        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_a2inv"))):
            if f.endswith(".rs") and f[2] in ["1"]:
                input_file = os.path.join(self.config.example_path, "input_a2inv", f)
                output_file = os.path.join(self.config.example_path, "output_a2inv", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    # TODO: need parser support to make sure the changes are not beyond requires and ensures
    # Please add `requires' and `ensures' at the beginning of every function.
    ##Inter Procedural##
    def assert2spec_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        instruction = """
        For every assert!(P) in the given code, carefully read the code right before assert!(P) to see how is the value of P determined. Then, do the following:

        Step 1. If P depends on the return value of an earlier function call, you HAVE TO add a corresponding POST-condition (i.e., `ensures') for that function, so that Verus can prove P is correct. You should find that function's definition in the file and modify that function's declaration. Then, go to Step 3.

        Step 2. If the correctness of P depends on the parameters of the function it is located in, please add a suitable pre-condition (i.e., `requires') for that function, so that Verus can prove P is correct. Then, go to Step 3.

        Step 3. Only AFTER you added pre- or post-condition to a function, add a comment right after this assert! statement with the following format: `//<P> depends on xxx, so I added post-condition xxx to function xx' or `//<P> depends on xxxx, added pre-condition xxx to function xx'. If you did not chang eany function's pre/post-condition, please explain why.

        Pleae do NOT add any pre-condition or post-conditio that is unnecessary.

Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
You should never change or delete any existing code.
"""
        print("[assert2spec] input:")
        print(code)

        examples = []
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_a2spec"))):
            if f.endswith(".rs") and f[2] in ["1", "2", "3"]:
                input_file = os.path.join(self.config.example_path, "input_a2spec", f)
                output_file = os.path.join(self.config.example_path, "output_a2spec", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    ##Inter Procedural##
    def ensurerefine_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        instruction = """Please check every function in the program.

            If a function currently has no ensures block, you should make NO change to this function. Do NOT add ensures to this function.

            If a function's existing ensures block claims something related to the function return value, you need to adjust the function prototype to give a name to the return value through --> (return_variable_name: return_type). For example, given a function `fn foo(x: i32) -> i32', you can change it to be `fn foo(x:i32) -> (ret:i32)', which would allow you to use `ret' to refer to the return value of function foo in its ensures block.

            Do NOT make any other changes to the code.

Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
You should never change or delete any existing code.
You should NOT add ensures, if a function currently does not have ensures.

"""
        examples = []
        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_ensurerefine"))):
            if f.endswith(".rs") and f[2] in ["1", "5"]:
                input_file = os.path.join(self.config.example_path, "input_ensurerefine", f)
                output_file = os.path.join(self.config.example_path, "output_ensurerefine", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    ##Inter Procedural##
    def removeexec_inference(self, code, temp=0, answer_num=1, errors: [VerusError] = None):
        ###This one is not working very well. We should maybe only use it during diagnosis.
        if errors is None:
            errors = []
        system = "You are an experienced formal language programmer. You are very familiar with Verus, which is a tool for verifying the correctness of code written in Rust."

        instruction = """
        Verus does not allow assert, loop invariant, ensures, or requires block to invoke any executable functions, or to access any private field of an object. Please check if any existing assert, loop invariant, ensures, or requires block does such things. Remove those if they do. Please make NO other changes to the program.

        Here are some principles that you have to follow:
Response with the Rust code only, do not include any explanation.
You should never EVER add new variables, NEVER!
You should never change or delete any existing code.

Here is an example of correct function pre and post conditions: \n
"""

        example_file = os.path.join(self.config.example_path, "example_ensurequire.rs")
        example_content = open(example_file).read()

        instruction += example_content

        examples = []

        for f in sorted(os.listdir(os.path.join(self.config.example_path, "input_removeexec"))):
            if f.endswith(".rs") and f[2] in ["1"]:
                input_file = os.path.join(self.config.example_path, "input_removeexec", f)
                output_file = os.path.join(self.config.example_path, "output_removeexec", f)
                input_content = open(input_file).read()
                output_content = open(output_file).read()
                examples.append({"query": input_content, "answer": output_content})

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=answer_num,
            max_tokens=self.config.max_token,
            temp=temp,
        )

    # TODO: to combine with generate_with_hdn later
    def generate(self, code, infer_funcs=None, verbose=True, answer_num=1, errors=None, temp=0):
        """
        generate the first version of proof code
        """
        if errors is None:
            errors = []
        if infer_funcs is None:
            infer_funcs = []
        if len(infer_funcs) == 0:
            infer_funcs = self.infer_funcs

        veval = VEval(code, self.logger)
        veval.eval()
        scores = veval.get_score()

        if scores.is_correct():
            print("Verus succeeded!")
            return code

        for func in infer_funcs:
            self.logger.info(f"Inference with {func.__name__}")
            attempt = 0
            # for each inference function, give 3 attempts to generate code
            while attempt < 3:
                # inference always based on current code, could be based on initial version as an alternative
                codes = func(code, temp, answer_num, errors)
                found = False
                for cand_code in codes:
                    self.logger.info("raw inference output:" + cand_code)
                    might_code = re.findall(
                        r"```rust(.*)```|```verus(.*)```", cand_code, flags=re.DOTALL
                    )
                    if might_code:
                        cand_code = might_code[0][0] if might_code[0][0] else might_code[0][1]
                    if "verus!" in cand_code and not check_syntaxerr_inv(cand_code):
                        # TODO: maybe check_syntaxerr_inv should be replaced with VEval syntax check
                        # TODO: many inter-procedural repair agents need to change pre/post conditions, so I am commenting out code-change-safe check for now
                        # and code_change_is_safe(code, cand_code, self.config.verus_path, self.logger):
                        veval = VEval(cand_code, self.logger)
                        veval.eval()
                        scores = veval.get_score()
                        if scores.is_correct():
                            return cand_code
                        found = True
                        # TODO: we may want to merge, but merging is not very stable now for inter-proc
                        code = cand_code
                        # code = self.hdn.merge_invariant(code, cand_code)
                        veval = VEval(code, self.logger)
                        veval.eval()
                        if veval.get_score().is_correct():
                            print("Verus succeeded!")
                            return code
                if found:
                    break
                else:
                    # if this attempt did not generate any valid code, try again
                    self.logger.info("regenerate...")
                    temp += 0.1  # generate a different one
                    attempt += 1

            if not found:
                self.logger.info(
                    "Inference function " + func.__name__ + "didn't generate valid code."
                )
            # else:
            #    if verbose:
            #        self.logger.info(func.__name__+" produced the following code:")
            #        self.logger.info(code)

        code = remove_redundant_loopinv(code)

        if verbose:
            self.logger.info("Merged inference results:")
            self.logger.info(code)
            self.logger.info("Move on?")
            x = input()
            if "n" in x:
                exit()

        return code

    # Applies all inference functions in infer_funcs one by one
    # With houdini at the end
    def run_new(self, input_file, output_file, infer_funcs=None):
        if infer_funcs is None:
            infer_funcs = []
        content = open(input_file).read()

        veval = VEval(content, self.logger)
        veval.eval()
        failures = veval.get_failures()
        scores = veval.get_score()

        if scores.is_correct():
            self.logger.info("[run_new] Verus succeeded. No more generation needed.")
            with open(output_file, "w") as wf:
                wf.write(content)
                self.logger.info("[run_new] Done!")
                return

        if len(infer_funcs) == 0:
            infer_funcs = self.infer_funcs

        self.logger.info("[run_new] generating proof code...")
        code = self.generate(content, infer_funcs)

        failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=False)
        if len(failures) == 0:
            self.logger.info("[run_new] Verus succeeded. No more refinement needed.")
            with open(output_file, "w") as wf:
                wf.write(hdn_code)
            self.logger.info("[run_new] Succeed!")
        else:
            # os.makedirs(os.path.dirname(output_file), exist_ok=True)
            with open(output_file, "w") as wf:
                wf.write(code)
            self.logger.info("finished [run_new]!")

    # Inter Proc

    # refine function fname in input_file, with every other function unchanged from input_file and old_file
    # input_file was one round of inference result from old_file
    #
    # Different from run_refine_newpre, here,
    #                           we are not starting with a version that is correct intra-procedurally
    #                           other functions have no pre/post conditions
    #                           and we are not supposed to change other functions' pre/post conditions
    # TODO: it is possible that changes to other functions' pre/post conditions are needed ...
    # TODO: I am using direct_require_inference here, but assert2spec in run_refine_newpre
    # return the number of remaining errors

    def run_refine(self, old_file, input_file, output_file, fname):
        old_content = open(old_file).read()
        content = open(input_file).read()

        self.logger.info("[run_refine] checking function ...")

        veval = VEval(content)
        veval.eval()
        failures = veval.get_failures()

        if len(failures) == 0:
            self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
            with open(output_file, "w") as wf:
                wf.write(content)
                self.logger.info("[run_refine] Done!")
                return 0

        # intra-procedural loop invariant and assert refinement
        # In theory, it could change highlight function's spec, but it is unlikely
        # TODO: should we re-generate based on the old_content? something to consider later
        self.logger.info("[run_refine] intra-procedural proof generation and refine")
        code = self.generate(
            content,
            [self.generation.direct_inference, self.generation.constantrefine_inference],
            answer_num=2,
        )

        # merge with baseline file, so as not to change other function's pre/post conditions
        code = merge_with_highlight(old_content, code, fname)

        # merge with the preliminary inference version generated before run_refine
        # both has only made changes to function fname
        code = self.hdn.merge_code(code, content)

        veval = VEval(code)
        veval.eval()
        failures = veval.get_failures()

        if len(failures) == 0:
            self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
            with open(output_file, "w") as wf:
                wf.write(code)
            self.logger.info("[run_refine] Done!")
            return 0

        # 1. use houdini to remove any wrong loop invariant or assert
        # 2. if it still does not work, Houdini will remove post conditions that are not satisfied

        self.logger.info("[run_refine] Debugging w/ Houdini")

        failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=True)

        if len(failures) == 0:
            self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
            with open(output_file, "w") as wf:
                wf.write(hdn_code)
            self.logger.info("[run_refine] Done!")
            return 0

        # 2. if Houdini fails, pre-condition should be strengthened
        # The precondition could fix whatever verification errors, including arithmetic overflow problems
        self.logger.info(
            "[run_refine] Verus failed on Houdini result. Adding function pre-condition ..."
        )
        # Houdini may have removed invariants that could be proved with the new pred-condition added next
        # so, here, I feed the code before houdini
        # TODO: actually, it is possible that we need to strengthen other function's post conditions
        #       but that needs to be very targeted, very careful
        code = self.generate(code, infer_funcs=[self.direct_require_inference])
        # make sure no changes to other functions' spec
        code = merge_with_highlight(content, code, fname)

        # Run Houdini again with the added pre-condition
        failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=True)

        if len(failures) == 0:
            self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
            hdn_code = remove_redundant_req(hdn_code, fname, self.config.verus_path)
            with open(output_file, "w") as wf:
                wf.write(hdn_code)
            self.logger.info("[run_refine] Done!")
            return 0

        else:
            self.logger.info("[run_refine] Verus failed. Let's try some more refinement.")
            self.logger.info(
                "[run_refine] Adding more loop invariants based on the new function precondition."
            )
            code = self.generate(
                code,
                [self.generation.direct_inference, self.generation.constantrefine_inference],
                answer_num=2,
            )
            code = merge_with_highlight(content, code, fname)
            failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=True)
            if len(failures) == 0:
                self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
                with open(output_file, "w") as wf:
                    wf.write(hdn_code)
                self.logger.info("[run_refine] Done!")
                return 0
            else:
                # let's do some debugging
                print("Will start repairing")
                code = self.refinement.repair_veval(hdn_code, max_attempt=3)
                print("Repair is done:")
                print(code)
                code = merge_with_highlight(content, code, fname)
                failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=True)
                if len(failures) == 0:
                    self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
                    with open(output_file, "w") as wf:
                        wf.write(hdn_code)
                    self.logger.info("[run_refine] Done!")
                    return 0

        attempt = 0
        # This is for testing purpose only
        with open("test.rs", "w") as wf:
            wf.write(hdn_code)
        self.logger.info(
            "[run_refine] Written the code before aritherror_inference to a test.rs for later reference!"
        )

        # Debug: to change to 3
        while attempt < 1:
            # check if there are any arithmetic overflow/underflow errors
            arithf = None
            for f in failures:
                if f.error == VerusErrorType.ArithmeticFlow:
                    arithf = f
                    break
            if arithf is None:
                self.logger.info("[run_refine] no arithmetic overflow/underflow error detected.")
                break

            attempt += 1
            # adding loop invariants and assert to fix arithmetic overflow/underflow errors
            code = self.generate(hdn_code, infer_funcs=[self.aritherror_inference], errors=[arithf])
            # add function pre/post condition to support the new invariants/assert if needed
            code = self.generate(code, infer_funcs=[self.assert2spec_inference])
            # TODO: in theory, I may also have added function post conditions which merge_with_highlight would NOT work
            code = merge_with_highlight(content, code, fname)
            failures, hdn_code = self.hdn.run_interproc(code, verbose=True, removPost=True)
            if len(failures) == 0:
                self.logger.info("[run_refine] Verus succeeded. No more refinement needed.")
                hdn_code = remove_redundant_req(hdn_code, fname, self.config.verus_path)
                with open(output_file, "w") as wf:
                    wf.write(hdn_code)
                self.logger.info("[run_refine] Done!")
                return 0

        with open(output_file, "w") as wf:
            wf.write(hdn_code)
        self.logger.info("[run_refine] Done!")

        # TODO: if the only remaining errors are pre-condition errors, we can leave it to the next round ...
        # TODO: or should I?

        for f in failures:
            if (
                not f.error == VerusErrorType.PreCondFail
                and not f.error == VerusErrorType.PreCondFailVecLen
            ):
                self.logger.info("There are still non-pre-condition errors remaining.")
                return 1

        return 0

    # refine function fname in input_file, with every other function unchanged from input_file
    # input_file was Verified, but now may need update as some of its callee functions' pre-condition might have changed
    # it returns the number of non-fname's post conditions that have been changed
    # Different from run_refine,
    #           intput_file was verified before its callee's spec change
    def run_refine_newpre(self, input_file, output_file, fname):
        content = open(input_file).read()

        # log how many lines of other functions' spec are added
        added_ensures = []

        self.logger.info("[run_refine_newpre] checking function ...")

        # 3 attempts
        attempt = 0
        while attempt < 5:
            attempt += 1
            # Every attempt should start from the original input
            code = content

            veval = VEval(code, self.logger)
            veval.eval()
            scores = veval.get_score()
            failures = veval.get_failures()

            if scores.is_correct():
                break

            # If there are verification failures, it must be due to callee's precondition not satisfied

            # Let's first turn callee's preconditions into assert
            self.logger.info(f"[run_refine_newpre] Attempt {attempt} ...")
            self.logger.info(
                "[run_refine_newpre] Adding assert about violated callee preconditions."
            )
            code = self.generate(code, infer_funcs=[self.spec2assert_inference], errors=failures)
            # merge with baseline file, so as not to change other function's pre/post conditions
            code = merge_with_highlight(content, code, fname)

            # Let's try adding loop invariants
            # Using answer==3 here to make sure all the needed are there
            # TODO: sometimes, there is no loop in the program. It is weird to add invoke this ...
            self.logger.info("[run_refine_newpre] Adding loop invariants ...")
            code = self.generate(code, infer_funcs=[self.assert2inv_inference], answer_num=3)
            code = merge_with_highlight(content, code, fname)

            self.logger.info("[run_refine_newpre] Apply Houdini to the latest generations.")
            failures, hdn_code = self.hdn.run_interproc(
                code, verbose=True, removPost=True, considerassert=False
            )
            if len(failures) == 0:
                # We don't immediately overwrite code, as Houdini would remove assert! added by spec2assert, which is still needed for further refinement
                code = hdn_code
                self.logger.info("[run_refine_newpre] Verus succeeded. No more refinement needed.")
                break

            # Let's strengthen the function pre-condition or other function's post-condition
            self.logger.info(
                "[run_refine_newpre] Adding function pre-condition and post-condition if necessary ..."
            )
            code = self.generate(
                code, infer_funcs=[self.assert2spec_inference], answer_num=1, temp=0.8
            )

            # Run Houdini again with the added pre-condition
            # since we just added assert, houdini should not remove them. Those are the asserts that have to be satisfied
            self.logger.info("[run_refine_newpre] Apply Houdini to the latest generations.")
            failures, code = self.hdn.run_interproc(
                code, verbose=True, removPost=True, considerassert=False
            )
            if len(failures) == 0:
                self.logger.info("[run_refine_newpre] Verus succeeded. No more refinement needed.")
                code = remove_redundant_req(code, fname, self.config.verus_path)

                break
            else:
                # This attempt has failed
                if attempt >= 5:
                    with open(output_file, "w") as wf:
                        wf.write(code)
                    self.logger.info(
                        "[run_refine_newpre] Done with 5 attempts. Did not find a correct version."
                    )
                    return added_ensures

        # Now we need to merge carefully, as non-highlight function's post condition may have changed
        correct_unmerged = code
        code = merge_with_highlight(content, code, fname)

        veval = VEval(code, self.logger)
        veval.eval()
        scores = veval.get_score()
        if scores.is_correct():
            # didn't need to change non-highlight functions' prorotype to succeed
            self.logger.info(
                "[run_refine_newpre] Found a correct version w/o changes to other functions' spec."
            )
            with open(output_file, "w") as wf:
                wf.write(code)
            self.logger.info("[run_refine_newpre] Done!")
            return added_ensures
        else:
            self.logger.info(
                "[run_refine_newpre] The correct version requires changes to other functions' spec."
            )

        # Now we need to merge some non-highlight's post conditions in correct_unmerged into code
        # TODO: wish we could do some check for the newensurelines, try and only merge the necessary changes
        code, added_ensures = merge_with_highlight_post(code, correct_unmerged, fname)

        veval = VEval(code, self.logger)
        veval.eval()
        scores = veval.get_score()
        if scores.is_correct():
            self.logger.info(
                "[run_refine_newpre] Found a correct version w/ changes to other functions' spec."
            )
        else:
            self.logger.info(
                "[run_refine_newpre] Warning: something went wrong during merge_with_highlight_post. Verus failed."
            )

        with open(output_file, "w") as wf:
            wf.write(code)
            self.logger.info("[run_refine_newpre] Done!")

        return added_ensures

    ###############Could be more robust than Python, but not used now #####
    def getfun_from_file(self, code, func_name):
        system = "You are an experienced Rust programmer."

        instruction = "Your mission is to identify the function named: "
        instruction += func_name
        instruction += ", and print this function out. Response with the Rust code only, do not include any explanation or comment."

        examples = []

        return self.llm.infer_llm(
            self.config.aoai_generation_model,
            instruction,
            examples,
            code,
            system,
            answer_num=1,
            max_tokens=self.config.max_token,
            temp=0,
        )
