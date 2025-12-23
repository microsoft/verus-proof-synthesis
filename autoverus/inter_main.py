# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #

# Very preliminary inter-procedural version#

import argparse
import json
import logging
import os
import re

from utils_inter import highlight_code_by_func, merge_with_highlight, merge_with_highlight_post
from veval import verus

from utils import AttrDict


def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Verus Copilot (InterProcedural)")
    parser.add_argument("--config", default="config.json", help="Path to config file")
    parser.add_argument("--mode", default="gen", help="Mode to run in (gen, testrun, testRefine)")
    parser.add_argument("--input", default="input.rs", help="Path to input file")
    parser.add_argument("--input2", default="input.rs", help="Path to the second input file")
    parser.add_argument("--output", default="output.rs", help="Path to output file")
    parser.add_argument("--oprefix", default="tmp", help="prefix to intermediate files")
    parser.add_argument("--fname", default="main", help="The function to focus on")
    args = parser.parse_args()

    # Set log level
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
    logger = logging.getLogger("Assitant")

    # logger write to file
    fh = logging.FileHandler("log1.txt", mode="w")
    fh.setFormatter(
        logging.Formatter("%(asctime)s %(levelname)s: %(message)s", datefmt="%Y-%m-%d %H:%M:%S")
    )
    logger.addHandler(fh)

    # Check if config file exists
    if not os.path.isfile(args.config):
        logger.error("Config file does not exist")
        return
    config = json.load(open(args.config))
    config = AttrDict(config)

    verus.set_verus_path(config.verus_path)

    # Set up inference engine
    from inter_generation import interGeneration

    runner = interGeneration(config, logger)

    if args.mode == "testRefine":
        runner.run_refine(args.input, args.input2, args.output, args.fname)
        exit()

    if args.mode == "testrun":
        runner.run(args.input, args.output)
        exit()

    # Generating initial round of spec and invariant for the whole file
    # This is used as a reference
    # logger.info("Step 0: first round for the whole file ... @ " + args.output)
    # runner.run_new(args.input, args.output)

    logger.info("Step 0: Splitting the whole file into per-function files ...")
    # TODO: should be replaced with a parser-based implementation
    fun_files, fnames = highlight_code_by_func(open(args.input).read(), args.oprefix, True)
    # print("The input file has been split to per-function files. Continue?")
    # x = input()
    # if "n" in x:
    #    exit()

    logger.info("Step 1: preliminary proof generation for each function ...")
    fun_files1 = []
    fun_files1_merged = []
    for i, f in enumerate(fun_files):
        print(f)
        of = re.sub(r".rs", "v1.rs", f)
        fun_files1.append(of)
        # A preliminary inference round. ensurerefine helps add return value for return ensure
        runner.run_new(f, of, [runner.generation.direct_inference, runner.ensurerefine_inference])
        off = re.sub(r".rs", "v1_merged.rs", f)
        fun_files1_merged.append(off)
        # In preliminary round, one function's generation is not allowed to change other functions' spec
        # TODO: should be replaced with a parser-based implementation
        mergedc = merge_with_highlight(open(f).read(), open(of).read(), fnames[i])
        with open(off, "w") as woff:
            woff.write(mergedc)

    logger.info("Step 2: debugging and refinement for each function ...")

    files2 = []
    allpass = True
    for i, f in enumerate(fun_files1):
        print("Checking " + f)
        of = re.sub(r"v1.rs", "v2.rs", f)
        files2.append(of)
        errornum = 0
        errornum = runner.run_refine(fun_files[i], fun_files1_merged[i], of, fnames[i])
        if errornum > 0:
            allpass = False
        # The result of run_refine is already merged, hence guarantee not to change functions other than fnames[i]

    if not allpass:
        print("Failed to generate provable versions for at least one function.")
        print("To exit ...")
        exit()

    # generating next round of spec and invariant for each function separately
    logger.info("Step 3: Compose per-function files together and decompose again ...")

    file3 = re.sub(r".rs", "_v2.rs", args.output)
    newcode = open(files2[0]).read()
    for i, _ in enumerate(files2):
        print("Merging function " + fnames[i])
        oldcode = newcode
        # TODO: should be replaced with a parser-based implementation
        newcode = merge_with_highlight(oldcode, open(files2[i]).read(), fnames[i])
    with open(file3, "w") as of:
        of.write(newcode)

    fun_files, fnames = highlight_code_by_func(newcode, args.oprefix + "2", True)

    # TODO: would be good to know which functions have new pre/post conditions since last round

    logger.info("Step 4: refine each function with updated callee pre-conditions...")

    files4 = []
    changes_to_others = []
    for i, f in enumerate(fun_files):
        print("Function " + fnames[i])
        of = re.sub(r".rs", "v3.rs", f)
        files4.append(of)
        newensures = runner.run_refine_newpre(fun_files[i], of, fnames[i])
        changes_to_others.append(newensures)

    # Now, we finished this round, but some functions' post or pre condition may have changed
    # which may trigger the next round
    # TODO: we should have a working queue ...
    file4 = re.sub(r".rs", "_v3.rs", args.output)
    newcode = open(files4[0]).read()
    for i, _ in enumerate(files4):
        print("Merging function " + fnames[i])
        oldcode = newcode
        newcode = merge_with_highlight(oldcode, open(files4[i]).read(), fnames[i])
    for i, _ in enumerate(files4):
        if len(changes_to_others[i]) > 0:
            # TODO: should be replaced with a parser-based implementation
            newcode, newensurelines = merge_with_highlight_post(
                newcode, open(files4[i]).read(), fnames[i]
            )
            print(f"Merging {newensurelines} post-condition changes made by " + fnames[i])
    print("New file generated in " + file4)
    with open(file4, "w") as of:
        of.write(newcode)


if __name__ == "__main__":
    main()
    # evaluation("rag_debug_gpt4_10_1")
