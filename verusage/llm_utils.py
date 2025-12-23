"""
LLM Utility Functions
Standalone utilities for calling LLM with various formats.
No dependency on refinement or BaseModel.
"""

import time

from global_config import GlobalConfig
from output_format import SearchReplaceFormatter, apply_search_replace_format


def insert_loop_isolation(code: str) -> str:
    """
    Insert #[verifier::loop_isolation(false)] attribute after verus! macro.

    Args:
        code: Source code to modify

    Returns:
        Modified code with loop isolation attribute
    """
    logger = GlobalConfig.get_logger()

    if not code or not code.strip():
        logger.warning("Empty code provided to insert_loop_isolation")
        return code

    lines = code.splitlines()
    verus_line = -1

    # Find the verus! macro line
    for i, line in enumerate(lines):
        if "verus!" in line.strip():
            verus_line = i
            break

    if verus_line == -1:
        logger.error("No verus! macro found in the code.")
        return code

    # Insert the loop isolation attribute after the verus! line
    loop_isolation_attr = "#[verifier::loop_isolation(false)]"
    lines.insert(verus_line + 1, loop_isolation_attr)

    return "\n".join(lines)


def call_llm_with_diff_format(
    engine: str,
    instruction: str,
    query: str,
    system: str,
    original_code: str = "",
    examples: list = None,
    answer_num: int = 1,
    max_tokens: int = 4096,
    temp: float = 1.0,
) -> list[str]:
    """
    Call LLM with SEARCH/REPLACE format instructions and handle the response.

    This is a standalone function that doesn't depend on refinement.

    Args:
        engine: LLM engine/model name
        instruction: Base instruction for the LLM
        query: The specific query/task
        system: System prompt
        original_code: Original code to apply changes to
        examples: Optional list of examples for few-shot learning (default: [])
        answer_num: Number of responses to generate
        max_tokens: Maximum tokens for response
        temp: Temperature for sampling

    Returns:
        List of modified code strings (successfully applied patches only)
    """
    if examples is None:
        examples = []
    llm = GlobalConfig.get_llm()
    logger = GlobalConfig.get_logger()

    # Add SEARCH/REPLACE format instructions to the query
    search_replace_instructions = SearchReplaceFormatter.get_format_instructions()
    system = system + "\n\n" + search_replace_instructions

    # Log the prompt for debugging
    llm_prompt_dir = GlobalConfig.get_llm_prompt_dir()
    time_stamp = str(time.time())
    (llm_prompt_dir / f"{time_stamp}-input.txt").write_text(
        instruction + "\n\n" + query, encoding="utf-8"
    )

    # Call LLM with examples
    responses = llm.infer_llm(
        engine,
        instruction,
        examples,
        query,
        system,
        answer_num=answer_num,
        max_tokens=max_tokens,
        temp=temp,
    )

    # Process responses using SEARCH/REPLACE format
    modified_codes = []
    for i, response in enumerate(responses):
        (llm_prompt_dir / f"{time_stamp}-output-{i}.txt").write_text(response, encoding="utf-8")

        modified_code, success, message = apply_search_replace_format(original_code, response)
        if success:
            logger.info(f"Successfully applied SEARCH/REPLACE format: {message}")
            modified_codes.append(modified_code)
        else:
            # Discard the response if it fails to apply the SEARCH/REPLACE format
            logger.warning(f"Failed to apply SEARCH/REPLACE format: {message}")

    return modified_codes


def call_llm_with_full_return(
    engine: str,
    instruction: str,
    query: str,
    system: str,
    answer_num: int = 1,
    max_tokens: int = 4096,
    temp: float = 1.0,
) -> list[str]:
    """
    Call LLM expecting full code return (not diff format).

    This is a standalone function that doesn't depend on refinement or examples.

    Args:
        engine: LLM engine/model name
        instruction: Base instruction for the LLM
        query: The specific query/task
        system: System prompt
        answer_num: Number of responses to generate
        max_tokens: Maximum tokens for response
        temp: Temperature for sampling

    Returns:
        List of LLM responses
    """
    llm = GlobalConfig.get_llm()

    # Add standard instructions
    query += "\n\nDo not add `proof { ... }` to in the body of the `proof fn` function and `spec fn` function."
    query += "\n\nPlease return the full code with the changes applied. The code should be surrounded by ```verus and ```."

    # Log the prompt for debugging
    llm_prompt_dir = GlobalConfig.get_llm_prompt_dir()
    (llm_prompt_dir / f"{time.time()}.txt").write_text(instruction + "\n\n" + query)

    # Call LLM (no examples)
    return llm.infer_llm(
        engine,
        instruction,
        [],  # No examples
        query,
        system,
        answer_num=answer_num,
        max_tokens=max_tokens,
        temp=temp,
    )
