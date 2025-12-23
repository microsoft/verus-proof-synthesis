"""
Output format utilities for refinement agents.
Defines and processes SEARCH/REPLACE formats that are easy for LLMs to generate.
"""

import re

from utils import ERROR_SUFFIX


class SearchReplaceOperation:
    """Represents a single SEARCH/REPLACE operation."""

    def __init__(self, search_text: str, replace_text: str):
        self.search_text = search_text
        self.replace_text = replace_text


class SearchReplaceFormatter:
    """Handles SEARCH/REPLACE format for LLM output."""

    @staticmethod
    def get_format_instructions() -> str:
        """Returns instructions for LLMs on how to use the SEARCH/REPLACE format."""
        return """
Response format: Use the following SEARCH/REPLACE format to specify your changes.

Every *SEARCH/REPLACE* edit must use this format:
1. The start of search block: <<<<<<< SEARCH
2. A contiguous chunk of lines to search for in the existing source code
3. The dividing line: =======
4. The lines to replace into the source code
5. The end of the replace block: >>>>>>> REPLACE

Examples:

```rust
<<<<<<< SEARCH
    assert(y > x);
=======
    assert(y > x) by {
        assert(x > 0);
    }
>>>>>>> REPLACE
```

```rust
<<<<<<< SEARCH
    proof fn rev_map_union(s1: Set<int>, s2: Set<int>, x: int, f: spec_fn(int) -> int)
        requires
            s1.map(f).union(s2.map(f)).contains(x)
        ensures
            exists |y:int| s1.union(s2).contains(y) && f(y) == x
    {
    }
=======
    proof fn rev_map_union(s1: Set<int>, s2: Set<int>, x: int, f: spec_fn(int) -> int)
        requires
            s1.map(f).union(s2.map(f)).contains(x)
        ensures
            exists |y:int| s1.union(s2).contains(y) && f(y) == x
    {
        if (s1.map(f).contains(x)) {
        } else {
        }
    }
>>>>>>> REPLACE
```

```rust
<<<<<<< SEARCH
    let v = Vec::new();
=======
    let v = Vec::new();
    proof {
        assert(v@.len() == 0);
    }
>>>>>>> REPLACE
```

Rules:
1. The *SEARCH/REPLACE* edit REQUIRES PROPER INDENTATION
2. If you want to add '        print(x)', write it with all spaces
3. Use exact text matching - be precise with whitespace and indentation
4. Include enough context in SEARCH to uniquely identify the location
5. Multiple SEARCH/REPLACE blocks are allowed
6. To delete code, use empty REPLACE section
7. To insert code, include the surrounding context in SEARCH
8. Use ```rust``` to wrap the code. DO NOT use any -/+ symbols in the beginning of the lines.

Only specify the changes needed to fix the error. The search text should be exact and unique.
Plus, before generating the SEARCH/REPLACE blocks, please write an explanation of what changes you are making and why.
"""

    @staticmethod
    def parse_search_replace_response(response: str) -> list[SearchReplaceOperation]:
        """Parse LLM response in SEARCH/REPLACE format into SearchReplaceOperation objects."""
        operations = []

        # Remove outer code block markers if present
        response = re.sub(
            r"```(?:rust|verus|python)?\s*\n?|```\s*$", "", response, flags=re.MULTILINE
        )

        # Pattern for SEARCH/REPLACE blocks
        # Accept 7 or more equal signs to handle LLM variations
        pattern = r"<{7,}\s*SEARCH\s*\n(.*?)\n={7,}\s*\n(.*?)\n>{7,}\s*REPLACE"

        for match in re.finditer(pattern, response, re.DOTALL):
            search_text = match.group(1)
            replace_text = match.group(2)
            operations.append(SearchReplaceOperation(search_text, replace_text))

        return operations

    @staticmethod
    def apply_search_replace_operations(
        original_code: str, operations: list[SearchReplaceOperation]
    ) -> str:
        """Apply SEARCH/REPLACE operations to the original code and return the modified code."""
        modified_code = original_code

        for op in operations:
            modified_code = SearchReplaceFormatter._apply_single_operation(modified_code, op)

        return modified_code

    @staticmethod
    def _apply_single_operation(code: str, op: SearchReplaceOperation) -> str:
        """Apply a single SEARCH/REPLACE operation with priority-based matching."""
        # Check for direct string match first
        if op.search_text in code:
            # For multiple matches, prioritize ERROR_SUFFIX lines
            matches = SearchReplaceFormatter._find_all_matches(code, op.search_text)
            if len(matches) > 1:
                # Find the best match to replace (prioritize ERROR_SUFFIX lines)
                best_match = SearchReplaceFormatter._select_best_match(code, matches)
                return SearchReplaceFormatter._replace_at_position(code, op, best_match)
            else:
                # Single match - direct replacement
                return code.replace(op.search_text, op.replace_text, 1)
        else:
            # Try with normalized whitespace for more flexibility
            result = SearchReplaceFormatter._apply_with_normalized_whitespace(code, op)
            if result != code:
                return result

            # Try with fuzzy whitespace (ignoring blank lines)
            return SearchReplaceFormatter._apply_with_fuzzy_whitespace(code, op)

    @staticmethod
    def _find_all_matches(code: str, search_text: str) -> list[int]:
        """Find all starting positions of search_text in code."""
        matches = []
        start = 0
        while True:
            pos = code.find(search_text, start)
            if pos == -1:
                break
            matches.append(pos)
            start = pos + 1
        return matches

    @staticmethod
    def _select_best_match(code: str, matches: list[int]) -> int:
        """Select the best match position, prioritizing ERROR_SUFFIX lines."""
        code_lines = code.splitlines(keepends=True)
        line_starts = [0]
        for line in code_lines[:-1]:
            line_starts.append(line_starts[-1] + len(line))

        # Check each match and prioritize those on ERROR_SUFFIX lines
        error_suffix_matches = []
        regular_matches = []

        for match_pos in matches:
            # Find which line this match is on
            line_idx = 0
            for i, line_start in enumerate(line_starts):
                if match_pos >= line_start:
                    line_idx = i
                else:
                    break

            # Check if this line contains ERROR_SUFFIX
            if line_idx < len(code_lines) and ERROR_SUFFIX in code_lines[line_idx]:
                error_suffix_matches.append(match_pos)
            else:
                regular_matches.append(match_pos)

        # Return the first ERROR_SUFFIX match if any, otherwise the first regular match
        if error_suffix_matches:
            return error_suffix_matches[0]
        else:
            return regular_matches[0] if regular_matches else matches[0]

    @staticmethod
    def _replace_at_position(code: str, op: SearchReplaceOperation, position: int) -> str:
        """Replace search_text with replace_text at the specified position."""
        before = code[:position]
        after = code[position + len(op.search_text) :]
        return before + op.replace_text + after

    @staticmethod
    def _apply_with_normalized_whitespace(code: str, op: SearchReplaceOperation) -> str:
        """Apply operation with normalized whitespace matching."""
        search_lines = op.search_text.splitlines()
        code_lines = code.splitlines()

        # Find all potential matches with normalized whitespace
        matches = []
        for i in range(len(code_lines) - len(search_lines) + 1):
            match = True
            for j, search_line in enumerate(search_lines):
                if search_line.strip() != code_lines[i + j].strip():
                    match = False
                    break
            if match:
                matches.append(i)

        if not matches:
            return code

        # Select the best match (prioritize ERROR_SUFFIX lines)
        best_match_idx = SearchReplaceFormatter._select_best_line_match(
            code_lines, matches, search_lines
        )

        # Apply the replacement at the best match
        return SearchReplaceFormatter._replace_at_line_index(code_lines, op, best_match_idx)

    @staticmethod
    def _select_best_line_match(
        code_lines: list[str], matches: list[int], search_lines: list[str]
    ) -> int:
        """Select the best line match, prioritizing ERROR_SUFFIX lines."""
        error_suffix_matches = []
        regular_matches = []

        for match_idx in matches:
            # Check if any line in this match contains ERROR_SUFFIX
            has_error_suffix = False
            for j in range(len(search_lines)):
                if match_idx + j < len(code_lines) and ERROR_SUFFIX in code_lines[match_idx + j]:
                    has_error_suffix = True
                    break

            if has_error_suffix:
                error_suffix_matches.append(match_idx)
            else:
                regular_matches.append(match_idx)

        # Return the first ERROR_SUFFIX match if any, otherwise the first regular match
        if error_suffix_matches:
            return error_suffix_matches[0]
        else:
            return regular_matches[0] if regular_matches else matches[0]

    @staticmethod
    def _replace_at_line_index(
        code_lines: list[str], op: SearchReplaceOperation, line_index: int
    ) -> str:
        """Replace lines starting at line_index with the replacement text."""
        search_lines = op.search_text.splitlines()

        # Preserve the indentation of the first line
        base_indent = len(code_lines[line_index]) - len(code_lines[line_index].lstrip())

        # Prepare replacement lines with proper indentation
        replace_lines = op.replace_text.splitlines()
        if replace_lines:
            # For the first line, use the existing indentation
            if replace_lines[0].strip():
                replace_lines[0] = " " * base_indent + replace_lines[0].lstrip()

            # For subsequent lines, preserve their relative indentation
            for k in range(1, len(replace_lines)):
                if replace_lines[k].strip():  # Don't modify empty lines
                    # Calculate relative indentation from original
                    original_indent = len(replace_lines[k]) - len(replace_lines[k].lstrip())
                    replace_lines[k] = (
                        " " * (base_indent + original_indent) + replace_lines[k].lstrip()
                    )

        # Replace the lines
        code_lines[line_index : line_index + len(search_lines)] = replace_lines
        return "\n".join(code_lines)

    @staticmethod
    def _apply_operations_with_priority(
        code: str, operations: list[SearchReplaceOperation], error_suffix_lines: set
    ) -> str:
        """Apply SEARCH/REPLACE operations with priority for lines that originally had ERROR_SUFFIX."""
        modified_code = code

        for op in operations:
            modified_code = SearchReplaceFormatter._apply_single_operation_with_priority(
                modified_code, op, error_suffix_lines
            )

        return modified_code

    @staticmethod
    def _apply_single_operation_with_priority(
        code: str, op: SearchReplaceOperation, error_suffix_lines: set
    ) -> str:
        """Apply a single SEARCH/REPLACE operation with priority for originally ERROR_SUFFIX lines."""
        # Check for direct string match first
        if op.search_text in code:
            # For multiple matches, prioritize lines that originally had ERROR_SUFFIX
            matches = SearchReplaceFormatter._find_all_matches(code, op.search_text)
            if len(matches) > 1:
                # Find the best match to replace (prioritize originally ERROR_SUFFIX lines)
                best_match = SearchReplaceFormatter._select_best_match_with_priority(
                    code, matches, error_suffix_lines
                )
                return SearchReplaceFormatter._replace_at_position(code, op, best_match)
            else:
                # Single match - direct replacement
                return code.replace(op.search_text, op.replace_text, 1)
        else:
            # Try with normalized whitespace for more flexibility
            result = SearchReplaceFormatter._apply_with_normalized_whitespace_priority(
                code, op, error_suffix_lines
            )
            if result != code:
                return result

            # Try with fuzzy whitespace (ignoring blank lines)
            return SearchReplaceFormatter._apply_with_fuzzy_whitespace(code, op, error_suffix_lines)

    @staticmethod
    def _select_best_match_with_priority(
        code: str, matches: list[int], error_suffix_lines: set
    ) -> int:
        """Select the best match position, prioritizing lines that originally had ERROR_SUFFIX."""
        code_lines = code.splitlines(keepends=True)
        line_starts = [0]
        for line in code_lines[:-1]:
            line_starts.append(line_starts[-1] + len(line))

        # Check each match and prioritize those on originally ERROR_SUFFIX lines
        priority_matches = []
        regular_matches = []

        for match_pos in matches:
            # Find which line this match is on
            line_idx = 0
            for i, line_start in enumerate(line_starts):
                if match_pos >= line_start:
                    line_idx = i
                else:
                    break

            # Check if this line originally had ERROR_SUFFIX (1-based line numbers)
            if (line_idx + 1) in error_suffix_lines:
                priority_matches.append(match_pos)
            else:
                regular_matches.append(match_pos)

        # Return the first priority match if any, otherwise the first regular match
        if priority_matches:
            return priority_matches[0]
        else:
            return regular_matches[0] if regular_matches else matches[0]

    @staticmethod
    def _apply_with_normalized_whitespace_priority(
        code: str, op: SearchReplaceOperation, error_suffix_lines: set
    ) -> str:
        """Apply operation with normalized whitespace matching and priority for originally ERROR_SUFFIX lines."""
        search_lines = op.search_text.splitlines()
        code_lines = code.splitlines()

        # Find all potential matches with normalized whitespace
        matches = []
        for i in range(len(code_lines) - len(search_lines) + 1):
            match = True
            for j, search_line in enumerate(search_lines):
                if search_line.strip() != code_lines[i + j].strip():
                    match = False
                    break
            if match:
                matches.append(i)

        if not matches:
            return code

        # Select the best match (prioritize originally ERROR_SUFFIX lines)
        best_match_idx = SearchReplaceFormatter._select_best_line_match_with_priority(
            code_lines, matches, search_lines, error_suffix_lines
        )

        # Apply the replacement at the best match
        return SearchReplaceFormatter._replace_at_line_index(code_lines, op, best_match_idx)

    @staticmethod
    def _select_best_line_match_with_priority(
        code_lines: list[str], matches: list[int], search_lines: list[str], error_suffix_lines: set
    ) -> int:
        """Select the best line match, prioritizing lines that originally had ERROR_SUFFIX."""
        priority_matches = []
        regular_matches = []

        for match_idx in matches:
            # Check if any line in this match originally had ERROR_SUFFIX
            has_priority = False
            for j in range(len(search_lines)):
                if (
                    match_idx + j < len(code_lines) and (match_idx + j + 1) in error_suffix_lines
                ):  # 1-based line numbers
                    has_priority = True
                    break

            if has_priority:
                priority_matches.append(match_idx)
            else:
                regular_matches.append(match_idx)

        # Return the first priority match if any, otherwise the first regular match
        if priority_matches:
            return priority_matches[0]
        else:
            return regular_matches[0] if regular_matches else matches[0]

    @staticmethod
    def _find_fuzzy_matches(code: str, op: SearchReplaceOperation) -> list[tuple[int, int]]:
        """Find all fuzzy matches (ignoring blank lines). Returns list of (start_line_idx, end_line_idx)."""
        search_lines = op.search_text.splitlines()
        code_lines = code.splitlines()

        # Helper to check if a line is blank
        def is_blank(s):
            return not s.strip()

        matches = []

        for i in range(len(code_lines)):
            # Optimization: Quick check first line
            # Find first non-blank search line
            first_nb_search_idx = 0
            while first_nb_search_idx < len(search_lines) and is_blank(
                search_lines[first_nb_search_idx]
            ):
                first_nb_search_idx += 1

            if first_nb_search_idx >= len(search_lines):
                # Search block is all blank? Should have matched by now or is invalid.
                continue

            # If current code line is blank, it can't be the start of a non-blank match
            if is_blank(code_lines[i]):
                continue

            if code_lines[i].strip() != search_lines[first_nb_search_idx].strip():
                continue

            # Potential match started. Verify the rest.
            c_idx = i
            s_idx = first_nb_search_idx
            match = True
            match_end_idx = i

            while s_idx < len(search_lines):
                # Skip blank lines in search
                if is_blank(search_lines[s_idx]):
                    s_idx += 1
                    continue

                # Skip blank lines in code
                while c_idx < len(code_lines) and is_blank(code_lines[c_idx]):
                    c_idx += 1

                if c_idx >= len(code_lines):
                    match = False
                    break

                if code_lines[c_idx].strip() != search_lines[s_idx].strip():
                    match = False
                    break

                match_end_idx = c_idx
                c_idx += 1
                s_idx += 1

            if match:
                matches.append((i, match_end_idx))

        return matches

    @staticmethod
    def _apply_with_fuzzy_whitespace(
        code: str, op: SearchReplaceOperation, error_suffix_lines: set = None
    ) -> str:
        """Apply operation with fuzzy whitespace matching (ignoring blank lines)."""
        matches = SearchReplaceFormatter._find_fuzzy_matches(code, op)

        if not matches:
            return code

        # Select best match
        best_match = matches[0]

        if error_suffix_lines:
            # Prioritize matches that touch error lines
            for start, end in matches:
                # Check if any line in range [start+1, end+1] is in error_suffix_lines
                is_priority = False
                for line_num in range(start + 1, end + 2):
                    if line_num in error_suffix_lines:
                        is_priority = True
                        break
                if is_priority:
                    best_match = (start, end)
                    break

        start_idx, end_idx = best_match
        return SearchReplaceFormatter._replace_range(code.splitlines(), op, start_idx, end_idx)

    @staticmethod
    def _replace_range(
        code_lines: list[str], op: SearchReplaceOperation, start_idx: int, end_idx: int
    ) -> str:
        """Replace lines from start_idx to end_idx (inclusive) with replacement text."""
        # Preserve the indentation of the first line
        base_indent = len(code_lines[start_idx]) - len(code_lines[start_idx].lstrip())

        # Prepare replacement lines with proper indentation
        replace_lines = op.replace_text.splitlines()
        if replace_lines:
            # For the first line, use the existing indentation
            if replace_lines[0].strip():
                replace_lines[0] = " " * base_indent + replace_lines[0].lstrip()

            # For subsequent lines, preserve their relative indentation
            for k in range(1, len(replace_lines)):
                if replace_lines[k].strip():  # Don't modify empty lines
                    # Calculate relative indentation from original replacement text
                    original_indent = len(replace_lines[k]) - len(replace_lines[k].lstrip())
                    replace_lines[k] = (
                        " " * (base_indent + original_indent) + replace_lines[k].lstrip()
                    )

        # Replace the lines
        code_lines[start_idx : end_idx + 1] = replace_lines
        return "\n".join(code_lines)

    @staticmethod
    def validate_operations(
        original_code: str, operations: list[SearchReplaceOperation]
    ) -> tuple[bool, str]:
        """Validate that SEARCH/REPLACE operations can be safely applied."""
        for i, op in enumerate(operations):
            if op.search_text not in original_code:
                # Try with normalized whitespace
                search_lines = op.search_text.splitlines()
                code_lines = original_code.splitlines()

                found = False
                for j in range(len(code_lines) - len(search_lines) + 1):
                    match = True
                    for k, search_line in enumerate(search_lines):
                        if search_line.strip() != code_lines[j + k].strip():
                            match = False
                            break
                    if match:
                        found = True
                        break

                if not found:
                    # Try fuzzy match
                    fuzzy_matches = SearchReplaceFormatter._find_fuzzy_matches(original_code, op)
                    if not fuzzy_matches:
                        return False, f"SEARCH block {i+1} not found: '{op.search_text[:50]}...'"

        return True, "Valid"


def apply_search_replace_format(original_code: str, llm_response: str) -> tuple[str, bool, str]:
    """
    Apply SEARCH/REPLACE format response to original code.

    Returns:
        tuple: (modified_code, success, error_message)
    """
    code, success, message = _apply_search_replace_format(original_code, llm_response)
    if not success:
        # For retry, clean ERROR_SUFFIX from both code and response for matching,
        # but track which lines originally had ERROR_SUFFIX for priority
        error_suffix_lines = _get_error_suffix_line_numbers(original_code)
        clean_code = _clean_error_suffix(original_code)
        clean_llm_response = _clean_error_suffix(llm_response)

        # Retry with cleaned code and response, but pass priority information
        code, success, message = _apply_search_replace_format_with_priority(
            clean_code, clean_llm_response, error_suffix_lines
        )

    # Clean ERROR_SUFFIX from the final result if successful
    if success:
        code = _clean_error_suffix(code)

    return code, success, message


def _clean_error_suffix(code: str) -> str:
    """Remove ERROR_SUFFIX from the code after successful replacement."""
    return code.replace(" " + ERROR_SUFFIX, "").replace(ERROR_SUFFIX, "")


def _get_error_suffix_line_numbers(code: str) -> set:
    """Get the line numbers (1-based) that contain ERROR_SUFFIX."""
    lines = code.splitlines()
    error_suffix_lines = set()
    for i, line in enumerate(lines):
        if ERROR_SUFFIX in line:
            error_suffix_lines.add(i + 1)  # 1-based line numbers
    return error_suffix_lines


def _apply_search_replace_format_with_priority(
    original_code: str, llm_response: str, error_suffix_lines: set
) -> tuple[str, bool, str]:
    """Apply SEARCH/REPLACE format with priority information for lines that originally had ERROR_SUFFIX."""
    try:
        operations = SearchReplaceFormatter.parse_search_replace_response(llm_response)

        if not operations:
            # If no SEARCH/REPLACE operations found, try to extract code blocks as fallback
            code_blocks = re.findall(r"```(?:rust|verus)?\s*\n(.*?)```", llm_response, re.DOTALL)
            if code_blocks:
                extracted_code = code_blocks[0].strip()
                # Safety check: reject if extracted code contains SEARCH/REPLACE markers
                if re.search(
                    r"<{7,}\s*SEARCH|={7,}\s*$|>{7,}\s*REPLACE", extracted_code, re.MULTILINE
                ):
                    return (
                        original_code,
                        False,
                        "Extracted code contains SEARCH/REPLACE markers - rejecting",
                    )
                return extracted_code, True, "Fallback to code block extraction"
            return original_code, False, "No SEARCH/REPLACE operations or code blocks found"

        # Validate operations
        valid, message = SearchReplaceFormatter.validate_operations(original_code, operations)
        if not valid:
            return original_code, False, f"Invalid SEARCH/REPLACE operations: {message}"

        # Apply operations with priority for originally ERROR_SUFFIX lines
        modified_code = SearchReplaceFormatter._apply_operations_with_priority(
            original_code, operations, error_suffix_lines
        )

        # Safety check: if result still contains SEARCH/REPLACE markers, discard it
        if re.search(r"<{7,}\s*SEARCH|={7,}\s*$|>{7,}\s*REPLACE", modified_code, re.MULTILINE):
            return (
                original_code,
                False,
                "Result contains SEARCH/REPLACE markers - discarding malformed output",
            )

        return (
            modified_code,
            True,
            f"Applied {len(operations)} SEARCH/REPLACE operations with priority",
        )

    except Exception as e:
        return original_code, False, f"Error processing SEARCH/REPLACE format: {str(e)}"


def _apply_search_replace_format(original_code: str, llm_response: str) -> tuple[str, bool, str]:
    try:
        operations = SearchReplaceFormatter.parse_search_replace_response(llm_response)

        if not operations:
            # If no SEARCH/REPLACE operations found, try to extract code blocks as fallback
            code_blocks = re.findall(r"```(?:rust|verus)?\s*\n(.*?)```", llm_response, re.DOTALL)
            if code_blocks:
                extracted_code = code_blocks[0].strip()
                # Safety check: reject if extracted code contains SEARCH/REPLACE markers
                if re.search(
                    r"<{7,}\s*SEARCH|={7,}\s*$|>{7,}\s*REPLACE", extracted_code, re.MULTILINE
                ):
                    return (
                        original_code,
                        False,
                        "Extracted code contains SEARCH/REPLACE markers - rejecting",
                    )
                return extracted_code, True, "Fallback to code block extraction"
            return original_code, False, "No SEARCH/REPLACE operations or code blocks found"

        # Validate operations
        valid, message = SearchReplaceFormatter.validate_operations(original_code, operations)
        if not valid:
            return original_code, False, f"Invalid SEARCH/REPLACE operations: {message}"

        # Apply operations
        modified_code = SearchReplaceFormatter.apply_search_replace_operations(
            original_code, operations
        )

        # Safety check: if result still contains SEARCH/REPLACE markers, discard it
        if re.search(r"<{7,}\s*SEARCH|={7,}\s*$|>{7,}\s*REPLACE", modified_code, re.MULTILINE):
            return (
                original_code,
                False,
                "Result contains SEARCH/REPLACE markers - discarding malformed output",
            )

        return modified_code, True, f"Applied {len(operations)} SEARCH/REPLACE operations"

    except Exception as e:
        return original_code, False, f"Error processing SEARCH/REPLACE format: {str(e)}"


# Backward compatibility - keeping the old names as aliases
DiffFormatter = SearchReplaceFormatter
apply_diff_format = apply_search_replace_format
