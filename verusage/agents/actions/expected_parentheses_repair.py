"""
Expected Parentheses Repair Action
Repairs VerusErrorType.ExpectedParentheses errors by transforming assert syntax.
Specifically converts: assert(forall|...| condition) by { ... }
                  to: assert forall|...| condition by { ... }
"""

import re
from typing import Any

from veval import VerusError, VerusErrorType

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class ExpectedParenthesesRepairAction(BaseAction):
    """Action to repair expected parentheses errors in assert statements"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair expected parentheses errors by transforming assert(forall|...) syntax to assert forall|...| syntax"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Fix syntax errors where assert(forall|...) should be assert forall|...|"

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Expected parentheses repairs should improve compilation"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the expected parentheses repair action"""
        guidance = params.get("guidance", "")

        # Fix the expected parentheses error
        repaired_code = self._fix_expected_parentheses_error(
            observation.code, observation.error, guidance=guidance
        )

        return self._create_result(
            observation, ActionType.EXPECTED_PARENTHESES_REPAIR, [repaired_code], guidance
        )

    def _fix_expected_parentheses_error(
        self, code: str, error: VerusError, guidance: str = ""
    ) -> str:
        """Fix expected parentheses error by transforming assert syntax"""

        if error.error != VerusErrorType.ExpectedParentheses:
            self.logger.warning(
                f"Expected parentheses repair called for wrong error type: {error.error}"
            )
            return code

        try:
            # Get the error location
            error_trace = error.trace[0] if error.trace else None
            if not error_trace:
                self.logger.warning("No error trace available for expected parentheses error")
                return code

            lines = code.split("\n")
            error_start_line = error_trace.lines[0] - 1  # Convert to 0-based indexing
            error_end_line = error_trace.lines[1] - 1

            self.logger.info(
                f"Fixing expected parentheses error at lines {error_start_line + 1}-{error_end_line + 1}"
            )

            # Find the problematic assert statement
            fixed_lines = []
            i = 0
            while i < len(lines):
                line = lines[i]

                # Check if this line is within the error range and contains assert(forall
                if (
                    error_start_line <= i <= error_end_line
                    and self._is_assert_forall_with_parentheses(line)
                ):
                    # Transform the line
                    fixed_line = self._transform_assert_forall_line(line)
                    if fixed_line != line:
                        self.logger.info(
                            f"Transformed line {i + 1}: '{line.strip()}' -> '{fixed_line.strip()}'"
                        )
                        fixed_lines.append(fixed_line)
                    else:
                        # If we can't fix this specific line, try to find and fix the pattern in the error range
                        fixed_section = self._fix_assert_forall_in_section(
                            lines[error_start_line : error_end_line + 1]
                        )
                        if fixed_section:
                            fixed_lines.extend(lines[:error_start_line])
                            fixed_lines.extend(fixed_section)
                            fixed_lines.extend(lines[error_end_line + 1 :])
                            return "\n".join(fixed_lines)
                        else:
                            fixed_lines.append(line)
                else:
                    fixed_lines.append(line)
                i += 1

            result_code = "\n".join(fixed_lines)

            if result_code != code:
                self.logger.info("Successfully fixed expected parentheses error")
                return result_code
            else:
                self.logger.warning("Could not find assert(forall pattern to fix")
                return code

        except Exception as e:
            self.logger.error(f"Error fixing expected parentheses: {e}")
            return code

    def _is_assert_forall_with_parentheses(self, line: str) -> bool:
        """Check if line contains assert(forall pattern that needs fixing"""
        # Look for assert(forall pattern
        pattern = r"assert\s*\(\s*forall\s*\|"
        return bool(re.search(pattern, line))

    def _transform_assert_forall_line(self, line: str) -> str:
        """Transform assert(forall|...| condition) to assert forall|...| condition"""
        # Pattern to match assert(forall|variables| condition) by { ... }
        # We need to be careful about nested parentheses and pipes

        # First try: assert(forall|...| ...) by - with closing parenthesis
        pattern1 = r"assert\s*\(\s*(forall\s*\|[^|]*\|[^)]*)\)\s*(by\s*\{?)"
        match1 = re.search(pattern1, line)
        if match1:
            forall_part = match1.group(1)
            by_part = match1.group(2)
            # Replace the matched part
            replacement = f"assert {forall_part} {by_part}"
            return re.sub(pattern1, replacement, line)

        # Second try: assert(forall|...| ...) by - without explicit closing parenthesis match
        # This handles cases where the closing paren is at the end before 'by'
        pattern2 = r"assert\s*\(\s*(forall\s*\|[^|]*\|.*?)\)\s*(by(?:\s*\{)?)"
        match2 = re.search(pattern2, line)
        if match2:
            forall_part = match2.group(1)
            by_part = match2.group(2)
            # Replace the matched part
            replacement = f"assert {forall_part} {by_part}"
            return re.sub(pattern2, replacement, line)

        # Third try: handle cases without 'by' keyword
        pattern3 = r"assert\s*\(\s*(forall\s*\|[^|]*\|.*?)\)\s*$"
        match3 = re.search(pattern3, line)
        if match3:
            forall_part = match3.group(1)
            replacement = f"assert {forall_part}"
            return re.sub(pattern3, replacement, line)

        # More complex case: handle multi-line or nested structures
        # Look for assert( at the beginning and try to remove the opening parenthesis
        pattern4 = r"(\s*assert)\s*\(\s*(forall\s*\|)"
        match4 = re.search(pattern4, line)
        if match4:
            prefix = match4.group(1)
            forall_start = match4.group(2)
            # Remove the opening parenthesis after assert
            return re.sub(pattern4, f"{prefix} {forall_start}", line)

        return line

    def _fix_assert_forall_in_section(self, section_lines: list[str]) -> list[str] | None:
        """Fix assert(forall pattern in a section of lines"""
        try:
            section_text = "\n".join(section_lines)

            # Look for assert(forall pattern across multiple lines
            # Pattern to match: assert(forall|...| ... ) by {
            pattern = r"assert\s*\(\s*(forall\s*\|[^|]*\|[^)]*)\)\s*(by\s*\{?)"

            if re.search(pattern, section_text, re.MULTILINE | re.DOTALL):
                # Replace the pattern
                fixed_text = re.sub(
                    pattern, r"assert \1 \2", section_text, flags=re.MULTILINE | re.DOTALL
                )
                if fixed_text != section_text:
                    return fixed_text.split("\n")

            # Try simpler approach: just remove parentheses around forall
            pattern2 = r"(\s*assert)\s*\(\s*(forall\s*\|[^|]*\|)"
            if re.search(pattern2, section_text):
                fixed_text = re.sub(pattern2, r"\1 \2", section_text)
                if fixed_text != section_text:
                    return fixed_text.split("\n")

            return None

        except Exception as e:
            self.logger.error(f"Error fixing assert forall in section: {e}")
            return None

    def _find_matching_closing_paren(self, text: str, start_pos: int) -> int | None:
        """Find the matching closing parenthesis for an opening parenthesis at start_pos"""
        if start_pos >= len(text) or text[start_pos] != "(":
            return None

        paren_count = 1
        pos = start_pos + 1

        while pos < len(text) and paren_count > 0:
            if text[pos] == "(":
                paren_count += 1
            elif text[pos] == ")":
                paren_count -= 1
            pos += 1

        return pos - 1 if paren_count == 0 else None
