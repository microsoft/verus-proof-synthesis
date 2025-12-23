"""
Syntax Repair Action
Repairs compilation errors including type errors, unexpected proof blocks, Rust assert errors, and generic syntax errors.
"""

from typing import Any

from veval import VerusError, VerusErrorType, VEval

from ..shared_types import generate_search_replace_diff
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation

# Global history: maps error_pattern -> list of (diff, success)
_SYNTAX_REPAIR_HISTORY: dict[str, list[tuple[str, bool]]] = {}


class SyntaxRepairAction(BaseAction):
    """Action to repair compilation errors and syntax issues"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair compilation errors including type errors, unexpected proof blocks, Rust assert errors, and generic syntax errors"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain what compilation errors need to be fixed and how to resolve them while preserving the intended functionality."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Syntax repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the syntax repair action"""
        guidance = params.get("guidance", "")
        max_attempts = params.get("max_attempts", 5)

        # Use the comprehensive syntax repair implementation
        repaired_code = self._repair_compilation_errors(
            observation.code, observation.error, guidance=guidance, max_attempts=max_attempts
        )

        return self._create_result(observation, ActionType.SYNTAX_REPAIR, [repaired_code], guidance)

    def _repair_compilation_errors(
        self, code: str, verus_error: VerusError, guidance: str = "", max_attempts: int = 3
    ) -> str:
        """Repair compilation errors in the code"""
        veval = VEval(code, self.logger)
        veval.eval()
        score = veval.get_score()

        if not score.compilation_error:
            return code

        attempt = 0
        current_code = code
        direct_use_llm = False

        while attempt < max_attempts:
            attempt += 1
            self.logger.info(f"Syntax repair attempt {attempt}/{max_attempts}")

            # Get all compilation failures
            veval = VEval(current_code, self.logger)
            veval.eval()
            failures = veval.get_failures()

            if not failures:
                self.logger.info("No compilation errors found")
                return current_code

            # Get the first compilation error to fix
            error = self._get_one_compilation_failure(failures)
            if not error:
                self.logger.info("No fixable compilation errors found")
                return current_code

            self.logger.info(f"Working on compilation error: {error.error}")

            # Try to fix the specific error type
            old_code = current_code
            new_code = self._fix_specific_compilation_error(
                current_code, error, guidance, direct_use_llm
            )

            if not new_code or new_code == current_code:
                self.logger.warning(f"Could not fix compilation error: {error.error}")
                direct_use_llm = True  # Next attempt will directly use LLM
                continue

            # Test the fixed code
            current_code = new_code
            veval = VEval(current_code, self.logger)
            veval.eval()
            score = veval.get_score()
            direct_use_llm = False  # Reset for next attempt

            # Get error pattern and log the result
            error_pattern = self._get_error_pattern(error)

            if not score.compilation_error:
                self.logger.info(f"All compilation errors fixed after {attempt} attempts")
                # Log successful fix
                self._log_repair_attempt(error_pattern, old_code, new_code, success=True)
                return current_code
            else:
                # Log failed fix (compilation error still exists)
                self._log_repair_attempt(error_pattern, old_code, new_code, success=False)

        self.logger.warning(f"Failed to fix compilation errors after {max_attempts} attempts")
        return current_code

    def _get_one_compilation_failure(self, verus_errors: list[VerusError]) -> VerusError | None:
        """Prioritize among compilation errors"""
        # Type errors get first priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.MismatchedType:
                return verus_error

        # Unexpected proof block gets second priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.UnxProofBlock:
                return verus_error

        # Rust assert gets third priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.RustAssert:
                return verus_error

        # Expected parentheses gets fourth priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.ExpectedParentheses:
                return verus_error

        # Default to first error
        return verus_errors[0] if verus_errors else None

    def _fix_specific_compilation_error(
        self, code: str, error: VerusError, guidance: str = "", direct_use_llm=False
    ) -> str | None:
        """Fix a specific compilation error based on its type"""
        if direct_use_llm:
            return self._fix_with_llm(code, error, "compilation error", guidance)

        if error.error == VerusErrorType.MismatchedType:
            return self._fix_type_error(code, error, guidance)
        elif error.error == VerusErrorType.UnxProofBlock:
            return self._fix_unexpected_proof_block(code, error, guidance)
        elif error.error == VerusErrorType.RustAssert:
            return self._fix_rust_assert(code, error, guidance)
        elif error.error == VerusErrorType.ExpectedParentheses:
            return self._fix_expected_parentheses(code, error, guidance)
        elif error.error == VerusErrorType.UnsupportedForBitVector:
            return self._fix_unsupported_bitvector(code, error, guidance)
        else:
            # Try generic syntax repair for unknown error types
            return self._fix_with_llm(code, error, "compilation error", guidance)

    def _fix_type_error(self, code: str, error: VerusError, guidance: str = "") -> str | None:
        """Fix type mismatch errors"""
        try:
            from utils import fix_one_type_error_in_code

            new_code = fix_one_type_error_in_code(code, error.trace[0], verbose=False)
            if new_code and new_code != code:
                self.logger.info("Fixed type error")
                return new_code
        except Exception as e:
            self.logger.warning(f"Failed to fix type error: {e}")

        # If automatic fix fails, try LLM-based repair
        return self._fix_with_llm(code, error, "type error", guidance)

    def _fix_unexpected_proof_block(
        self, code: str, error: VerusError, guidance: str = ""
    ) -> str | None:
        """Fix unexpected proof block errors by removing the proof block"""
        try:
            if error.error != VerusErrorType.UnxProofBlock:
                return None

            # Get problematic proof block line number ranges
            err_trace = error.trace[0]
            line_start = err_trace.get_lines()[0]
            line_end = err_trace.get_lines()[1]

            self.logger.info(
                f"Fixing unexpected proof block error at lines {line_start}-{line_end}"
            )

            # Check if the first and last lines are indeed proof { and }
            code_lines = code.split("\n")
            if line_start > len(code_lines) or line_end > len(code_lines):
                return None

            line_start_str = code_lines[line_start - 1]
            line_end_str = code_lines[line_end - 1]

            if "".join(line_start_str.split()) != "proof{":
                self.logger.warning(f"Line {line_start}: {line_start_str} cannot be handled")
                return None
            elif not line_end_str.lstrip().startswith("}"):
                self.logger.warning(f"Line {line_end}: {line_end_str} cannot be handled")
                return None

            print("\n".join(code_lines[line_start : line_end - 1]))
            # Remove the enclosing proof block
            new_lines = (
                code_lines[: line_start - 1]
                + code_lines[line_start : line_end - 1]
                + code_lines[line_end:]
            )
            new_code = "\n".join(new_lines)

            self.logger.info("Fixed unexpected proof block error")
            return new_code

        except Exception as e:
            self.logger.warning(f"Failed to fix unexpected proof block: {e}")
            return None

    def _fix_rust_assert(self, code: str, error: VerusError, guidance: str = "") -> str | None:
        """Fix Rust assert! errors by converting to assert"""
        try:
            if error.error != VerusErrorType.RustAssert:
                return None

            code_lines = code.split("\n")
            line_num = error.trace[0].get_lines()[0] - 1

            if line_num >= len(code_lines):
                return None

            old_line = code_lines[line_num]
            new_line = old_line.replace("assert!", "assert")
            code_lines[line_num] = new_line

            new_code = "\n".join(code_lines)

            if new_code != code:
                self.logger.info("Fixed Rust assert! error")
                return new_code

        except Exception as e:
            self.logger.warning(f"Failed to fix Rust assert: {e}")

        return None

    def _fix_expected_parentheses(
        self, code: str, error: VerusError, guidance: str = ""
    ) -> str | None:
        """Fix expected parentheses errors by using the dedicated action"""
        try:
            from ..shared_types import Observation
            from .expected_parentheses_repair import ExpectedParenthesesRepairAction

            # Create an observation for the expected parentheses repair action
            observation = Observation(
                code=code,
                error=error,
                error_location=(0, 0),  # Will be filled by the action
                error_text=error.get_text(),
                surrounding_context=code,
            )

            # Create and execute the expected parentheses repair action
            action_instance = ExpectedParenthesesRepairAction()
            result = action_instance.execute(observation, {"guidance": guidance})

            if result.success and result.modified_code and result.modified_code != code:
                self.logger.info("Fixed expected parentheses error using dedicated action")
                return result.modified_code
            else:
                self.logger.warning("Expected parentheses repair action failed")
                return None

        except Exception as e:
            self.logger.error(f"Failed to use expected parentheses repair action: {e}")
            return None

    def _fix_unsupported_bitvector(
        self, code: str, error: VerusError, guidance: str = ""
    ) -> str | None:
        """Fix unsupported bitvector assert errors"""

        guidance = """
        There are two key code features that are NOT supported by the bit_vector prover yet, and have to be avoided:
        1. spec functions;
        2. constant variables.
        These two code features can NOT appear in ANY part of a bit_vector assert --- they can NOT be part of the
        asserted expression, AND they can NOT be part of the `requires` clause either!!

        You should rewrite the bit_vector expression to avoid using spec functions (by inlining them) and
        to avoid constant variables (by assigning them to a normal variable) in BOTH the asserted expression,
        and the requires clause.

        Here are two examples.


        First: an example about spec function.

The following code would lead to compilation errors as it included spec functions `get_bit` and `andtwo` in the bit_vector code block:
```rust
spec fn get_bit(a: u32, b: u32) -> bool {
    (0x1u32 & (a >> b)) == 1
}

spec fn andtwo(a: u32) -> u32 {
    a & 2
}

proof fn test_macro(x: u32)
    requires andtwo(x) == 1
{
    assert(get_bit(x, 1)) by (bit_vector)
        requires
            andtwo(x) == 1
    ; // Unsupported Bitvector ERROR
}
```

To fix the above error, you should rewrite by inlining ALL the spec functions:
```
    assert(get_bit(x, 1)) by {
        assert((0x1u32 & (x >> 1)) == 1) by (bit_vector)
            requires
                x & 2 == 1
        ; // SUCCEEDS
    }
}
```

    Second: an example about constant variables.

The following code would lead to unsupported-bit-vector error, as constant variable is NOT supported by bit_vector.
```rust
    pub const MYCONST: u32 = 10;

    assert( MYCONST & 3 == 10 & 3) by (bit_vector)
        requires
            MYCONST == 10,
    ; // MYCONST cannot be directly used here, as bit_vector prover does NOT support const
```

Instead, you should do the following, using a variable with equal value as MYCONST in the bit_vector assert:

```rust
    pub const MYCONST: u32 = 10;

    let ghost tmp = MYCONST; //needed here!

    assert( tmp & 3 == 10 & 3) by (bit_vector)
        requires
            tmp == 10,
    ; // SUCCEED
```

Keep in mind that spec functions and const variables can NOT show up in any part of a bit_vector code block:
    they cannot be part of the asserted expression; AND they cannot be parted of the requires clause.
        """

        return self._fix_with_llm(code, error, "unsupported bit-vector error", guidance)

    def _get_error_pattern(self, error: VerusError) -> str:
        """Create a pattern string for error matching"""
        import re

        # Use error type + normalized message
        pattern = f"{error.error.name}: {error.message}"
        # Remove line numbers and specific identifiers
        pattern = re.sub(r"\d+", "NUM", pattern)
        return pattern[:200]  # Limit length

    def _log_repair_attempt(self, error_pattern: str, old_code: str, new_code: str, success: bool):
        """Log a repair attempt to history using diff format"""
        global _SYNTAX_REPAIR_HISTORY
        if error_pattern not in _SYNTAX_REPAIR_HISTORY:
            _SYNTAX_REPAIR_HISTORY[error_pattern] = []

        # Generate search-replace diff
        diff = generate_search_replace_diff(old_code, new_code)
        _SYNTAX_REPAIR_HISTORY[error_pattern].append((diff, success))
        self.logger.debug(f"Logged repair: {'success' if success else 'failed'}")

    def _get_history_context(self, error_pattern: str) -> str:
        """Get relevant history for this error pattern"""
        global _SYNTAX_REPAIR_HISTORY
        if error_pattern not in _SYNTAX_REPAIR_HISTORY:
            return ""

        history = _SYNTAX_REPAIR_HISTORY[error_pattern]
        if not history:
            return ""

        context = "\n## Previous Repair Attempts for Similar Errors:\n"
        for i, (diff, success) in enumerate(history[-3:], 1):  # Last 3 attempts
            status = "✓ SUCCESSFUL" if success else "✗ FAILED"
            context += f"\n### Attempt {i}: {status}\n```diff\n{diff}\n```\n"

        return context

    def _fix_with_llm(
        self, code: str, error: VerusError, error_type: str, guidance: str = ""
    ) -> str | None:
        """Fix errors using LLM-based repair with history augmentation"""
        try:
            # Use LLM to fix the syntax error
            instruction = f"Your mission is to fix the {error_type} in the following Verus code. Please follow the Verus and Rust syntax rules strictly."
            if guidance:
                instruction += f"\n\nSpecific guidance: {guidance}"

            # Check for known invalid syntax patterns and add specific hints
            from ..verus_syntax_patterns import check_invalid_verus_syntax, get_syntax_hint

            pattern_error = check_invalid_verus_syntax(code)
            if pattern_error:
                hint = get_syntax_hint(code)
                instruction += f"\n\n⚠️ **Known Syntax Pattern Detected**: {pattern_error}"
                if hint:
                    instruction += f"\n💡 **Syntax Hint**: {hint}"
                    instruction += "\n\n**IMPORTANT**: This is a common mistake. Follow the hint above to fix it correctly."

            # Add history context with diffs
            error_pattern = self._get_error_pattern(error)
            self.logger.debug(error_pattern)
            history_context = self._get_history_context(error_pattern)
            if history_context:
                instruction += f"\n\n{history_context}"
                instruction += "\n**Learn from previous attempts**: Reuse successful fixes and avoid repeating failed approaches."

            line_info = ""
            # Get error information
            error_text = str(error.error) + ": " + error.message + "\n" + error.get_text()
            if len(error.trace) > 0:
                trace = error.trace[0]
                line_info += (
                    f"Error at line {trace.lines[0]}-{trace.lines[1]}: {trace.get_text()}\n\n"
                )
            line_info += f"Error: {error_text}\n"
            self.logger.warning(line_info)

            query = f"""Error Information:
{line_info}

Code to fix:
```rust
{code}
```"""

            # Call LLM for repair
            engine = self.config.aoai_debug_model
            responses = self.invoke_llm(
                engine,
                instruction,
                query,
                self.default_system,
                original_code=code,
                answer_num=self.get_action_candidate_num(),
                max_tokens=4096,
                temp=1.0,
                skip_history=True,
            )

            if responses and responses[0]:
                # Extract code from response
                response = responses[0].strip()

                # Try to extract code blocks
                import re

                code_blocks = re.findall(r"```rust\s*\n(.*?)\n```", response, re.DOTALL)
                if code_blocks:
                    new_code = code_blocks[0].strip()
                else:
                    # If no code blocks, try to extract the entire response
                    new_code = response.strip()

                if new_code and new_code != code:
                    self.logger.info(f"Fixed {error_type} using LLM")
                    # Don't log here - logging happens in _repair_compilation_errors after verification
                    return new_code

        except Exception as e:
            self.logger.error(f"Error line: {e.__traceback__.tb_lineno}")
            self.logger.error(f"Failed to fix {error_type} with LLM: {e}")

        return None
