"""
Type Repair Action
Repairs type mismatch errors and other type-related compilation issues.
Contains the full repair implementation including type debugging and fixing.
"""

import re
from typing import Any

from veval import VerusErrorType, VEval

from utils import clean_code, fix_one_type_error_in_code

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class TypeRepairAction(BaseAction):
    """Action to repair type mismatch and compilation errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair type mismatch errors and other compilation issues by fixing type annotations and conversions"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain what type mismatch is occurring and suggest the appropriate type conversions or annotations needed."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Type repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the type repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_type_error(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.TYPE_REPAIR, repaired_codes, guidance)

    def _repair_type_error(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained type error repair implementation"""

        # Use the provided candidate number

        # First try automatic type debugging
        if verus_error.error == VerusErrorType.MismatchedType:
            auto_fixed_code, remaining_errors = self._debug_type_error(code, verus_error)
            if remaining_errors == 0 and auto_fixed_code:
                return [auto_fixed_code]

        # If automatic fix didn't work, use LLM-based repair
        return self._llm_based_type_repair(code, verus_error, guidance, num, temp)

    def _debug_type_error(self, code: str, verus_error=None) -> tuple[str, int]:
        """Debug and automatically fix type errors using built-in type fixing"""

        rnd = 0
        max_rnd = 10

        # Fix the specific reported error first if provided
        if verus_error and verus_error.error == VerusErrorType.MismatchedType:
            newcode = fix_one_type_error_in_code(code, verus_error.trace[0], verbose=False)
            if newcode:
                code = newcode

        # Iteratively fix all type errors
        while rnd < max_rnd:
            rnd = rnd + 1

            veval = VEval(code, self.logger)
            veval.eval()
            failures = veval.get_failures()

            if len(failures) == 0:
                self.logger.info("Verus has succeeded.")
                return code, 0

            has_typeerr = False
            fixed_typeerr = False

            for cur_failure in failures:
                if cur_failure.error == VerusErrorType.MismatchedType:
                    has_typeerr = True
                    newcode = fix_one_type_error_in_code(code, cur_failure.trace[0], verbose=False)

                    # When newcode is "", the function failed to fix any type error
                    if newcode:
                        fixed_typeerr = True
                        code = newcode
                        break
                    else:
                        # This type error is unfixable, let's move on to next error
                        continue

                if not fixed_typeerr:
                    # Not able to fix any type error in this program, no need to try again
                    break

            if not has_typeerr:
                return code, 0

            if not fixed_typeerr:
                self.logger.info("Remaining type errors are unfixable.")
                return "", len(failures)

        return code, len(failures)

    def _llm_based_type_repair(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """LLM-based type error repair when automatic fixing fails"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        instruction = load_prompt("type_repair")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Parse error information
        if len(verus_error.trace) == 0:
            self.logger.warning("No trace information in the error.")
            return [code]

        trace = verus_error.trace[0]
        line_info = f"Line {trace.lines[0]}-{trace.lines[1]}:\n"
        error_info = line_info + verus_error.get_text() + "\n"

        # Format query directly
        query = f"Error\n```\n{error_info}```\n\nCode\n```\n{code}```\n"

        # Get examples from the existing example system

        # Invoke LLM directly
        llm_results = self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )

        # Post-process each result with automatic type debugging
        processed_results = []
        for result in llm_results:
            if not result:
                continue

            cleaned_code = clean_code(result)
            # Try to fix any remaining type errors automatically
            final_code, _ = self._debug_type_error(cleaned_code)
            if final_code:
                processed_results.append(final_code)
            else:
                processed_results.append(cleaned_code)

        return processed_results


class UseRepairAction(BaseAction):
    """Action to repair method-not-found errors by adding use ..."""

    @classmethod
    def get_description(cls) -> str:
        return "Repair method-not-found errors by adding use ..."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Check if the error message suggests a use statement."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Rust assert repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the Rust use repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_rust_use(observation.code, observation.error)

        return self._create_result(observation, ActionType.USE_REPAIR, repaired_codes, guidance)

    def _repair_rust_use(self, code: str, verus_error) -> list[str]:
        """Repair method-not-found error by adding use"""

        if verus_error.error != VerusErrorType.MethodNotFound:
            self.logger.warning("A non method-not-found error is passed to repair_rust_use")
            return [code]

        hint = verus_error.error_text

        match = re.search(r"\+ use\s*(.*?);", hint)

        if not match:
            return [code]
        else:
            toadd = "use " + match.group(1).strip() + ";"

            codes = code.split("\n")
            codes.insert(0, toadd)

            newcode = "\n".join(codes)
            return [newcode] if newcode else []
