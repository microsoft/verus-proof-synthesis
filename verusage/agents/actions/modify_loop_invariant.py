"""
Modify Loop Invariant Action
Handles general loop invariant modification and addition for various invariant-related errors.
Contains comprehensive invariant repair implementation including both front and end scenarios.
"""

from typing import Any

from veval import VerusErrorType

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class ModifyLoopInvariantAction(BaseAction):
    """Action to modify, add, or strengthen loop invariants"""

    @classmethod
    def get_description(cls) -> str:
        return "Modify, add, or strengthen loop invariants to resolve invariant-related verification failures"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain which loop invariant needs to be modified, added, or strengthened and provide specific conditions or properties that should be included."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Loop invariant modifications should improve verification"""
        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the modify loop invariant action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._modify_loop_invariant(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.MODIFY_LOOP_INVARIANT, repaired_codes, guidance
        )

    def _modify_loop_invariant(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained loop invariant modification implementation"""

        # Use the provided candidate number

        # Determine the type of invariant issue and handle accordingly
        if hasattr(verus_error, "error"):
            if verus_error.error == VerusErrorType.InvFailFront:
                return self._handle_invariant_front(code, verus_error, guidance, num, temp)
            elif verus_error.error == VerusErrorType.InvFailEnd:
                return self._handle_invariant_end(code, verus_error, guidance, num, temp)

        # General loop invariant modification for other error types (like assertion failures in loops)
        return self._handle_general_invariant_modification(code, verus_error, guidance, num, temp)

    def _handle_invariant_front(
        self, code: str, verus_error, guidance: str, num: int, temp: float
    ) -> list[str]:
        """Handle invariant failures at loop entry"""
        engine = self.config.aoai_debug_model

        instruction = load_prompt("invariant_front_repair_general")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare invariant info
        error_trace = verus_error.trace[0]
        inv_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info += error_trace.get_text() + "\n"

        query = f"""Fix this failed loop invariant at loop entry:

{inv_info}

Target code:
```verus
{code}
```"""

        return self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            original_code=code,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
        )

    def _handle_invariant_end(
        self, code: str, verus_error, guidance: str, num: int, temp: float
    ) -> list[str]:
        """Handle invariant failures at loop end"""
        engine = self.config.aoai_debug_model

        instruction = load_prompt("invariant_end_repair")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare invariant info
        error_trace = verus_error.trace[0]
        inv_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info += error_trace.get_text() + "\n"

        query = f"""Fix this failed loop invariant at loop end:

{inv_info}

Target code:
```verus
{code}
```"""

        # Get examples from the existing example system

        return self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )

    def _handle_general_invariant_modification(
        self, code: str, verus_error, guidance: str, num: int, temp: float
    ) -> list[str]:
        """Handle general loop invariant modifications for non-invariant-specific errors"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("invariant_front_repair_general")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Create query with error information
        if hasattr(verus_error, "trace") and verus_error.trace:
            error_info = verus_error.trace[0].get_text() + "\n"
            query = f"""Fix this verification error by modifying loop invariants:

{error_info}

Target code:
```verus
{code}
```"""
        else:
            query = f"""Fix this verification error by modifying loop invariants:

Target code:
```verus
{code}
```"""

        # Use general assertion repair examples which often involve invariants

        return self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
