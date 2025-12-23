"""
Invariant Repair Actions
Repairs loop invariant failure errors at the beginning and end of loops.
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class InvariantFrontRepairAction(BaseAction):
    """Action to repair invariant failures before loop execution"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair loop invariant failures at the beginning of loops by adding assertions before the loop or modifying the invariant conditions"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain which invariant is failing at loop entry and suggest whether to add assertions before the loop or modify the invariant condition."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Invariant front repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the invariant front repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_invfail_front(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.INVARIANT_FRONT_REPAIR, repaired_codes, guidance
        )

    def _repair_invfail_front(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained invariant front failure repair implementation"""

        # Use the provided candidate number
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

        # Get examples from the existing example system

        # Use the existing repair infrastructure
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


class InvariantEndRepairAction(BaseAction):
    """Action to repair invariant failures at the end of loops"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair loop invariant failures at the end of loops by adding assertions within the loop body to maintain the invariant"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain which invariant is failing at loop end and suggest what assertions should be added within the loop body to maintain the invariant."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Invariant end repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the invariant end repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_invfail_end(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.INVARIANT_END_REPAIR, repaired_codes, guidance
        )

    def _repair_invfail_end(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained invariant end failure repair implementation"""

        # Use the provided candidate number
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

        # Use the existing repair infrastructure
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
