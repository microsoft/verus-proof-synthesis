"""
Precondition Repair Action
Repairs precondition failure errors by adding proof blocks before function calls.
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class PreconditionRepairAction(BaseAction):
    """Action to repair precondition failure errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair precondition failure errors by adding proof blocks before function calls to establish required preconditions"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain what properties need to be proven before the function call to satisfy its preconditions."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Precondition repairs should improve verification"""
        return {"criteria": AcceptanceCriteria.FIX_PRECONDITION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the precondition repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_precondition_failure(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.PRECONDITION_REPAIR, repaired_codes, guidance
        )

    def _repair_precondition_failure(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained precondition failure repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        instruction = load_prompt("precondition_repair")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare precondition info
        precond_trace, location_trace = verus_error.trace[0], verus_error.trace[1]
        if hasattr(location_trace, "label") and location_trace.label.name == "FailedThisPreCond":
            precond_trace, location_trace = location_trace, precond_trace

        pre_cond_info = precond_trace.get_text() + "\n"
        location_info = f"Line {location_trace.lines[0]}-{location_trace.lines[1]}:\n"
        location_info += location_trace.get_text() + "\n"

        query = f"""Fix this failed precondition:

Precondition:
{pre_cond_info}

Location:
{location_info}

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
