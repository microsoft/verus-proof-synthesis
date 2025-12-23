"""
Postcondition Repair Action
Repairs postcondition failure errors by adding proof blocks at function exit points.
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class PostconditionRepairAction(BaseAction):
    """Action to repair postcondition failure errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair postcondition failure errors by adding proof blocks at function exit points to establish required postconditions"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain what postconditions are failing and what proof blocks or loop invariants should be added at the function exit point."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Postcondition repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the postcondition repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_postcondition_failure(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.POSTCONDITION_REPAIR, repaired_codes, guidance
        )

    def _repair_postcondition_failure(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained postcondition failure repair implementation"""

        # Use the provided candidate number

        # Check if we have expand trace information for more detailed repair
        if len(verus_error.expand_trace) > 0:
            self.logger.error("Repairing postcondition with expand trace information")
            return self._repair_postcond_expand_error(code, verus_error, guidance, num, temp)
        else:
            self.logger.error("Repairing postcondition with basic error")
            return self._repair_postcond_basic_error(code, verus_error, guidance, num, temp)

    def _repair_postcond_expand_error(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Repair postcondition with expand trace information"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        # Load instruction from prompt file
        instruction = load_prompt("postcondition_repair_expand")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Parse error traces for expand error
        location_trace = verus_error.trace[0]

        post_cond_info = ""
        for t in verus_error.expand_trace:
            post_cond_info += f"Line {t.lines[0]}-{t.lines[1]}:\n"
            post_cond_info += t.get_text() + "\n"

        location_info = f"Line {location_trace.lines[0]}-{location_trace.lines[1]}:\n"
        location_info += location_trace.get_text() + "\n"

        query = self.format_query_template(
            "failed_postcondition", post_cond_info, location_info, code
        )

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

    def _repair_postcond_basic_error(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Repair basic postcondition failure"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        # Load instruction from prompt file
        instruction = load_prompt("postcondition_repair_basic")

        # Parse error traces for basic error
        from veval import VerusErrorLabel

        location_trace, postcond_trace = verus_error.trace[0], verus_error.trace[1]
        if location_trace.label == VerusErrorLabel.FailedThisPostCond:
            location_trace, postcond_trace = postcond_trace, location_trace

        post_cond_info = f"Line {postcond_trace.lines[0]}-{postcond_trace.lines[1]}:\n"
        post_cond_info += postcond_trace.get_text() + "\n"

        location_info = f"Line {location_trace.lines[0]}-{location_trace.lines[1]}:\n"
        location_info += location_trace.get_text() + "\n"

        query = self.format_query_template(
            "failed_postcondition", post_cond_info, location_info, code
        )

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
