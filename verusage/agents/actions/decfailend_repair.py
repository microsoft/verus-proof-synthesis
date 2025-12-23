"""
Loop Decrease (error at the end of loop) Repair Action
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class DecFailEndRepairAction(BaseAction):
    """Action to repair loop decrease-fail-end errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair DecFailEnd errors by adjusting the decrease clause of a loop"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Think about what is the wrong with the current decrease clause, and adjust accordingly."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """should improve verification"""
        return {
            # TODO
            "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the decfailend repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_decfailend(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.DECFAILEND_REPAIR, repaired_codes, guidance
        )

    def _repair_decfailend(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained decrease fail-end repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        error_trace = verus_error.trace[0]

        instruction = f"""Your mission is to fix the decrease-clause error reported for the loop ` {error_trace.get_highlights()[0]}' in line `{error_trace.get_text().strip()}' of the program.

        The value of the decrease clause expression needs to strictly decrease across every iteration.
        Furthermore, that value should NEVER become negative. For example, if an expression ```E``` 's value may become -7 at the end of the loop, you should use ```E + 7``` as the decrease clause.
"""

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare query
        line_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info = line_info + error_trace.get_text() + "\n"
        query = self.format_query_template("decfailend_error", inv_info, code)

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
