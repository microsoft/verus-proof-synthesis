"""
Special repair actions for various edge cases and syntax issues
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class PlainTextRepairAction(BaseAction):
    """Action to repair based on plain text error descriptions"""

    @classmethod
    def get_action_type(cls) -> ActionType:
        return ActionType.PLAIN_TEXT_REPAIR

    @classmethod
    def get_description(cls) -> str:
        return "Repair code based on plain text error descriptions when specific error types are not available."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Analyze the plain text error and suggest appropriate fixes."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Plain text repairs should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the plain text repair action"""
        guidance = params.get("guidance", "Apply general text-based repair")
        error_text = observation.error_text

        # Directly implement plain text repair without using self.repairs
        candidates = self._repair_plain_text(observation.code, error_text, num=3, temp=1.0)

        if candidates:
            return self._create_result(
                observation=observation,
                action_type=ActionType.PLAIN_TEXT_REPAIR,
                repaired_codes=candidates,
                guidance=guidance,
            )
        else:
            return self._create_result(
                observation=observation,
                action_type=ActionType.PLAIN_TEXT_REPAIR,
                repaired_codes=[],
                guidance=guidance,
            )

    def _repair_plain_text(self, code: str, error_text: str, num=1, temp=1.0) -> list[str]:
        """Repair code given plain text error description"""
        instruction = """Your mission is to fix the error for the following code. Basically, you should add/modify/delete the proof blocks, assertions and loop invariants related to the errors."""

        # Get examples

        # Format query
        query = f"Errors\n```\n{error_text}```\n\nCode\n```\n{code}```\n"

        # Invoke LLM
        return self.invoke_llm(
            self.config.aoai_generation_model,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
