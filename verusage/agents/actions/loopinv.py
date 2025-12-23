"""
Add Loop Invariant Action
Contains full implementation with prompts.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class LoopInvAction(BaseAction):
    """Action to add loop invariants in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "If the assert statement is after a loop in the same function, proper invariants need to be added to that loop."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Loop invariants are needed to tell Verus what properties are true at the end of a loop."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when there is a loop before the asserted expression."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        return {
            # TODO I think we should accept as long as there is no syntax error, and # assert error does not go up
            "criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED_EXLOOP,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._repair_loopinv(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.LOOPINV, repaired_codes, guidance)

    def _repair_loopinv(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("loopinv")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""Fix this failed assertion:

{assertion_info}

Target code:
```verus
{code}
```"""

        # todo - examples?

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
