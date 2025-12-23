"""
Use Lemma Axiom Action
Contains full implementation with prompts.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class UseLemmaAction(BaseAction):
    """Action to leverage axioms or existing lemmas in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "If the full code contains other proof functions (lemmas or axioms), we may need to call them to prove the failing assertion. Do NOT assume any lemma functions that do not exist in the code!"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Do not make up proof functions that do not exist; only call a proof function when it is already in the code and can help prove the failing assert."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "When the full code contains any proof function other than the current function to be proved, make sure to check if any of those proof functions can help prove the failing assert. Note: do NOT make sure lemma functions to call. Use this action ONLY when the full code contains another proof function."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        return {
            # TODO: I am not sure if it should be ERROR_REDUCTION OR NOT; I feel it should be no more error
            "criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED_NO_ERROR_INCREASE,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._repair_lemma(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.USELEMMA, repaired_codes, guidance)

    def _repair_lemma(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("uselemma")

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
