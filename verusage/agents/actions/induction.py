"""
Induction Action
Turns the proof into a proof by induction.
Contains full implementation with prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class InductionAction(BaseAction):
    """Action to use induction in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "When the lemma requires inductive reasoning to reason about *recursive* spec functions or to prove the lemma conclusion, transform the lemma into a proof by induction. Add inductive invocations of the lemma within its own proof."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Analyze why induction is necessary to complete the proof. Identify potential base and inductive cases."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when induction is necessary to prove the current lemma. This is common when recursive definitions show up in the lemma specification. **Notes:** This action is more powerful than simple case analysis: it allows recursive invocations of the current lemma. If the inductive proof should be factored out into a separate lemma, use the inductive lemma action instead."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Induction should not affect verified code"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the induction action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._repair_induction(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.INDUCTION, repaired_codes, guidance)

    def _repair_induction(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained induction repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("induction")

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
