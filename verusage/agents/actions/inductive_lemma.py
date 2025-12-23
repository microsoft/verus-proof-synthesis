"""
Inductive Lemma Action
Adds an inductive lemma to the file
Contains full implementation with prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class InductiveLemmaAction(BaseAction):
    """Action to insert an inductive lemma in the file"""

    @classmethod
    def get_description(cls) -> str:
        return "When the failing assertion requires a separate helper lemma that itself requires a proof by induction, create a new helper lemma for the inductive proof."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Analyze what fact is needed to prove the failing assertion and why it requires induction to prove."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the failing assertion can only be proven by an inductive proof, but the proof should be factored out into a new, separate lemma. **Notes:** this action has important information about setting up the signature of an inductive lemma that is not included in the normal induction action."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Induction should not affect verified code"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED, "threshold": 0.0}

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

        return self._create_result(
            observation, ActionType.INDUCTIVE_LEMMA, repaired_codes, guidance
        )

    def _repair_induction(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained inductive lemma repair implementation"""

        instruction = load_prompt("inductive_lemma")

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
            self.config.aoai_debug_model,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
