"""
Reveal Opaque Action
Reveals an opaque definition in the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class RevealOpaqueAction(BaseAction):
    """Action to reveal an opaque definition in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "When a spec fn in the current code is marked as `[#verifier::opaque]`, reveal its definition so that it can be made visible to the verifier."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "ONLY apply when there is a spec function in the current code marked with `[#verifier::opaque]` whose definition needs to be visible to the verifier. You should NEVER reveal an executable function, or a `closed` or `open` spec function. "

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Identify the opaque definition to be revealed and where it should be revealed."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Reveal is a structural change and may not lead to verification improvement"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the reveal action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._repair_reveal(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.REVEAL_OPAQUE, repaired_codes, guidance)

    def _repair_reveal(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained reveal repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("reveal_opaque")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""Address this failed assertion:

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
