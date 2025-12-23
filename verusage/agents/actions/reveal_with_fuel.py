"""
Reveal with Fuel Action
Reveals a recursive definition with fuel definition in the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class RevealWithFuelAction(BaseAction):
    """Action to reveal a definition with fuel in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return (
            "When a spec fn is recursive, allow the verifier to unfold its definition a specified number of times ("
            "fuel"
            ")."
        )

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when there is a recursive function in this file whose definition needs to be unfolded multiple times by the verifier. **Notes:** By default, Verus will unfold all recursive definitions *once*."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Identify the recursive definition to be revealed with more fuel and where it should be revealed."

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

        return self._create_result(
            observation, ActionType.REVEAL_WITH_FUEL, repaired_codes, guidance
        )

    def _repair_reveal(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained reveal repair implementation"""

        instruction = load_prompt("reveal_with_fuel")

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
            self.config.aoai_debug_model,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
