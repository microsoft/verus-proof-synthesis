"""
Integer Ring Action
Adds integer-ring lemma function to the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class IntegerRingAction(BaseAction):
    """Action to use integer ring in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "Nonlinear formulas that consists of congruence modulo relations among integers (e.g., to show that a % n == b % n ==> (a * c) % n == (b * c) % n) can benefit from integer_ring."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Think about what integer modulo-congruence relationship to establish using integer_ring."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the failing assertion is about modulo-congruence relationship among integers. Keep in mind that integer_ring can only be used with int parameters; it does NOT support division; it does NOT support inequalities."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Integer ring should reduce error count"""
        return {"criteria": AcceptanceCriteria.ERROR_REDUCTION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the integer ring action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._integer_ring_reasoning(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.INTEGER_RING, repaired_codes, guidance)

    def _integer_ring_reasoning(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained integer-ring reasoning implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("integer_ring")

        # Add guidance if provided
        # if guidance:
        #    instruction += f"\n\nSpecific guidance: {guidance}"

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
