"""
Bit Vector Reasoning Action
Adds bit vector reasoning to the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class BitVectorReasoningAction(BaseAction):
    """Action to use bit vector reasoning in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "When the failing assertion requires reasoning about bitwise operators `&`, `|`, `^`, `<<` and `>>`, and/or the truncating arithmetic functions `add`, `sub`, and `mul`."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the assertion involves bitwise operations and truncating arithmetic functions. Bit vector reasoning is more effective than arithmetic reasoning when these operations are present."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Describe mathematically why the failing assertion is true. Do not describe what Verus features to use or assume existence of any Verus lemmas/axioms besides those in this file."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Bit vector reasoning should reduce error count"""
        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the bit vector reasoning action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._bit_vector_reasoning(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.BIT_VECTOR_REASONING, repaired_codes, guidance
        )

    def _bit_vector_reasoning(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained bit vector reasoning implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("bit_vector_reasoning")

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
