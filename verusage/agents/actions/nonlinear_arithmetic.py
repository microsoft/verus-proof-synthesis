"""
Nonlinear Arithmetic Reasoning Action
Adds nonlinear arithmetic reasoning to the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class NonlinearArithmeticAction(BaseAction):
    """Action to use nonlinear arithmetic in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "Nonlinear arithmetic supports reasoning about equalities and inequalities for expressions that use arithmetic operators +, -, *, /, % and non-constant number values. This action also includes knowledge of axioms about natural numbers/integers, such as commutativity. This action CANNOT reason about spec function definitions or simplify spec function expressions: it will treat spec functions as arbitrary values. If you need to reason about the value of a spec function expression, apply another action FIRST (e.g., reveal with fuel, inductive lemma, compute on concrete values)."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Describe what equalities or inequalities to establish using nonlinear arithmetic, and why nonlinear arithmetic is sufficient to establish those facts. Do not describe what Verus features to use or assume existence of any Verus lemmas/axioms besides those in this file."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the failing assertion involves operators +, -, *, /, % and equational reasoning, including on non-concrete (arbitrary) values. Most effective for assertions with integer/natural number operations, bounds checking, or mathematical properties. **Notes:** this action uses a specialized solver that CANNOT use and simplify spec function definitions. You can only establish simple facts about +, -, *, /, %, and any spec functions will be treated as arbitrary values. If the expression uses spec functions, you may need to combine this action with other actions, or use a different action entirely."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Arithmetic reasoning should reduce error count"""
        return {"criteria": AcceptanceCriteria.ERROR_REDUCTION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the nonlinear arithmetic reasoning action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._nonlinear_arithmetic_reasoning(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.NONLINEAR_ARITHMETIC, repaired_codes, guidance
        )

    def _nonlinear_arithmetic_reasoning(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained nonlinear arithmetic reasoning implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("arithmetic_reasoning")

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
