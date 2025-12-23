"""
Add Trigger Assert Action
Adds assert statements to trigger quantified formulas.
Contains full implementation with prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class AddTriggerAssertAction(BaseAction):
    """Action to add trigger assertions for quantified formulas"""

    @classmethod
    def get_description(cls) -> str:
        return "Add strategic trigger assertions to help the verifier instantiate quantified formulas. Analyzes trigger patterns from preconditions, previous assertions, and spec functions to add targeted assert statements that provide necessary quantifier instantiations for proof completion."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Identify trigger patterns in preconditions, previous assertions, and spec functions. Determine what instantiations are missing for the failed assertion, then add `assert(trigger_expression)` statements to provide the necessary quantifier triggers. Focus on expressions marked with `#[trigger]` annotations."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the assertion failure is caused by missing quantifier triggers, preventing the verifier from instantiating relevant quantified formulas. Most effective when preconditions or previous assertions/spec functions contain `#[trigger]` annotations and the verifier needs specific trigger expressions to instantiate quantifiers for the proof."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Trigger assertions should reduce error count"""
        return {"criteria": AcceptanceCriteria.ERROR_REDUCTION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the add trigger assert action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._repair_trigger_assertions(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.ADD_TRIGGER_ASSERT, repaired_codes, guidance
        )

    def _repair_trigger_assertions(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained trigger assertion repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("add_trigger_assert")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        trigger_expr = verus_error.trigger_expr
        if trigger_expr:
            trigger_text = "\n  ".join(trigger_expr)
            assertion_info += "\nTrigger expression: " + trigger_text + "\n"

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
