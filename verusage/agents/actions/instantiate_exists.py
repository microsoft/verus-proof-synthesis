"""
Instantiate Exists Action for existential quantifier handling
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class InstantiateExistsAction(BaseAction):
    """Action to handle existential quantifier instantiation for assertion proving"""

    @classmethod
    def get_action_type(cls) -> ActionType:
        return ActionType.INSTANTIATE_EXISTS

    @classmethod
    def get_description(cls) -> str:
        return "If the failing assertion starts with `exists` AND/OR depends on a known fact that starts with `exists`, explicitly instantiate the existentially quantified variable(s) to use in further reasoning."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Identify which quantified expressions need instantiation."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the failing assertion contains a `forall` quantifier and/or there are useful facts that are contained in existentially quantified expressions. Most effective when the verifier needs help finding or choosing a witness for an `exists` expression."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Instantiation should not affect verified code"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the instantiation action"""
        guidance = params.get("guidance", "Apply quantifier instantiation")

        # Use self-contained implementation instead of calling repairs
        repaired_codes = self._instantiation_repair(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.INSTANTIATE_EXISTS, repaired_codes, guidance
        )

    def _instantiation_repair(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ):
        """Self-contained instantiation repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("instantiate_exists")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""Fix this failed assertion with quantifier instantiation:

{assertion_info}

Target code:
```verus
{code}
```"""

        # Use the repair infrastructure to call LLM
        return self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            original_code=code,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
        )
