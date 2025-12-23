"""
Proof by compute
Contains full implementation with prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class ComputeAction(BaseAction):
    """Action to use by(compute) in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "This action performs proof by computation: it simplifies spec functions on concrete, constant values (e.g., 0, 1, seq![42]) or on ranges of concrete integers (e.g., 1 to 100)."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Describe what expressions to compute and what concrete argument value or argument value-range to use."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Consider this action when the asserted expression contains constant variables, and zero or just one integer variable whose value is bounded. Furthermore, if the expression contains complicated computation, such as recursion, bit operation, multiplication, we **should** definitely use this by-compute action. The reason is that the verifier requires special mode to reason about bit-operations, non-linear operations, and can only expand a recursive function a small number of times. And yet, the `compute` engine is not limited by any of these, as long as there is at most one bounded integer variable in the expression. ***Note***: this action should be used BEFORE case analysis, because case-analysis may introduce more variables into the asserted expression, causing by-compute not appliable."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Proof by computation should reduce error count"""
        return {"criteria": AcceptanceCriteria.ERROR_REDUCTION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the proof-by-computation action"""
        guidance = params.get("guidance", "")

        # Get failure context for the prompt (no skipping - just inform the LLM)
        failure_context = self._get_failure_context_prompt(observation, ActionType.COMPUTE)

        # Use self-contained repair implementation
        repaired_codes = self._compute(
            observation.code,
            observation.error,
            guidance=guidance,
            failure_context=failure_context,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        # Check if we got valid results
        result = self._create_result(observation, ActionType.COMPUTE, repaired_codes, guidance)

        # Record failure if the action didn't succeed
        if not result.success or not repaired_codes or repaired_codes == [observation.code]:
            self._record_failure(
                observation,
                ActionType.COMPUTE,
                "no_valid_candidates" if not repaired_codes else "no_changes_generated",
                params,
            )

        return result

    def _compute(
        self,
        code: str,
        verus_error,
        guidance: str = "",
        failure_context: str = "",
        num: int = None,
        temp: float = 1.0,
    ) -> list[str]:
        """Self-contained proof by compute implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("compute")

        # Add failure context if available
        self.logger.info(f"Failure context: {failure_context}")
        if failure_context:
            instruction += f"\n\n{failure_context}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""## Task

Fix this failed assertion:

{assertion_info}"""

        # Add guidance if provided
        if guidance:
            query += f"\n\nSpecific guidance: {guidance}"

        query += f"""

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
