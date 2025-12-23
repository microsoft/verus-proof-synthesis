"""
Case Analysis Action
Adds case analysis to the proof.
Contains full implementation with prompts and examples.
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class CaseAnalysisAction(BaseAction):
    """Action to use case analysis in the proof"""

    @classmethod
    def get_description(cls) -> str:
        return "If the failing assertion requires case analysis with different proofs for each case, inline a spec function from a failing assertion or known facts (e.g. preconditions) which uses branching."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Identify the cases that should be used and relevant spec function(s)."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when when the proof needs to consider different cases based on the given definitions. Most effective when preconditions or spec function definitions contain branching that needs to be analyzed differently for each case. **Note:** for a recursive spec function which requires induction, you **must** use the induction action instead of this one; if the expression contains only one integer variable whose value is bounded, you **must** use by-compute action instead of this one."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Case analysis should not affect verified code"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the case analysis action"""
        guidance = params.get("guidance", "")

        # Get failure context for the prompt (no skipping - just inform the LLM)
        failure_context = self._get_failure_context_prompt(observation, ActionType.CASE_ANALYSIS)

        # Use self-contained repair implementation
        repaired_codes = self._repair_case_analysis(
            observation.code,
            observation.error,
            guidance=guidance,
            failure_context=failure_context,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        # Check if we got valid results
        result = self._create_result(
            observation, ActionType.CASE_ANALYSIS, repaired_codes, guidance
        )

        # Record failure if the action didn't succeed
        if not result.success or not repaired_codes or repaired_codes == [observation.code]:
            self._record_failure(
                observation,
                ActionType.CASE_ANALYSIS,
                "no_valid_candidates" if not repaired_codes else "no_changes_generated",
                params,
            )

        return result

    def _repair_case_analysis(
        self,
        code: str,
        verus_error,
        guidance: str = "",
        failure_context: str = "",
        num: int = None,
        temp: float = 1.0,
    ) -> list[str]:
        """Self-contained case analysis repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = load_prompt("case_analysis")

        # Add failure context if available
        if failure_context:
            instruction += f"\n\n{failure_context}"

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
