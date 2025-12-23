"""
Fallback LLM repair action for general error handling
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class FallbackLLMRepairAction(BaseAction):
    """Fallback action that uses general LLM repair when specific actions fail"""

    @classmethod
    def get_action_type(cls) -> ActionType:
        return ActionType.FALLBACK_LLM_REPAIR

    @classmethod
    def get_description(cls) -> str:
        return "General LLM-based repair as fallback when specific repair strategies are not applicable."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Provide general guidance for fixing the error using LLM reasoning."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Fallback LLM repair should improve verification"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the fallback LLM repair action"""
        guidance = params.get("guidance", "Apply general LLM-based repair")

        # Load the fallback LLM repair instruction
        instruction = load_prompt("fallback_llm_repair")

        # Get examples for assertion repair
        # examples = GlobalConfig.get_refinement().get_examples("assert-trigger")

        # Format the error information
        error_trace = observation.error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        # Format the query
        query = self.format_query_template("failed_assertion", assertion_info, observation.code)

        # Write debug file
        # self.write_debug_file("fallback-llm-query.txt", instruction + "\n\n" + query)

        # Invoke LLM with the loaded instruction
        candidates = self.invoke_llm(
            self.config.aoai_debug_model,
            instruction,
            query,
            self.default_system,
            answer_num=self.get_action_candidate_num(),
            max_tokens=4096,
            temp=1.0,
            original_code=observation.code,
        )

        if candidates:
            return self._create_result(
                observation=observation,
                action_type=ActionType.FALLBACK_LLM_REPAIR,
                repaired_codes=candidates,
                guidance=guidance,
            )
        else:
            return self._create_result(
                observation=observation,
                action_type=ActionType.FALLBACK_LLM_REPAIR,
                repaired_codes=[],
                guidance=guidance,
            )
