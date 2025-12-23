"""
Base Action Class
Defines the interface that all repair actions must implement.
Actions can now directly access repair modules without delegation methods.
"""

from abc import ABC, abstractmethod
from typing import Any

from global_config import GlobalConfig
from llm_utils import call_llm_with_diff_format

# Import shared classes from shared_types to avoid circular imports
from ..shared_types import AcceptanceCriteria, AcceptanceEvaluator, ActionResult, Observation


class BaseAction(ABC):
    """
    Base class for all repair actions.
    Actions are now self-contained and can directly access repair modules.
    """

    def __init__(self):
        # Access global configuration and resources
        self.config = GlobalConfig.get_config()
        self.logger = GlobalConfig.get_logger()
        self.llm = GlobalConfig.get_llm()
        self.failure_manager = None  # Will be set by main loop

        self.default_system = "You are a Verus verification expert. You are given a Verus program and an error trace. You need to fix the error in the program. Please focus on the Verus grammar and semantics"

    @classmethod
    @abstractmethod
    def get_description(cls) -> str:
        """Get a human-readable description of what this action does"""
        pass

    @classmethod
    @abstractmethod
    def get_guidance_template(cls) -> str:
        """Get the guidance template for the LLM system prompt"""
        pass

    @classmethod
    def get_when_to_apply(cls) -> str:
        """Get a description of when this action should be applied (default implementation)"""
        return "Apply when the assertion failure can be addressed with this repair strategy."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Get the acceptance criteria for this action (fallback implementation)"""
        return {
            "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
            "threshold": 0.0,
        }

    @staticmethod
    def sort_action_based_on_criteria(
        actions: list["BaseAction"],
    ) -> list["BaseAction"]:
        """
        Sort actions based on their acceptance criteria.
        This is a static method to allow sorting without needing an instance.
        """

        def sort_key(action: "BaseAction") -> AcceptanceCriteria:
            criteria = action.get_acceptance_criteria()
            return criteria.get("criteria", AcceptanceCriteria.DONT_AFFECT_VERIFIED)

        sorted_actions = sorted(actions, key=sort_key, reverse=True)
        return sorted_actions

    @staticmethod
    def filter_action_based_on_criteria(
        actions: list["BaseAction"],
        least_criteria: AcceptanceCriteria = AcceptanceCriteria.NO_BANDAID_ASSERTS,
    ) -> list["BaseAction"]:
        """
        Sort actions based on their acceptance criteria.
        This is a static method to allow sorting without needing an instance.
        """

        def filter(action: "BaseAction") -> bool:
            criteria = action.get_acceptance_criteria()
            return (
                criteria.get("criteria", AcceptanceCriteria.DONT_AFFECT_VERIFIED) > least_criteria
            )

        filtered_actions = [action for action in actions if filter(action)]
        return filtered_actions

    @classmethod
    def create_acceptance_evaluator(cls) -> AcceptanceEvaluator:
        """Create an AcceptanceEvaluator based on this action's criteria"""
        criteria_config = cls.get_acceptance_criteria()

        # Get criteria from the new format
        if "criteria" in criteria_config:
            # New format: direct AcceptanceCriteria enum
            criteria = criteria_config["criteria"]
            threshold = criteria_config.get("threshold", 0.0)
        else:
            # Fallback for old format (should not happen after migration)
            criteria = AcceptanceCriteria.VERIFICATION_IMPROVEMENT
        threshold = criteria_config.get("tolerance_threshold", 0.0)

        return AcceptanceEvaluator(criteria=criteria, threshold=threshold)

    def set_failure_manager(self, failure_manager):
        """Set the failure manager instance"""
        self.failure_manager = failure_manager

    def _get_failure_context_prompt(self, observation: Observation, action_type) -> str:
        """Get failure context prompt if failure manager is available"""
        if self.failure_manager:
            error_context = f"{observation.error_type}:{observation.error_text[:100]}"
            self.logger.debug(f"Looking for failure context for {action_type.value} on state hash")
            return self.failure_manager.generate_failure_context_prompt(
                observation.code, action_type.value, error_context
            )
        else:
            self.logger.warning(f"No failure manager available for {action_type.value}")
        return ""

    def _should_skip_action(self, observation: Observation, action_type) -> bool:
        """Check if action should be skipped due to failure history - DISABLED per user request"""
        # User wants failure knowledge but no skipping
        return False

    def _record_failure(
        self, observation: Observation, action_type, failure_reason: str, params: dict
    ):
        """Record action failure in failure manager"""
        if self.failure_manager:
            error_context = f"{observation.error_type}:{observation.error_text[:100]}"
            self.failure_manager.record_failure(
                code=observation.code,
                action_type=action_type.value,
                failure_reason=failure_reason,
                action_parameters=params,
                error_context=error_context,
            )

    @abstractmethod
    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """
        Execute the action with the given observation and parameters.

        Args:
            observation: Contains the code, error, and context information
            params: Parameters from the LLM reasoning, typically containing 'guidance'

        Returns:
            ActionResult with the repaired code and metadata
        """
        pass

    def _create_result(
        self, observation: Observation, action_type, repaired_codes: list, guidance: str
    ) -> ActionResult:
        """Helper method to create standardized ActionResult"""

        # Create action-specific acceptance evaluator
        acceptance_evaluator = self.create_acceptance_evaluator()

        if repaired_codes and any(repaired_codes):
            valid_candidates = [code for code in repaired_codes if code and code.strip()]

            if valid_candidates:
                explanation = f"Generated {len(valid_candidates)} {action_type.value} candidates"
                if guidance:
                    explanation += (
                        f" (guidance: {guidance[:100]}...)"
                        if len(guidance) > 100
                        else f" (guidance: {guidance})"
                    )

                result = ActionResult(
                    action_taken=action_type,
                    explanation=explanation,
                    candidates=valid_candidates,
                    action_parameters={"guidance": guidance},
                    acceptance_evaluator=acceptance_evaluator,
                    original_code=observation.code,  # Set original code for diff generation
                )

                # Log diff information for each candidate
                if result.candidate_diffs:
                    self.logger.info(f"Generated {len(valid_candidates)} candidates with diffs:")
                    for i, diff in enumerate(result.candidate_diffs):
                        self.logger.info(f"  Candidate {i+1}: {diff.get_summary()}")

                return result

        return ActionResult(
            action_taken=action_type,
            explanation=f"Failed to generate {action_type.value} candidates",
            candidates=[],  # Empty list = failure (success property will return False)
            action_parameters={"guidance": guidance},
            acceptance_evaluator=acceptance_evaluator,
            original_code=observation.code,
        )

    def invoke_llm(
        self,
        engine,
        instruction,
        query,
        system,
        original_code="",
        examples=None,
        answer_num=1,
        max_tokens=4096,
        temp=1.0,
        skip_history=False,
    ):
        """
        For actions, we use the diff format to invoke the LLM.

        Examples can now be optionally provided for few-shot learning.
        NO refinement dependency - uses llm_utils directly.
        """
        if not skip_history:
            # Add the history data
            query += "\n\nPlease analyze the previous repair attempts below before proceeding:\n"
            query += GlobalConfig.get_metadata_store().format_action_history(5)

        # Add restriction against assume(...)
        query += "\n\n\nPlease don't use assume(...).\n"
        query += "Please follow the Rust and Verus syntax and best practices.\n"
        query += "Please use if-else statements to handle different cases, instead of using match statements with _ patterns.\n"
        query += "Prioritize SAFE changes that only modify ghost code (proofs, assertions, loop invariants) and leave the executable code (AST) exactly the same. Do NOT modify the `requires` or `ensures` clauses of the target function (though `decreases` is allowed). Modifying executable statements (e.g., extracting variables, changing loop bounds) is UNSAFE and will be rejected.\n"

        return call_llm_with_diff_format(
            engine=engine,
            instruction=instruction,
            query=query,
            system=system,
            original_code=original_code,
            examples=examples,
            answer_num=answer_num,
            max_tokens=max_tokens,
            temp=temp,
        )

    def get_action_candidate_num(self):
        """Get the number of candidates to generate for actions"""
        return 3

    def format_query_template(self, template_type: str, *args) -> str:
        """Format query templates for different error types"""
        templates = {
            "failed_assertion": "Failed assertion\n```\n{}```\n\nCode\n```\n{}\n```\n",
            "failed_precondition": "Failed pre-condition\n```\n{}```\n\nFailed location\n```\n{}```\n\nCode\n```\n{}\n```\n",
            "failed_postcondition": "Failed post-condition\n```\n{}```\n\nFailed location\n```\n{}```\n\nCode\n```\n{}\n```\n",
            "failed_invariant": "Failed invariant\n```\n{}```\n\nCode\n```\n{}\n```\n",
            "arithmetic_error": "Arithmetic underflow/overflow \n```\n{}```\n\nCode\n```\n{}\n```\n",
            "error_code": "Error\n```\n{}```\n\nCode\n```\n{}\n```\n",
        }

        template = templates.get(template_type, "Error\n```\n{}```\n\nCode\n```\n{}\n```\n")
        return template.format(*args)
