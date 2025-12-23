"""
Merged Prompt Ablation Action
This action merges all prompts from enabled actions for repair_assert agent into a single large prompt.
Used for ablation studies to test the effectiveness of action decomposition vs. single large prompt.
"""

import re
from typing import Any

from ..shared_types import AcceptanceCriteria, ActionResult, Observation
from .action_types import ActionType
from .base_action import BaseAction
from .prompt_loader import load_prompt


class MergedPromptAblationAction(BaseAction):
    """
    Ablation study action that merges all enabled action prompts into one large prompt.
    Instead of selecting specific actions, this gives the LLM all repair strategies at once.
    """

    def __init__(self):
        super().__init__()

        # List of actions to merge prompts from (same as repair_assert enabled actions)
        self.enabled_actions = [
            ActionType.INSTANTIATE_FORALL,
            ActionType.INSTANTIATE_EXISTS,
            ActionType.CASE_ANALYSIS,
            ActionType.REVEAL_OPAQUE,
            ActionType.EXTENSIONAL_EQUALITY,
            ActionType.INDUCTION,
            ActionType.INDUCTIVE_LEMMA,
            ActionType.REVEAL_WITH_FUEL,
            ActionType.COMPUTE,
            ActionType.SEQSETMAP,
            ActionType.NONLINEAR_ARITHMETIC,
            ActionType.BIT_VECTOR_REASONING,
            ActionType.ADD_TRIGGER_ASSERT,
            ActionType.USELEMMA,
            ActionType.LOOPINV,
        ]

        # Mapping from action types to their prompt files
        self.action_prompt_mapping = {
            ActionType.INSTANTIATE_FORALL: "instantiate_forall",
            ActionType.INSTANTIATE_EXISTS: "instantiate_exists",
            ActionType.CASE_ANALYSIS: "case_analysis",
            ActionType.REVEAL_OPAQUE: "reveal_opaque",
            ActionType.EXTENSIONAL_EQUALITY: "extensional_equality",
            ActionType.INDUCTION: "induction",
            ActionType.INDUCTIVE_LEMMA: "inductive_lemma",
            ActionType.REVEAL_WITH_FUEL: "reveal_with_fuel",
            ActionType.COMPUTE: "compute",
            ActionType.SEQSETMAP: "seqsetmap",
            ActionType.NONLINEAR_ARITHMETIC: "arithmetic_reasoning",
            ActionType.BIT_VECTOR_REASONING: "bit_vector_reasoning",
            ActionType.ADD_TRIGGER_ASSERT: "add_trigger_assert",
            ActionType.USELEMMA: "uselemma",
            ActionType.LOOPINV: "loopinv",
        }

    @classmethod
    def get_description(cls) -> str:
        return "Ablation study action that merges all enabled repair action prompts into a single comprehensive prompt"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Apply all available repair strategies in a single comprehensive analysis and repair attempt"

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Use for ablation studies to compare single large prompt vs. action decomposition approaches"

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Default acceptance criteria - can be overridden based on strategy"""
        return {"criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED, "threshold": 0.0}

    def get_strategy_based_acceptance_criteria(self, strategy: str) -> dict[str, Any]:
        """Get acceptance criteria based on the detected strategy"""
        # Map strategies to their appropriate acceptance criteria
        strategy_criteria_map = {
            # Actions that should not affect verified code (structural changes)
            "reveal_opaque": {
                "criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED,
                "threshold": 0.0,
            },
            "reveal_with_fuel": {
                "criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED,
                "threshold": 0.0,
            },
            # Actions that should not add bandaid assertions
            "instantiate_forall": {
                "criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS,
                "threshold": 0.0,
            },
            "instantiate_exists": {
                "criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS,
                "threshold": 0.0,
            },
            "case_analysis": {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0},
            "induction": {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0},
            "extensional_equality": {
                "criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS,
                "threshold": 0.0,
            },
            "compute": {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0},
            "nonlinear_arithmetic": {
                "criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS,
                "threshold": 0.0,
            },
            "bit_vector_reasoning": {
                "criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS,
                "threshold": 0.0,
            },
            # Actions that can allow loop-related verified increases
            "loopinv": {
                "criteria": AcceptanceCriteria.DONT_AFFECT_VERIFIED_EXLOOP,
                "threshold": 0.0,
            },
            # Actions that should improve verification
            "add_trigger_assert": {
                "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
                "threshold": 0.0,
            },
            "uselemma": {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0},
            "inductive_lemma": {
                "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
                "threshold": 0.0,
            },
            "seqsetmap": {
                "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
                "threshold": 0.0,
            },
        }

        # Get strategy-specific criteria or fall back to default
        return strategy_criteria_map.get(strategy, self.get_acceptance_criteria())

    def create_strategy_based_acceptance_evaluator(self, strategy: str):
        """Create an AcceptanceEvaluator based on the detected strategy"""
        from ..shared_types import AcceptanceEvaluator

        criteria_config = self.get_strategy_based_acceptance_criteria(strategy)
        criteria = criteria_config["criteria"]
        threshold = criteria_config.get("threshold", 0.0)

        return AcceptanceEvaluator(criteria=criteria, threshold=threshold)

    def _load_and_merge_prompts(self) -> str:
        """Load and merge all enabled action prompts into a single comprehensive prompt"""
        merged_sections = []

        merged_sections.append("# Comprehensive Verus Assertion Repair Strategies")
        merged_sections.append(
            "You are provided with multiple repair strategies that can be applied to fix Verus assertion failures."
        )
        merged_sections.append(
            "Analyze the code and error, then apply the most appropriate strategy or combination of strategies."
        )
        merged_sections.append("")

        # Import action_registry to get metadata
        from . import action_registry

        for action_type in self.enabled_actions:
            if action_type in self.action_prompt_mapping:
                prompt_name = self.action_prompt_mapping[action_type]
                try:
                    prompt_content = load_prompt(prompt_name)

                    # Add section header
                    section_title = f"# Strategy: {action_type.value.upper().replace('_', ' ')}"
                    merged_sections.append(section_title)
                    merged_sections.append("")

                    # Get and add when_to_apply information
                    try:
                        action_metadata = action_registry.get_action_metadata(action_type)
                        when_to_apply = action_metadata.get("when_to_apply", "")
                        if when_to_apply:
                            merged_sections.append(f"**When to apply**: {when_to_apply}")
                            merged_sections.append("")
                    except Exception as e:
                        self.logger.warning(f"Could not get metadata for {action_type.value}: {e}")

                    # Add the prompt content
                    merged_sections.append(prompt_content)
                    merged_sections.append("")
                    merged_sections.append("---")
                    merged_sections.append("")

                except FileNotFoundError:
                    self.logger.warning(
                        f"Prompt file not found for {action_type.value}: {prompt_name}.md"
                    )
                    # Add a fallback description with when_to_apply if available
                    merged_sections.append(
                        f"## Strategy: {action_type.value.upper().replace('_', ' ')}"
                    )

                    # Try to get when_to_apply for fallback case too
                    try:
                        action_metadata = action_registry.get_action_metadata(action_type)
                        when_to_apply = action_metadata.get("when_to_apply", "")
                        if when_to_apply:
                            merged_sections.append(f"**When to apply**: {when_to_apply}")
                        merged_sections.append(
                            f"Apply {action_type.value} repair strategy for assertion failures."
                        )
                    except Exception as e:
                        merged_sections.append(
                            f"Apply {action_type.value} repair strategy for assertion failures."
                        )
                        self.logger.warning(
                            f"Could not get metadata for fallback {action_type.value}: {e}"
                        )

                    merged_sections.append("")
                    merged_sections.append("---")
                    merged_sections.append("")

        # Add final instruction
        merged_sections.append("# Instructions")
        merged_sections.append("1. Analyze the assertion failure and surrounding code context")
        merged_sections.append(
            "2. Identify which repair strategy or strategies are most appropriate"
        )
        merged_sections.append(
            "3. Apply the selected strategy to generate a fixed version of the code"
        )
        merged_sections.append(
            "4. Ensure the fix addresses the root cause of the assertion failure"
        )
        merged_sections.append("5. Maintain code correctness and readability")
        merged_sections.append("")
        merged_sections.append("# Output Format")
        merged_sections.append("CRITICAL: Your response MUST start with exactly this format:")
        merged_sections.append("")
        merged_sections.append("STRATEGY: [strategy_name]")
        merged_sections.append("")
        merged_sections.append("Where [strategy_name] must be one of these exact values:")
        strategy_names = [action.value.upper() for action in self.enabled_actions]
        merged_sections.append("- " + "\n- ".join(strategy_names))
        merged_sections.append("")
        merged_sections.append("Example:")
        merged_sections.append("STRATEGY: CASE_ANALYSIS")
        merged_sections.append("")
        merged_sections.append("After the STRATEGY line, provide the fixed code.")

        return "\n".join(merged_sections)

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the merged prompt ablation repair"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes, selected_strategies = self._repair_merged_prompt_ablation(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        # Create result with strategy selection information
        result = self._create_result(
            observation, ActionType.MERGED_PROMPT_ABLATION, repaired_codes, guidance
        )

        # Add selected strategies to metadata
        if hasattr(result, "metadata"):
            result.metadata["selected_strategies"] = selected_strategies
        else:
            result.metadata = {"selected_strategies": selected_strategies}

        # Determine acceptance criteria based on strategies
        # For multiple candidates with different strategies, we need to choose the most appropriate criteria
        result.metadata["strategy_based_acceptance"] = True
        result.metadata["candidate_strategies"] = selected_strategies

        # Choose primary strategy for overall acceptance criteria
        # Priority: use the most common strategy, or fall back to the first one
        if selected_strategies:
            # Count strategy occurrences
            strategy_counts = {}
            for strategy in selected_strategies:
                strategy_counts[strategy] = strategy_counts.get(strategy, 0) + 1

            # Get the most common strategy (or first one if tie)
            primary_strategy = max(strategy_counts.keys(), key=strategy_counts.get)

            # Set strategy-based acceptance criteria
            strategy_criteria = self.get_strategy_based_acceptance_criteria(primary_strategy)
            result.metadata["primary_strategy"] = primary_strategy
            result.metadata["strategy_acceptance_criteria"] = strategy_criteria

            # Override the acceptance evaluator with strategy-based one
            result.acceptance_evaluator = self.create_strategy_based_acceptance_evaluator(
                primary_strategy
            )

            self.logger.info(f"LLM selected strategies: {selected_strategies}")
            self.logger.info(
                f"Primary strategy: {primary_strategy}, acceptance criteria: {strategy_criteria['criteria'].value}"
            )
        else:
            result.metadata["primary_strategy"] = "unknown"
            result.metadata["strategy_acceptance_criteria"] = self.get_acceptance_criteria()
            self.logger.warning("No strategies detected, using default acceptance criteria")

        return result

    def _repair_merged_prompt_ablation(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> tuple[list[str], list[str]]:
        """Self-contained merged prompt ablation repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_debug_model

        instruction = self._load_and_merge_prompts()

        # Add guidance if provided
        # if guidance:
        #     instruction += f"\n\nSpecific guidance: {guidance}"

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

        # Get examples from the existing example system

        # Get raw LLM responses
        raw_responses = self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )

        # Parse strategies and cleaned codes from responses
        repaired_codes = []
        selected_strategies = []

        for response in raw_responses:
            strategy, cleaned_code = self._parse_strategy_and_code(response)
            selected_strategies.append(strategy)
            repaired_codes.append(cleaned_code)

        return repaired_codes, selected_strategies

    def _parse_strategy_and_code(self, response: str) -> tuple[str, str]:
        """Parse the strategy and code from LLM response"""
        # Look for STRATEGY: line at the beginning
        strategy_match = re.search(r"^STRATEGY:\s*([A-Z_]+)", response, re.MULTILINE)
        if strategy_match:
            strategy = strategy_match.group(1).lower()
            # Remove the strategy line from the code
            cleaned_response = re.sub(r"^STRATEGY:.*$", "", response, flags=re.MULTILINE).strip()
        else:
            # Fallback: try to detect strategy from content
            strategy = "unknown"
            cleaned_response = response
            self.logger.warning(
                "No STRATEGY: line found in LLM response and could not infer strategy"
            )

        return strategy, cleaned_response
