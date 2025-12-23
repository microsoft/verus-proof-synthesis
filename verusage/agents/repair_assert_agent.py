import json
import pprint
from pathlib import Path

from global_config import GlobalConfig
from veval import VerusError, VerusErrorType

from utils import comment_code_with_error, extract_and_parse_json, remove_error_comment

from .actions import ActionType, action_registry
from .actions.prompt_loader import format_prompt
from .base_agent import ActionResult, BaseAgent, Observation, ReasoningResult

# Import vstd library components for reasoning phase
try:
    from vstd_library import ResultFormatter, VstdSearchEngine
    from vstd_library.token_similarity_sampler import TokenSimilaritySampler

    VSTD_AVAILABLE = True
except ImportError:
    VSTD_AVAILABLE = False


class AssertionErrorAgent(BaseAgent):
    def __init__(
        self,
        ablation_mode=False,
        accept_rule="default",
        args=None,
    ):
        super().__init__()
        self.ablation_mode = ablation_mode
        self.accept_rule = accept_rule
        self.args = args

        # Initialize vstd token similarity sampler (no LLM needed!)
        self.vstd_sampler = None
        self.vstd_formatter = None

        if VSTD_AVAILABLE:
            try:
                # vstd_index.json should be in vstd_library directory
                index_path = Path(__file__).parent.parent / "vstd_library" / "vstd_index.json"
                if index_path.exists():
                    # Create sampler for token similarity search
                    self.vstd_sampler = TokenSimilaritySampler(str(index_path))
                    # Create search engine for formatter (to look up context functions)
                    vstd_engine = VstdSearchEngine(str(index_path))
                    # Formatter uses search engine to find helper functions
                    self.vstd_formatter = ResultFormatter(search_engine=vstd_engine)
                    self.logger.info(f"vstd token similarity sampler initialized from {index_path}")
                else:
                    self.logger.warning(f"vstd index not found at {index_path}")
            except Exception as e:
                self.logger.warning(f"Failed to initialize vstd sampler: {e}")

    def can_handle(self, error: VerusError) -> bool:
        return error.error == VerusErrorType.AssertFail

    def observe(self, code: str, error: VerusError) -> Observation:
        """Observe assertion failure and analyze context"""
        error_trace = error.trace[0]
        error_location = (error_trace.lines[0], error_trace.lines[1])
        error_text = error_trace.get_text()

        # Extract surrounding context (30 lines before and after)
        lines = code.splitlines()
        start_line = max(0, error_location[0] - 30)
        end_line = min(len(lines), error_location[1] + 30)
        surrounding_context = "\n".join(lines[start_line:end_line])

        return Observation(
            code=code,
            error=error,
            error_location=error_location,
            error_text=error_text,
            surrounding_context=surrounding_context,
        )

    def reason(self, observation: Observation) -> ReasoningResult:
        """Use LLM to reason about the assertion failure and plan repair strategy"""
        # In ablation mode, directly return the merged prompt action without LLM reasoning
        if self.ablation_mode:
            self.logger.info("Ablation mode enabled - using merged prompt action directly")
            return self._ablation_mode_reasoning(observation)

        return self._llm_based_reasoning(observation)

    def _ablation_mode_reasoning(self, observation: Observation) -> ReasoningResult:
        """Ablation mode reasoning - directly selects merged prompt action"""
        self.logger.info("Using ablation mode - directly selecting merged prompt action")

        return ReasoningResult(
            primary_action=ActionType.MERGED_PROMPT_ABLATION,
            secondary_actions=[],  # No secondary actions in ablation mode
            reasoning_explanation="Ablation study mode: Using merged prompt action that combines all repair strategies",
            action_parameters={
                "guidance": "Apply comprehensive analysis using all available repair strategies",
                "ablation_mode": True,
            },
        )

    def _get_assertion_relevant_actions(self) -> list[ActionType]:
        """Get the list of actions relevant for assertion repair"""
        assertion_actions = [
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
            ActionType.INTEGER_RING,
            ActionType.BIT_VECTOR_REASONING,
            ActionType.ADD_TRIGGER_ASSERT,
            ActionType.USELEMMA,
            ActionType.LOOPINV,
        ]

        # Apply preprocessing-based filtering and boosting
        filtered_actions = self.filter_actions_with_preprocessing(assertion_actions)
        boosted_actions = self.boost_actions_with_preprocessing(filtered_actions)

        return boosted_actions

    def _generate_action_descriptions(self) -> str:
        """Generate action descriptions dynamically from the action registry"""
        relevant_actions = self._get_assertion_relevant_actions()
        descriptions = []

        # Add preprocessing context if available (BEFORE the actions)
        preprocessing_context = ""
        if self.code_analysis:
            preprocessing_context = "### PREPROCESSING ANALYSIS:\n"
            if self.code_analysis.has_lemmas():
                preprocessing_context += (
                    f"- Available lemmas: {', '.join(self.code_analysis.lemmas)}\n"
                )
            else:
                preprocessing_context += "- No lemmas available\n"

            if self.code_analysis.has_recursive_functions():
                preprocessing_context += f"- Recursive functions detected: {', '.join(self.code_analysis.recursive_functions)} (please consider more using COMPUTE action)\n"

            if self.code_analysis.has_opaque_functions():
                preprocessing_context += f"- Opaque functions available: {', '.join(self.code_analysis.opaque_functions)}\n"
            else:
                preprocessing_context += "- No opaque functions found\n"
            preprocessing_context += "\n"
            preprocessing_context += "### ACTIONS:\n"
        for action_type in relevant_actions:
            try:
                metadata = action_registry.get_action_metadata(action_type)
                description = metadata["description"]
                guidance = metadata["guidance_template"]
                when_to_apply = metadata["when_to_apply"]

                # Format as: ACTION_NAME: Description
                # When to apply: ...
                # Guidance: ...
                action_desc = f"- **{action_type.value.upper()}**: {description}"
                if when_to_apply:
                    action_desc += f"\n  *When to apply*: {when_to_apply}"
                if guidance:
                    action_desc += f"\n  *Guidance*: {guidance}"

                # Add preprocessing-specific notes
                if (
                    action_type == ActionType.USELEMMA
                    and self.code_analysis
                    and self.code_analysis.has_lemmas()
                ):
                    action_desc += f"\n  *Available lemmas*: {', '.join(self.code_analysis.lemmas)}"
                elif (
                    action_type == ActionType.COMPUTE
                    and self.code_analysis
                    and self.code_analysis.has_recursive_functions()
                ):
                    action_desc += f"\n  *Recursive functions*: {', '.join(self.code_analysis.recursive_functions)}"
                elif (
                    action_type == ActionType.REVEAL_OPAQUE
                    and self.code_analysis
                    and self.code_analysis.has_opaque_functions()
                ):
                    action_desc += (
                        f"\n  *Opaque functions*: {', '.join(self.code_analysis.opaque_functions)}"
                    )

                descriptions.append(action_desc)

            except Exception as e:
                # Fallback for missing actions
                descriptions.append(
                    f"- **{action_type.value.upper()}**: Action for assertion repair"
                )
                self.logger.warning(f"Could not get metadata for {action_type.value}: {e}")

        return preprocessing_context + "\n".join(descriptions)

    def _get_vstd_examples(self, observation: Observation, max_examples: int = 5) -> str:
        """Get relevant vstd examples using token similarity (no LLM!)

        This method directly samples examples based on token overlap between
        error context and vstd library content.

        Args:
            observation: The observation containing code and error information
            max_examples: Maximum number of examples to retrieve (default: 5)

        Returns:
            Formatted string with vstd examples (signature + body + context), or empty string if unavailable
        """
        if not VSTD_AVAILABLE or not self.vstd_sampler or not self.vstd_formatter:
            return ""

        try:
            # Directly sample examples by token similarity (no LLM!)
            self.logger.info("Sampling vstd examples by token similarity...")
            self.logger.info(f"Error text: {observation.error_text[:100]}...")
            self.logger.info(f"Context length: {len(observation.surrounding_context)}")

            sampled_results = self.vstd_sampler.sample_examples(
                error_text=observation.error_text,
                code_context=observation.surrounding_context,
                top_k=max_examples,
            )

            if not sampled_results:
                self.logger.debug("No examples sampled")
                return ""

            self.logger.info(f"Sampled {len(sampled_results)} vstd examples by token similarity")
            for result in sampled_results:
                self.logger.debug(f"  {result.name}: score={result.score:.3f}")
                self.logger.debug(
                    f"  Result type: {type(result)}, content type: {type(result.content)}"
                )

            # Format for reasoning phase using existing formatter
            # This will show: doc comment + signature + body + context (helper functions)
            self.logger.info(
                f"Formatting {len(sampled_results)} results with max_results={max_examples * 2}"
            )
            formatted = self.vstd_formatter.format_for_reasoning(
                sampled_results, max_results=(max_examples * 2)
            )

            if formatted:
                self.logger.info("Successfully sampled and formatted vstd examples")
                print(formatted)
                return "\n\n" + formatted
            else:
                return ""

        except Exception as e:
            import traceback

            self.logger.error(f"Failed to sample vstd examples: {e}")
            self.logger.error(f"Exception type: {type(e)}")
            self.logger.error(f"Full traceback:\n{traceback.format_exc()}")
            return ""

    def _llm_based_reasoning(self, observation: Observation) -> ReasoningResult:
        """Use LLM to analyze the observation and determine the best repair strategy

        ENHANCED PARAMETER-DRIVEN REASONING:
        The LLM now provides specific parameters for each action type, enabling:
        - ADD_TRIGGER_ASSERT: quantified assertions, trigger patterns, instantiation values
        - CASE_ANALYSIS: case conditions, case-specific assertions
        - COMPUTE: computation hints, reveal expressions
        - And more...

        This allows for much more targeted and effective repairs compared to generic actions.
        """

        # Now we comment the lines with the error
        observation.code = comment_code_with_error(observation.code, observation.error)

        # Generate dynamic action descriptions
        action_descriptions = self._generate_action_descriptions()

        # Add vstd examples if relevant (Phase 4 enhancement)
        vstd_examples = self._get_vstd_examples(observation)
        if vstd_examples:
            action_descriptions += vstd_examples
            self.logger.info("Enhanced reasoning with vstd library examples")

        # Prepare reasoning prompt
        system_prompt = format_prompt(
            "assertion_reasoning_pipeline", action_descriptions=action_descriptions
        )

        history_text = GlobalConfig.get_metadata_store().format_action_history(8)

        # Create detailed analysis prompt
        analysis_prompt = f"""Please analyze this assertion failure following the systematic pipeline:

## Error Information
- Error Type: {observation.error.error.name}
- Error Location: Lines {observation.error_location[0]}-{observation.error_location[1]}
- Error Text: {observation.error_text}

## Code Context (surrounding area)
```rust
{observation.surrounding_context}
```

## Full Code
```rust
{observation.code}
```

{history_text}
"""

        reasoning_file = self.get_reasoning_file_path(f"reasoning-{self._attempt_id}.txt")
        reasoning_file.parent.mkdir(parents=True, exist_ok=True)
        reasoning_file.write_text(system_prompt + "\n\n" + analysis_prompt, encoding="utf-8")

        try:
            # Call LLM for reasoning
            responses = self.llm.infer_llm(
                engine=self.config.aoai_debug_model,
                instruction=system_prompt,
                exemplars=[],
                query=analysis_prompt,
                system_info="You are a Verus verification expert focused on precise analysis and reasoning.",
                answer_num=1,
                max_tokens=8192,
                temp=1.0,
            )

            self.logger.info("🔍 LLM Response:")
            self.logger.info("=" * 80)
            self.logger.info(pprint.pformat(responses, indent=2, width=80))
            self.logger.info("=" * 80)

            reasoning_answer_file = self.get_reasoning_file_path(
                f"reasoning-answer-{self._attempt_id}.txt"
            )
            reasoning_answer_file.write_text(responses[0], encoding="utf-8")

            if not responses or not responses[0]:
                raise ValueError("LLM returned empty response")

            # Parse LLM response using utility function
            response = responses[0].strip()

            try:
                reasoning_data = extract_and_parse_json(response)
                if reasoning_data is None:
                    raise ValueError("No JSON found in LLM response")
            except json.JSONDecodeError as e:
                raise ValueError(f"JSON parse error: {e}") from e

            # Validate and convert to ReasoningResult
            try:
                primary_action = self._parse_action_type(reasoning_data.get("primary_action"))

                # Parse secondary actions (top 5 alternative actions)
                secondary_actions = []
                if "secondary_actions" in reasoning_data:
                    secondary_actions = [
                        self._parse_action_type(action)
                        for action in reasoning_data.get("secondary_actions", [])
                    ]
                    # Limit to top 5
                    secondary_actions = secondary_actions[:5]

                # Extract pipeline-specific information
                root_cause_analysis = reasoning_data.get("root_cause_analysis", "")

                # Enhanced reasoning explanation with pipeline info
                enhanced_explanation = f"Pipeline Analysis: {root_cause_analysis}\n"
                if secondary_actions:
                    enhanced_explanation += (
                        f"Secondary Actions: {[action.value for action in secondary_actions]}\n"
                    )

                self.logger.warning(f"Primary Action: {primary_action.value}")
                self.logger.warning(
                    f"Secondary Actions: {[action.value for action in secondary_actions]}"
                )

                return ReasoningResult(
                    primary_action=primary_action,
                    secondary_actions=secondary_actions,
                    reasoning_explanation=enhanced_explanation,
                    action_parameters=reasoning_data.get("action_parameters", {}),
                )

            except (ValueError, KeyError) as e:
                self.logger.error(f"Invalid reasoning data: {e}")
                raise ValueError(f"Invalid reasoning data: {e}") from e

        except Exception as e:
            self.logger.error(f"LLM reasoning failed: {e}")
            raise

    def act(self, observation: Observation, reasoning: ReasoningResult) -> ActionResult:
        """Execute the planned repair action using the action registry"""
        action_type = reasoning.primary_action
        params = reasoning.action_parameters
        self.logger.info(f"Action type: {action_type}")

        # Now we comment the lines with the error
        observation.code = comment_code_with_error(observation.code, observation.error)

        try:
            # Get the action class from the registry
            action_class = action_registry.get_action_class(action_type)

            # Create an instance of the action
            action_instance = action_class()

            # Set failure manager if available
            if self.failure_manager:
                action_instance.set_failure_manager(self.failure_manager)

            # Execute the action
            result = action_instance.execute(observation, params)

            # Remove error comments from all candidates
            result.candidates = [remove_error_comment(c) for c in result.candidates]

            return result

        except Exception as e:
            return ActionResult(
                action_taken=action_type,
                explanation=f"Action execution failed: {e}",
                candidates=[],  # Empty list = failure
                original_code=observation.code,
            )

    def mark_last_action_accepted(self, accepted: bool, feedback: str = ""):
        """Mark the last action as accepted or rejected with optional feedback"""
        # TODO: Update to work with RepairAttemptMetadata in global store
        repair_history = GlobalConfig.get_metadata_store().get_all_attempts()
        if repair_history:
            last_attempt = repair_history[-1]
            status = "accepted" if accepted else "rejected"
            self.logger.info(f"Action {last_attempt.primary_action} marked as {status}")
            if feedback:
                self.logger.info(f"Feedback: {feedback}")
