"""
Base Agent Module for Verus Code Repair
Contains foundational classes and abstract base agent for the repair framework.
"""

import pprint
import traceback
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any

from global_config import GlobalConfig
from veval import EvalScore, VerusError, VEval

from utils import clean_code, proof_completion_code_change_is_safe, verusfmt_code

from .actions import ActionType, BaseAction, action_registry
from .preprocessing import CodeAnalysis
from .repair_metadata import CandidateMetadata, RepairAttemptMetadata
from .shared_types import (
    AcceptanceCriteria,
    AcceptanceEvaluator,
    ActionResult,
    Observation,
    ReasoningResult,
    generate_simple_diff,
    write_to_temp_dir,
)


class BaseAgent(ABC):
    """Base class for repair agents following observation-reasoning-action pattern"""

    def __init__(self):
        # Access global configuration and resources
        self.config = GlobalConfig.get_config()
        self.logger = GlobalConfig.get_logger()
        self.llm = GlobalConfig.get_llm()

        self.code_analysis: CodeAnalysis | None = None  # Preprocessing analysis

        self._attempt_id = 0
        self.accept_rule = "default"  # Default acceptance rule
        self.swap_case_compute = False  # Flag to enable CASE_ANALYSIS/COMPUTE priority swap
        self.failure_manager = None  # Will be set by orchestrator

    def set_failure_manager(self, failure_manager):
        """Set the failure manager for this agent"""
        self.failure_manager = failure_manager

    def get_reasoning_file_path(self, filename: str) -> Path:
        """Get the path for a reasoning file"""
        reasoning_dir = GlobalConfig.get_temp_dir() / "reasoning"
        reasoning_dir.mkdir(parents=True, exist_ok=True)
        return reasoning_dir / filename

    def _parse_action_type(self, action_str: str) -> ActionType:
        """Parse action type from LLM response, handling both enum names and values"""
        if not action_str:
            return ActionType.FALLBACK_LLM_REPAIR

        action_str = action_str.strip().upper()

        # Try to match by enum name first (e.g., "MODIFY_QUANTIFIER")
        for action_type in ActionType:
            if action_type.name == action_str:
                return action_type

        # Try to match by enum value (e.g., "modify_quantifier")
        action_str_lower = action_str.lower()
        for action_type in ActionType:
            if action_type.value == action_str_lower:
                return action_type

        # Handle common variations
        action_mappings = {
            "ADD_TRIGGER": ActionType.ADD_TRIGGER_ASSERT,
            "TRIGGER_ASSERT": ActionType.ADD_TRIGGER_ASSERT,
            "INSTANTIATE_FORALL": ActionType.INSTANTIATE_FORALL,
            "INSTANTIATE_EXISTS": ActionType.INSTANTIATE_EXISTS,
            "MODIFY_LOOP_INVARIANT": ActionType.MODIFY_LOOP_INVARIANT,
            "FALLBACK": ActionType.FALLBACK_LLM_REPAIR,
        }

        return action_mappings.get(action_str, ActionType.FALLBACK_LLM_REPAIR)

    @abstractmethod
    def can_handle(self, error: VerusError) -> bool:
        """Check if this agent can handle the given error type"""
        pass

    @abstractmethod
    def observe(self, code: str, error: VerusError) -> Observation:
        """Phase 1: Observe and analyze the current state"""
        pass

    @abstractmethod
    def reason(self, observation: Observation) -> ReasoningResult:
        """Phase 2: Reason about the problem and plan actions"""
        pass

    @abstractmethod
    def act(self, observation: Observation, reasoning: ReasoningResult) -> ActionResult:
        """Phase 3: Execute the planned action"""
        pass

    def repair(
        self, code: str, error: VerusError, attempt: int, tree_search: bool = True
    ) -> tuple[bool, str, dict[str, Any]]:
        """Main repair method following the three-phase pattern"""
        self._attempt_id = attempt
        try:
            # Phase 1: Observation
            self.logger.info(f"[{self.__class__.__name__}] Phase 1: Observing...")
            observation = self.observe(code, error)
            self.logger.info("Observation:")
            self.logger.info(pprint.pformat(observation.to_dict(), indent=2, width=80))

            # Phase 2: Reasoning/Planning
            self.logger.info(f"[{self.__class__.__name__}] Phase 2: Reasoning...")
            reasoning = self.reason(observation)
            self.logger.info("Reasoning:")
            self.logger.info(pprint.pformat(reasoning.to_dict(), indent=2, width=80))

            # Create RepairAttemptMetadata for this attempt (store objects directly!)
            attempt_metadata = RepairAttemptMetadata(
                attempt_id=attempt,
                agent_name=self.__class__.__name__,
                error_type=error.error.name,
                observation=observation,  # Store object, not dict
                reasoning=reasoning,  # Store object, not dict
            )

            # Phase 3: Action
            self.logger.info(f"[{self.__class__.__name__}] Phase 3: Acting...")
            if self.swap_case_compute:
                # swap_case_compute overrides tree_search behavior
                self.logger.info("Using swap_case_compute mode (overrides tree_search)")

                # Special case: CASE_ANALYSIS primary and COMPUTE in secondary -> use COMPUTE
                if (
                    reasoning.primary_action == ActionType.CASE_ANALYSIS
                    and ActionType.COMPUTE in reasoning.secondary_actions
                ):
                    self.logger.info(
                        "Special case: CASE_ANALYSIS is primary and COMPUTE is secondary - using COMPUTE instead"
                    )
                    action_class_list = [action_registry.get_action_class(ActionType.COMPUTE)]
                    # Create new reasoning with swapped action
                    new_reasoning = reasoning.copy()
                    new_reasoning.primary_action = ActionType.COMPUTE
                    # FIXME: for now, just disable guidance
                    new_reasoning.action_parameters["guidance"] = ""
                else:
                    # Default: use primary action only
                    self.logger.info("Using primary action only")
                    action_class_list = [action_registry.get_action_class(reasoning.primary_action)]
                    # Keep original reasoning
                    new_reasoning = reasoning.copy()

                # Execute the single action (similar to tree_search loop but with just one action)
                action_class = action_class_list[0]
                action_result = self.act(observation, new_reasoning)
                # Apply the action result to the code
                self.logger.info("Applying action result to code...")
                accepted, best_candidate, evaluation_details = self.apply_action(
                    code,
                    error,
                    action_result,
                    observation,
                    new_reasoning,
                    attempt,
                    attempt_metadata,
                )

                self.logger.info("Finished applying the action")

                self.logger.debug(
                    f"Attempt {attempt}, Action {new_reasoning.primary_action} Accepted: {accepted}"
                )

                if accepted and best_candidate:
                    self.logger.info(
                        f"Attempt-{attempt}: Action {new_reasoning.primary_action} accepted, best candidate found"
                    )
                    # Store metadata before returning
                    self._store_attempt_metadata(
                        attempt_metadata, action_result, best_candidate, accepted
                    )

                    # Simplified return - full details available in metadata store
                    return (
                        True,
                        best_candidate,
                        {
                            "success_action": new_reasoning.primary_action.value,
                            "attempt_id": attempt,
                        },
                    )
                else:
                    self.logger.warning("Action not accepted or no best candidate found")

                    # Record failure in failure history when action is rejected
                    if self.failure_manager and not accepted:
                        error_context = f"{observation.error_type}:{observation.error_text[:100]}"

                        # Use the REAL evaluation reason, not the generic action explanation
                        evaluation_reason = (
                            evaluation_details.get("evaluation_reason", "").lower()
                            if evaluation_details
                            else ""
                        )

                        # Extract specific and readable failure reasons from the actual evaluation
                        if (
                            "verification timeout" in evaluation_reason
                            or "timeout" in evaluation_reason
                        ):
                            failure_reason = "verification_timeout"
                            detailed_failure_reason = (
                                "Verification process timed out (took too long to verify)"
                            )
                        elif (
                            "compilation error" in evaluation_reason
                            or "failed compilation" in evaluation_reason
                        ):
                            failure_reason = "compilation_error"
                            detailed_failure_reason = (
                                "Generated code has syntax errors and failed to compile"
                            )
                        elif "no error reduction" in evaluation_reason:
                            failure_reason = "no_error_reduction"
                            detailed_failure_reason = (
                                "Generated code changes did not reduce verification errors"
                            )
                        elif "fix the target error by 0" in evaluation_reason:
                            failure_reason = "target_error_not_fixed"
                            detailed_failure_reason = (
                                "Code changes did not fix the specific target error"
                            )
                        elif "bandaid assertion" in evaluation_reason:
                            failure_reason = "bandaid_assertions"
                            detailed_failure_reason = (
                                "Generated code contains bandaid assertions (not allowed)"
                            )
                        elif "safe check" in evaluation_reason:
                            failure_reason = "unsafe_changes"
                            detailed_failure_reason = "Generated code changes are not considered safe; they may alter original execution code or add `assume` or `unimplemented!`"
                        elif (
                            "error count increased" in evaluation_reason
                            or "more errors" in evaluation_reason
                        ):
                            failure_reason = "errors_increased"
                            detailed_failure_reason = (
                                "Code changes introduced new verification errors"
                            )
                        elif "without bandaid assertions" in evaluation_reason:
                            failure_reason = "target_error_not_fixed"
                            detailed_failure_reason = "Code changes did not fix the target error without adding bandaid assertions"
                        else:
                            failure_reason = "evaluation_rejected"
                            detailed_failure_reason = f"Action rejected: {evaluation_details.get('evaluation_reason', action_result.explanation) or 'no specific reason given'}"

                        # Generate detailed candidate information for failure history from metadata store
                        attempted_changes = ""
                        if attempt_metadata and attempt_metadata.candidates:
                            # Format all candidate details from CandidateMetadata objects
                            candidate_lines = []
                            for cand_meta in attempt_metadata.candidates:
                                candidate_lines.append(
                                    f"=== Candidate #{cand_meta.candidate_index + 1} ==="
                                )
                                candidate_lines.append(
                                    f"Result: {'accepted' if cand_meta.accepted else 'rejected'}"
                                )
                                candidate_lines.append(f"Reason: {cand_meta.reason}")
                                # Generate diff on-demand
                                code_changes = generate_simple_diff(
                                    observation.code, cand_meta.candidate_code
                                )
                                if code_changes and code_changes != "No changes":
                                    candidate_lines.append(f"Changes:\n{code_changes}")
                                candidate_lines.append("")  # Empty line between candidates
                            attempted_changes = "\n".join(candidate_lines)
                        elif (
                            action_result.modified_code
                            and action_result.modified_code != observation.code
                        ):
                            # Fallback to simple diff if no candidate metadata
                            attempted_changes = generate_simple_diff(
                                observation.code, action_result.modified_code
                            )

                        self.failure_manager.record_failure(
                            code=observation.code,
                            action_type=new_reasoning.primary_action.value,
                            failure_reason=failure_reason,
                            action_parameters=new_reasoning.action_parameters,
                            error_context=error_context,
                            attempted_changes=attempted_changes,
                            detailed_failure_reason=detailed_failure_reason,
                        )
                        self.logger.info(
                            f"Recorded failure for {new_reasoning.primary_action.value}: {failure_reason} - {detailed_failure_reason[:100]}"
                        )

                    # Store metadata before returning
                    self._store_attempt_metadata(attempt_metadata, action_result, None, accepted)

                    # Simplified return - full details available in metadata store
                    return (
                        False,
                        code,
                        {
                            "success_action": new_reasoning.primary_action.value,
                            "attempt_id": attempt,
                        },
                    )

            elif tree_search:
                self.logger.info("Using tree search for action selection")

                secondary_actions = [
                    action_registry.get_action_class(action_type)
                    for action_type in reasoning.secondary_actions
                ]
                filtered_actions = BaseAction.filter_action_based_on_criteria(secondary_actions)
                filtered_actions = filtered_actions[: min(2, len(filtered_actions))]

                # Get at most 2 filtered actions
                action_class_list = [
                    action_registry.get_action_class(reasoning.primary_action)
                ] + filtered_actions
                action_class_list = list(set(action_class_list))  # Remove duplicates

                if len(action_class_list) == 0:
                    raise ValueError("No valid action classes found for tree search")

                # FIXME: for now, just disable guidance
                reasoning.action_parameters["guidance"] = ""

                action_class_list = BaseAction.sort_action_based_on_criteria(action_class_list)

                self.logger.info(f"Sorted action classes based on criteria: { action_class_list}")

                for action_class in action_class_list:
                    new_reasoning = reasoning.copy()
                    new_reasoning.primary_action = action_registry.get_action_type(action_class)

                    action_result = self.act(observation, new_reasoning)
                    # Apply the action result to the code
                    self.logger.info("Applying action result to code...")
                    accepted, best_candidate, evaluation_details = self.apply_action(
                        code,
                        error,
                        action_result,
                        observation,
                        new_reasoning,
                        attempt,
                        attempt_metadata,
                    )

                    self.logger.debug(
                        f"Attempt {attempt}, Action {new_reasoning.primary_action} Accepted: {accepted}"
                    )

                    if accepted and best_candidate:
                        self.logger.info(
                            f"Attempt-{attempt}: Action {new_reasoning.primary_action} accepted, best candidate found"
                        )
                        # Store metadata before returning
                        self._store_attempt_metadata(
                            attempt_metadata, action_result, best_candidate, accepted
                        )

                        # Simplified return - full details available in metadata store
                        return (
                            True,
                            best_candidate,
                            {
                                "success_action": new_reasoning.primary_action.value,
                                "attempt_id": attempt,
                            },
                        )
                    else:
                        self.logger.warning("Action not accepted or no best candidate found")
                        # Log the action result for debugging
                        self.logger.info(
                            f"Attempt-{attempt}: Action {new_reasoning.primary_action} was not accepted, continuing to next action"
                        )

                self.logger.warning("Action not accepted or no best candidate found")
                # Store metadata before returning
                self._store_attempt_metadata(attempt_metadata, action_result, None, accepted)

                # Simplified return - full details available in metadata store
                return (
                    False,
                    code,
                    {
                        "success_action": new_reasoning.primary_action.value,
                        "attempt_id": attempt,
                    },
                )
            else:
                action_result = self.act(observation, reasoning)
                self.logger.info("Action result:")
                self.logger.info(pprint.pformat(action_result.to_dict(), indent=2, width=80))

                # Apply the action result to the code
                self.logger.info("Applying action result to code...")
                accepted, best_candidate, evaluation_details = self.apply_action(
                    code, error, action_result, observation, reasoning, attempt, attempt_metadata
                )
                if accepted and best_candidate:
                    self.logger.info("Action accepted, best candidate found")
                    # Store metadata before returning
                    self._store_attempt_metadata(
                        attempt_metadata, action_result, best_candidate, accepted
                    )

                    # Simplified return - full details available in metadata store
                    return (
                        True,
                        best_candidate,
                        {
                            "success_action": reasoning.primary_action.value,
                            "attempt_id": attempt,
                        },
                    )
                else:
                    self.logger.warning("Action not accepted or no best candidate found")
                    # Store metadata before returning
                    self._store_attempt_metadata(attempt_metadata, action_result, None, accepted)

                    # Simplified return - full details available in metadata store
                    return (
                        False,
                        code,
                        {
                            "success_action": reasoning.primary_action.value,
                            "attempt_id": attempt,
                        },
                    )

        except Exception as e:
            self.logger.error(f"Error during repair phases: {e}")
            return False, code, {"error": str(e), "attempt_id": attempt}

    def _validate_candidate(
        self,
        cand_code: str,
        code: str,
        error: VerusError,
        index: int,
        best_candidate: str | None,
    ) -> tuple[bool, str | None, str | None, EvalScore, str]:
        """
        Run all validation checks on a candidate.

        Returns:
            (is_valid, reason_category, reason_detail, score, validated_code)
            - is_valid: True if candidate passes all validation checks
            - reason_category: Short reason code (e.g., "compilation_error")
            - reason_detail: Human-readable detail message
            - score: EvalScore object for the candidate
            - validated_code: The code after any fixes (e.g., compilation repair)
        """
        score = self._get_score(cand_code)

        # Check 1: Timeout
        if score.timeout:
            return (
                False,
                "verification_timeout",
                "Verification process timed out (took too long to verify)",
                score,
                cand_code,
            )

        # Check 2: Identical code
        if cand_code == code:
            return (
                False,
                "identical_code",
                "Candidate code is identical to original code",
                score,
                cand_code,
            )

        # Check 3: Compilation (with auto-fix)
        if score.compilation_error:
            if best_candidate:
                # Skip fix if we already have a candidate
                return (
                    False,
                    "compilation_error",
                    f"Generated code has syntax errors and failed to compile: {score.compilation_error}",
                    score,
                    cand_code,
                )

            # Try to fix compilation errors
            self.logger.info(f"Attempting to fix compilation errors for candidate {index+1}")
            fixed_code = self._fix_compilation_errors_with_action(cand_code, error)
            fixed_code = verusfmt_code(fixed_code)
            score = self._get_score(fixed_code)

            if score.compilation_error:
                # Check if this is a known invalid syntax pattern
                from .verus_syntax_patterns import check_invalid_verus_syntax, get_syntax_hint

                pattern_error = check_invalid_verus_syntax(fixed_code)

                if pattern_error:
                    # Known pattern detected - provide enhanced error message with hint
                    hint = get_syntax_hint(fixed_code)
                    detailed_msg = f"Known invalid Verus syntax pattern detected: {pattern_error}"
                    if hint:
                        detailed_msg += f"\n💡 Hint: {hint}"

                    self.logger.warning(f"Candidate {index+1}: {detailed_msg}")
                    return (
                        False,
                        "syntax_pattern_error",
                        detailed_msg,
                        score,
                        fixed_code,
                    )
                else:
                    # Generic compilation error
                    return (
                        False,
                        "compilation_error",
                        f"Generated code still has syntax errors after repair attempt: {score.compilation_error}",
                        score,
                        fixed_code,
                    )

            # Success! Use the fixed code
            self.logger.info(
                f"Candidate {index+1} fixed compilation errors with syntax repair action"
            )
            cand_code = fixed_code

        # Check 4: Safety
        is_safe = proof_completion_code_change_is_safe(code, cand_code)
        if not is_safe:
            return (
                False,
                "unsafe_changes",
                "Generated code changes are not considered safe",
                score,
                cand_code,
            )

        # All checks passed!
        return True, None, None, score, cand_code

    def _record_rejected_candidate(
        self,
        attempt_metadata: "RepairAttemptMetadata",
        index: int,
        cand_code: str,
        code: str,
        score: EvalScore,
        reason_category: str,
        reason_detail: str,
        attempt: int,
        action_name: str,
        metadata: dict[str, Any],
    ) -> None:
        """Record a rejected candidate with consistent metadata"""
        # Add to metadata store
        cand_meta = CandidateMetadata(
            candidate_index=index,
            candidate_code=cand_code,
            original_code=code,
            accepted=False,
            reason=f"{reason_category}: {reason_detail}",
            score=score,
        )
        attempt_metadata.add_candidate(cand_meta)

        # Write to temp file for debugging
        self.write_candidate_with_reason(
            cand_code,
            attempt,
            action_name,
            index,
            score,
            f"REJECTED: {reason_detail}",
            metadata,
        )
        self.logger.warning(f"Candidate {index+1} rejected: {reason_category}")

    def _record_candidate_result(
        self,
        attempt_metadata: "RepairAttemptMetadata",
        index: int,
        cand_code: str,
        code: str,
        score: EvalScore,
        accepted: bool,
        reason: str,
        attempt: int,
        action_name: str,
        metadata: dict[str, Any],
    ) -> None:
        """Record a candidate result (accepted or rejected after evaluation)"""
        # Add to metadata store
        cand_meta = CandidateMetadata(
            candidate_index=index,
            candidate_code=cand_code,
            original_code=code,
            accepted=accepted,
            reason=reason,
            score=score,
        )
        attempt_metadata.add_candidate(cand_meta)

        # Write to temp file for debugging
        self.write_candidate_with_reason(
            cand_code,
            attempt,
            action_name,
            index,
            score,
            reason,
            metadata,
        )

        if accepted:
            self.logger.info(f"Candidate {index+1} accepted: {reason}")
        else:
            self.logger.warning(f"Candidate {index+1} rejected: {reason}")

    def apply_action(
        self,
        code: str,
        error: VerusError,
        action_result: ActionResult,
        observation: Observation,
        reasoning: ReasoningResult,
        attempt: int,
        attempt_metadata: "RepairAttemptMetadata",
    ) -> tuple[bool, str, dict[str, Any]]:
        """
        Apply the action result to the code and return the best candidate.

        Uses validation pipeline pattern for cleaner code flow:
        1. Validate candidate (timeout, identical, compilation, safety)
        2. Evaluate acceptance criteria
        3. Record results
        """

        has_accepted_result = False
        evaluation_details = None

        try:
            input_score = self._get_score(code)
            action_name = action_result.action_taken.value

            candidates = action_result.candidates
            self.logger.info(f"Generated {len(candidates)} repair candidates")

            best_score = None
            best_candidate = None

            metadata = {
                "observation": observation.to_dict(),
                "reasoning": reasoning.to_dict(),
                "action": action_result,
                "candidates_count": len(candidates),
                "has_multiple_candidates": len(candidates) > 1,
                "agent": self.__class__.__name__,
            }

            # Process each candidate through validation pipeline
            for i, cand_code in enumerate(candidates):
                cand_code = clean_code(cand_code)
                cand_code = verusfmt_code(cand_code)

                # ===== VALIDATION PHASE =====
                (
                    is_valid,
                    reason_cat,
                    reason_detail,
                    score,
                    validated_code,
                ) = self._validate_candidate(cand_code, code, error, i, best_candidate)

                if not is_valid:
                    # Record rejection and skip to next candidate
                    self._record_rejected_candidate(
                        attempt_metadata,
                        i,
                        validated_code,
                        code,
                        score,
                        reason_cat,
                        reason_detail,
                        attempt,
                        action_name,
                        metadata,
                    )
                    continue

                # Use validated code (may have been fixed during validation)
                cand_code = validated_code

                # ===== EVALUATION PHASE =====
                self.logger.info(f"Evaluating candidate {i+1}...")

                failed_errors_before = self._get_failures(code)
                failed_errors_after = self._get_failures(cand_code)

                evaluate_metadata = {
                    "observation": observation.to_dict(),
                    "reasoning": reasoning.to_dict(),
                    "failed_errors_before": failed_errors_before,
                    "failed_errors_after": failed_errors_after,
                    "candidates_count": len(candidates),
                    "has_multiple_candidates": len(candidates) > 1,
                }

                accepted, reason = self.evaluate_action_acceptance(
                    error_to_repair=error,
                    before_score=input_score,
                    after_score=score,
                    action_result=action_result,
                    metadata=evaluate_metadata,
                )

                # Update overall acceptance status
                has_accepted_result = has_accepted_result or accepted

                # Store evaluation details for failure recording
                evaluation_details = {
                    "evaluation_reason": reason,
                    "accepted": accepted,
                    "before_score": input_score,
                    "after_score": score,
                }

                # ===== RECORDING PHASE =====
                self._record_candidate_result(
                    attempt_metadata,
                    i,
                    cand_code,
                    code,
                    score,
                    accepted,
                    reason,
                    attempt,
                    action_name,
                    metadata,
                )

                # Update best candidate if this one is better
                if accepted and (best_score is None or score > best_score):
                    self.logger.info(f"Candidate {i+1} is the new best candidate")
                    best_score = score
                    best_candidate = cand_code
                    attempt_metadata.best_candidate_index = i

            # If no candidates passed validation, create evaluation details from metadata
            if not evaluation_details:
                if attempt_metadata.candidates:
                    failed_reasons = [
                        c.reason.split(":")[0]
                        for c in attempt_metadata.candidates
                        if not c.accepted
                    ]
                    evaluation_details = {
                        "evaluation_reason": (
                            "; ".join(failed_reasons)
                            if failed_reasons
                            else "All candidates failed validation"
                        ),
                        "accepted": False,
                    }
                else:
                    evaluation_details = {
                        "evaluation_reason": "No valid candidates generated",
                    }

            return has_accepted_result, best_candidate, evaluation_details

        except Exception as e:
            self.logger.error(f"Error applying action: {e}")
            self.logger.error(traceback.format_exc())
            return (
                False,
                None,
                {"evaluation_reason": f"Exception during evaluation: {str(e)}"},
            )

    def evaluate_action_acceptance(
        self,
        error_to_repair,
        before_score,
        after_score,
        action_result: ActionResult,
        metadata: dict = None,
    ) -> tuple[bool, str]:
        """Evaluate if an action should be accepted using action-specific criteria"""
        if self.accept_rule == "least":
            evaluator = AcceptanceEvaluator(criteria=AcceptanceCriteria.DONT_AFFECT_VERIFIED)
            self.logger.info("Using least acceptance strategy")
        elif self.accept_rule == "most":
            evaluator = AcceptanceEvaluator(criteria=AcceptanceCriteria.ERROR_REDUCTION)
            self.logger.info("Using most acceptance strategy")
        elif action_result.acceptance_evaluator:
            # Use action-specific evaluator
            evaluator = action_result.acceptance_evaluator
            self.logger.info(
                f"Using action-specific acceptance criteria: {evaluator.criteria.value}"
            )
        else:
            # Use default evaluator
            evaluator = AcceptanceEvaluator(criteria=AcceptanceCriteria.VERIFICATION_IMPROVEMENT)
            self.logger.info("Using default acceptance criteria: verification_improvement")

        accepted, reason = evaluator.evaluate(
            error_to_repair, before_score, after_score, action_result, metadata
        )

        self.logger.info(f"Action {action_result.action_taken.value} evaluation: {reason}")
        return accepted, reason

    def get_action_statistics(self) -> dict[str, Any]:
        """Get statistics about action history from global metadata store"""
        return GlobalConfig.get_metadata_store().get_statistics()

    def _store_attempt_metadata(
        self,
        attempt_metadata: RepairAttemptMetadata,
        action_result: ActionResult = None,
        best_candidate: str | None = None,
        accepted: bool = False,
    ):
        """
        Store attempt metadata in global store.

        Note: Candidates are now added incrementally in apply_action(),
        so this just stores the final metadata object.
        """
        # Store action_result reference in metadata for completeness
        if action_result:
            attempt_metadata.action_result = action_result

        # Store in global metadata store
        GlobalConfig.get_metadata_store().add_attempt(attempt_metadata)
        self.logger.info(f"Stored attempt {attempt_metadata.attempt_id} metadata in global store")

    def apply_preprocessing_analysis(self, code_analysis: CodeAnalysis):
        """Apply preprocessing analysis to this agent for action selection"""
        self.code_analysis = code_analysis
        self.logger.info(f"Applied preprocessing analysis to {self.__class__.__name__}")
        self.logger.info(f"  Lemmas: {code_analysis.lemmas}")
        self.logger.info(f"  Recursive functions: {code_analysis.recursive_functions}")
        self.logger.info(f"  Opaque functions: {code_analysis.opaque_functions}")

    def get_preprocessing_analysis(self) -> CodeAnalysis | None:
        """Get the current preprocessing analysis if available"""
        return self.code_analysis

    def filter_actions_with_preprocessing(
        self, available_actions: list[ActionType]
    ) -> list[ActionType]:
        """Filter available actions based on preprocessing analysis"""
        if not self.code_analysis:
            return available_actions

        filtered_actions = available_actions.copy()

        # Disable USELEMMA if no lemmas found
        if not self.code_analysis.has_lemmas():
            if ActionType.USELEMMA in filtered_actions:
                filtered_actions.remove(ActionType.USELEMMA)
                self.logger.info("USELEMMA action disabled: No lemmas found")

        # Disable REVEAL_OPAQUE if no opaque functions found
        if not self.code_analysis.has_opaque_functions():
            if ActionType.REVEAL_OPAQUE in filtered_actions:
                filtered_actions.remove(ActionType.REVEAL_OPAQUE)
                self.logger.info("REVEAL_OPAQUE action disabled: No opaque functions found")

        # Disable REVEAL_WITH_FUEL if no recursive functions found
        if not self.code_analysis.has_recursive_functions():
            if ActionType.REVEAL_WITH_FUEL in filtered_actions:
                filtered_actions.remove(ActionType.REVEAL_WITH_FUEL)
                self.logger.info("REVEAL_WITH_FUEL action disabled: No recursive functions found")

        return filtered_actions

    def boost_actions_with_preprocessing(self, action_list: list[ActionType]) -> list[ActionType]:
        """Boost priority of certain actions based on preprocessing analysis"""
        if not self.code_analysis or not self.code_analysis.has_recursive_functions():
            return action_list

        # Boost COMPUTE action if recursive functions are present
        if ActionType.COMPUTE in action_list:
            # Move COMPUTE to higher priority (near the top)
            action_list.remove(ActionType.COMPUTE)
            # Insert after the first few actions
            insert_position = min(3, len(action_list))
            action_list.insert(insert_position, ActionType.COMPUTE)
            self.logger.info(
                "Please consider more using COMPUTE action: Recursive functions detected"
            )

        return action_list

    def write_candidate_with_reason(
        self,
        candidate_code: str,
        attempt: int,
        action_name: str,
        index: int,
        score,
        reason: str,
        metadata: dict[str, Any] = None,
    ):
        rejection_info = f"\n\n// EVALUATION RESULT: {reason}" if reason else ""
        write_to_temp_dir(
            GlobalConfig.get_temp_dir(),
            f"fix-a{attempt}-{action_name}-candidate-{index+1}.rs",
            candidate_code + "\n\n//" + str(score).replace("\n", "\n//") + rejection_info,
            metadata=metadata,
        )

    def _fix_compilation_errors_with_action(self, code: str, error: VerusError) -> str:
        """Fix compilation errors using the syntax repair action"""
        try:
            from .actions import action_registry
            from .actions.action_types import ActionType
            from .shared_types import Observation

            # Create observation for the syntax repair action
            observation = Observation(
                code=code,
                error=error,
                error_location=(0, 0),  # Will be filled by the action
                error_text=error.get_text(),
                surrounding_context=code,
            )

            # Get the syntax repair action
            action_class = action_registry.get_action_class(ActionType.SYNTAX_REPAIR)
            action_instance = action_class()

            # Set failure manager if available
            if self.failure_manager:
                action_instance.set_failure_manager(self.failure_manager)

            # Execute the syntax repair action
            result = action_instance.execute(observation, {"max_attempts": 3})

            if result.success and result.modified_code:
                self.logger.info("Syntax repair action successfully fixed compilation errors")
                return result.modified_code
            else:
                self.logger.warning("Syntax repair action failed to fix compilation errors")
                return code

        except Exception as e:
            self.logger.error(f"Failed to use syntax repair action: {e}")
            return code

    _cache_veval = {}

    @staticmethod
    def _get_failures(code: str, error_type=None) -> list[VerusError]:
        """Get failures from the code using VEval"""
        if code in BaseAgent._cache_veval:
            v = BaseAgent._cache_veval[code]
        else:
            v = VEval(code)
            v.eval()
            BaseAgent._cache_veval[code] = v
        return v.get_failures(error_type)

    @staticmethod
    def _get_score(code: str) -> EvalScore:
        """Get the score of code using VEval"""
        if code in BaseAgent._cache_veval:
            v = BaseAgent._cache_veval[code]
        else:
            v = VEval(code)
            v.eval()
            BaseAgent._cache_veval[code] = v
        return v.get_score()
