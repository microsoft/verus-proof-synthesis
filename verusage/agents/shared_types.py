"""
Shared Types for Agent Framework
Contains common dataclasses and types used across the agent framework to avoid circular imports.
"""

import difflib
import hashlib
from collections.abc import Callable
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Any

from loguru import logger
from veval import EvalScore, VerusError, VerusErrorType


def generate_search_replace_diff(original_code: str, modified_code: str) -> str:
    """
    Generate SEARCH/REPLACE format from original and modified code.

    This creates a readable diff in the format:
    <<<<<<< SEARCH
    original lines
    =======
    modified lines
    >>>>>>> REPLACE

    Improvements:
    - Merges adjacent/overlapping blocks to reduce redundancy
    - Numbers blocks when there are multiple changes
    - Uses minimal context to keep output compact
    - Handles overlapping changes intelligently
    """
    if original_code == modified_code:
        return "No changes"

    original_lines = original_code.splitlines()
    modified_lines = modified_code.splitlines()

    # Use difflib to find the changed sections
    import difflib

    matcher = difflib.SequenceMatcher(None, original_lines, modified_lines)

    # Collect all change blocks with their ranges
    change_blocks = []

    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "replace" or tag == "delete" or tag == "insert":
            change_blocks.append((i1, i2, j1, j2))

    if not change_blocks:
        return "No significant changes"

    # Merge overlapping or adjacent blocks
    merged_blocks = []
    context_before = 2
    context_after = 2

    for i1, i2, j1, j2 in change_blocks:
        # Expand to include context
        search_start = max(0, i1 - context_before)
        search_end = min(len(original_lines), i2 + context_after)
        replace_start = max(0, j1 - context_before)
        replace_end = min(len(modified_lines), j2 + context_after)

        # Check if this block overlaps with the last merged block
        if merged_blocks:
            (
                last_search_start,
                last_search_end,
                last_replace_start,
                last_replace_end,
            ) = merged_blocks[-1]

            # Merge if blocks overlap or are very close (within 3 lines)
            if search_start <= last_search_end + 3 and replace_start <= last_replace_end + 3:
                merged_blocks[-1] = (
                    min(last_search_start, search_start),
                    max(last_search_end, search_end),
                    min(last_replace_start, replace_start),
                    max(last_replace_end, replace_end),
                )
                continue

        merged_blocks.append((search_start, search_end, replace_start, replace_end))

    # Generate output blocks
    search_replace_blocks = []

    for idx, (search_start, search_end, replace_start, replace_end) in enumerate(merged_blocks):
        search_lines = original_lines[search_start:search_end]
        replace_lines = modified_lines[replace_start:replace_end]

        if search_lines or replace_lines:
            # Add block number if there are multiple blocks
            if len(merged_blocks) > 1:
                block = f"<<<<<<< SEARCH (Block {idx + 1}/{len(merged_blocks)})\n"
            else:
                block = "<<<<<<< SEARCH\n"

            block += "\n".join(search_lines)
            if search_lines:
                block += "\n"
            block += "=======\n"
            block += "\n".join(replace_lines)
            if replace_lines:
                block += "\n"
            block += ">>>>>>> REPLACE"
            search_replace_blocks.append(block)

    if not search_replace_blocks:
        return "No significant changes"

    # Join blocks with clear visual separator
    if len(search_replace_blocks) > 1:
        return "\n\n" + "\n\n".join(search_replace_blocks)
    else:
        return search_replace_blocks[0]


def generate_unified_diff(
    original_code: str,
    modified_code: str,
    original_name: str = "original",
    modified_name: str = "modified",
) -> str:
    """Generate a unified diff patch between two code strings"""
    if original_code == modified_code:
        return "No changes"

    original_lines = original_code.splitlines(keepends=True)
    modified_lines = modified_code.splitlines(keepends=True)

    diff = difflib.unified_diff(
        original_lines,
        modified_lines,
        fromfile=original_name,
        tofile=modified_name,
        lineterm="",
    )

    return "".join(diff)


def generate_context_diff(
    original_code: str,
    modified_code: str,
    original_name: str = "original",
    modified_name: str = "modified",
) -> str:
    """Generate a context diff patch between two code strings"""
    if original_code == modified_code:
        return "No changes"

    original_lines = original_code.splitlines(keepends=True)
    modified_lines = modified_code.splitlines(keepends=True)

    diff = difflib.context_diff(
        original_lines,
        modified_lines,
        fromfile=original_name,
        tofile=modified_name,
        lineterm="",
    )

    return "".join(diff)


def generate_simple_diff(original_code: str, modified_code: str) -> str:
    """Generate a simple line-by-line diff showing changes"""
    if original_code == modified_code:
        return "No changes"

    original_lines = original_code.splitlines()
    modified_lines = modified_code.splitlines()

    diff_lines = []
    diff_lines.append("--- Changes ---")

    # Use ndiff for line-by-line comparison
    diff = list(difflib.ndiff(original_lines, modified_lines))

    # Filter out lines that are just whitespace differences
    significant_diff = []
    for line in diff:
        if line.startswith("- ") or line.startswith("+ "):
            significant_diff.append(line)
        elif line.startswith("  ") and len(significant_diff) > 0 and len(significant_diff) < 20:
            # Include some context lines, but not too many
            significant_diff.append(line)

    if not significant_diff:
        return "Only whitespace or formatting changes"

    # Limit output to avoid huge diffs
    if len(significant_diff) > 50:
        diff_lines.extend(significant_diff[:25])
        diff_lines.append("... (truncated, showing first 25 changes) ...")
        diff_lines.extend(significant_diff[-25:])
    else:
        diff_lines.extend(significant_diff)

    return "\n".join(diff_lines)


def generate_state_hash(code: str, error_context: str = "") -> str:
    """Generate a consistent hash for the current code state"""
    # Normalize code by removing extra whitespace and comments for more stable hashing
    normalized_code = "\n".join(line.strip() for line in code.splitlines() if line.strip())
    hash_input = f"{normalized_code}|{error_context}"
    return hashlib.md5(hash_input.encode("utf-8")).hexdigest()[:16]


@dataclass
class ActionFailureRecord:
    """Enhanced failure record with code changes and detailed failure reasons"""

    state_hash: str  # Hash of code state when action was attempted
    action_type: str  # ActionType.value (e.g., "add_proof_block")
    failure_reason: str  # "reject", "timeout", "verification_failed"
    action_parameters: dict[str, Any]  # The params passed to action
    timestamp: str  # When this failure occurred
    attempted_changes: str = ""  # The actual code changes that were tried (diff format)
    detailed_failure_reason: str = ""  # Detailed explanation of why it failed

    def __post_init__(self):
        if not self.timestamp:
            self.timestamp = datetime.now().isoformat()


@dataclass
class CandidateDiff:
    """Represents the diff information for a candidate solution"""

    candidate_index: int
    unified_diff: str
    simple_diff: str
    search_replace_format: str = ""  # SEARCH/REPLACE format for readability
    stats: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self):
        """Calculate basic diff statistics"""

    def get_summary(self) -> str:
        # To be deleted
        return ""


PRIORITY_ORDER = {
    "complete_fix": 0,
    "error_reduction": 1,
    "verification_improvement": 2,
    "no_bandaid_asserts": 3,
    "dont_affect_verified_no_error_increase": 4,
    "dont_affect_verified_exloop": 5,
    "dont_affect_verified": 6,
    "fix_precondition": 7,
}


class AcceptanceCriteria(Enum):
    """Different types of acceptance criteria for actions"""

    COMPLETE_FIX = "complete_fix"  # Must completely fix all errors
    ERROR_REDUCTION = "error_reduction"  # Must reduce error count
    VERIFICATION_IMPROVEMENT = "verification_improvement"  # Standard: fix the target error
    NO_BANDAID_ASSERTS = "no_bandaid_asserts"  # Reject candidates that add assertions without fixing original failures
    FIX_PRECONDITION = "fix_precondition"  # Specifically fix precondition failures
    DONT_AFFECT_VERIFIED_NO_ERROR_INCREASE = "dont_affect_verified_no_error_increase"  # Must not affect verified count AND number of errors must not increase
    DONT_AFFECT_VERIFIED_EXLOOP = "dont_affect_verified_exloop"  # The verified count can go up by up to 1 due to loop invariant additions
    DONT_AFFECT_VERIFIED = "dont_affect_verified"  # Must not affect the verified count

    def __gt__(self, other: "AcceptanceCriteria") -> bool:
        return PRIORITY_ORDER[self.value] < PRIORITY_ORDER[other.value]

    def __lt__(self, other: "AcceptanceCriteria") -> bool:
        return PRIORITY_ORDER[self.value] > PRIORITY_ORDER[other.value]


def map_assertion_failure_to_lynette_range(
    assertion_error: VerusError, temp_file_path: str
) -> tuple[int, int] | None:
    """
    Map an assertion failure to exactly one assertion range from Lynette.

    Args:
        assertion_error: The VerusError representing an assertion failure
        temp_file_path: Path to the temporary file for Lynette analysis

    Returns:
        Optional[Tuple[int, int]]: (start_line, end_line) of the matched assertion range, or None if no match
    """
    try:
        from lynette import lynette

        # Get all assertions from the file using Lynette
        all_assertions = lynette.get_assertions(temp_file_path)
        if not all_assertions:
            return None

        # For each trace in the assertion error, find the best matching assertion range
        for trace in assertion_error.trace:
            trace_start, trace_end = trace.lines

            # Find the assertion range that exactly contains or matches this trace
            best_match = None
            best_overlap = 0

            for assertion in all_assertions:
                assertion_start = assertion["start_line"]
                assertion_end = assertion["end_line"]

                # Calculate overlap between trace and assertion ranges
                overlap_start = max(trace_start, assertion_start)
                overlap_end = min(trace_end, assertion_end)
                overlap = max(0, overlap_end - overlap_start + 1)

                # Prefer exact matches, then best overlap
                if (
                    assertion_start <= trace_start <= assertion_end
                    and assertion_start <= trace_end <= assertion_end
                ):
                    # Exact containment - this is the best match
                    return (assertion_start, assertion_end)
                elif overlap > best_overlap:
                    best_overlap = overlap
                    best_match = (assertion_start, assertion_end)

            # Return the best match found for this trace
            if best_match:
                return best_match

        return None

    except Exception as e:
        logger.warning(f"Failed to map assertion failure to Lynette range: {e}")
        return None


def detect_new_assertion_in_proof_block(
    failed_errors_before: list[VerusError],
    failed_errors_after: list[VerusError],
    target_assertion: VerusError = None,
    metadata: dict = None,
) -> tuple[bool, str]:
    """
    Detect if inner assertions were added for a target assertion being fixed.

    Accept Criteria:
    1. The target "outer" assertion (being fixed) disappears from error list
    2. Any newly introduced failed assertions are ONLY inside the target assertion body

    Args:
        failed_errors_before: List of failed assertion errors before repair
        failed_errors_after: List of failed assertion errors after repair
        target_assertion: The specific assertion being targeted for repair (optional)
        metadata: Dict containing 'candidate_code' with the patched code content

    Returns:
        Tuple[bool, str]: (should_reject, reason)
        - should_reject: False if accept criteria met (target fixed, new failures only inside target)
                        True if reject criteria met (target not fixed or new failures outside target)
        - reason: Explanation with "ACCEPT:" or "REJECT:" prefix
    """
    try:
        if not failed_errors_before or not failed_errors_after:
            return False, "No failed assertions to compare"

        # If target_assertion is not provided, try to infer it
        # (assume it's the first error in failed_errors_before for now)
        if target_assertion is None:
            if failed_errors_before:
                target_assertion = failed_errors_before[0]
                logger.warning(
                    "🎯 TARGET ASSERT: Inferred from first error in failed_errors_before"
                )
            else:
                return False, "No target assertion to analyze"
        else:
            logger.debug("🎯 TARGET ASSERT: Explicitly provided")

        # Debug: Show target assertion details
        target_lines = "unknown"
        if (
            hasattr(target_assertion, "assertion_locations")
            and target_assertion.assertion_locations
        ):
            target_lines = f"{target_assertion.assertion_locations[0]['start_line']}-{target_assertion.assertion_locations[0]['end_line']}"
        elif hasattr(target_assertion, "trace") and target_assertion.trace:
            target_lines = f"{target_assertion.trace[0].lines}"

        logger.debug("🎯 TARGET ASSERT DETAILS:")
        logger.debug(f"   Text: {target_assertion.error_text}")
        logger.debug(f"   Lines: {target_lines}")
        logger.debug(f"   Total errors before: {len(failed_errors_before)}")
        logger.debug(f"   Total errors after: {len(failed_errors_after)}")

        # Check if target assertion disappeared (Accept Criteria #1)
        target_still_failing = False
        for error_after in failed_errors_after:
            if target_assertion.similar(error_after):
                target_still_failing = True
                logger.debug("🔍 TARGET STILL PRESENT: Found similar error in after list")
                logger.debug(f"   After error text: {error_after.error_text}")
                break

        if not target_still_failing:
            logger.debug("✅ TARGET DISAPPEARED: Not found in after list - successfully repaired!")

        if target_still_failing:
            logger.debug("❌ TARGET STILL FAILING: Target assertion was not successfully repaired")
            return (
                True,
                "REJECT: Target assertion still failing - not successfully repaired",
            )

        # Find new assertion failures (present in after but not in before)
        new_failures = []
        for error_after in failed_errors_after:
            found_similar = False
            for error_before in failed_errors_before:
                if error_before.similar(error_after):
                    found_similar = True
                    break
            if not found_similar:
                new_failures.append(error_after)

        logger.debug("🔍 NEW FAILURES ANALYSIS:")
        logger.debug(f"   Found {len(new_failures)} new assertion failures")
        for i, new_err in enumerate(new_failures):
            new_lines = "unknown"
            if hasattr(new_err, "assertion_locations") and new_err.assertion_locations:
                new_lines = f"{new_err.assertion_locations[0]['start_line']}-{new_err.assertion_locations[0]['end_line']}"
            elif hasattr(new_err, "trace") and new_err.trace:
                new_lines = f"{new_err.trace[0].lines}"
            logger.debug(f"   New failure {i+1}: {new_err.error_text} at lines {new_lines}")

        if not new_failures:
            logger.debug("✅ ACCEPT: Target assertion fixed with no new failures")
            return False, "ACCEPT: Target assertion fixed with no new failures"

        # Check Accept Criteria #2: All new failures must be ONLY inside target assertion body
        # IMPORTANT: We need to find the target assertion range in the AFTER file
        # Use Lynette to get all assertions from the after file and find the target using is_similar_text

        target_range = None

        logger.debug("🎯 FINDING TARGET ASSERTION IN AFTER FILE:")
        logger.debug(f"   Target error text: '{target_assertion.error_text}'")
        logger.debug(
            f"   Target trace text: '{target_assertion.get_trace_text() if hasattr(target_assertion, 'get_trace_text') else 'N/A'}'"
        )

        # Get candidate_code from metadata
        target_range = None
        if not metadata or "candidate_code" not in metadata:
            logger.debug("❌ No candidate_code available in metadata")
        else:
            candidate_code = metadata["candidate_code"]
            logger.debug(
                f"🔍 Using candidate_code from metadata (length: {len(candidate_code)} chars)"
            )

            try:
                # Write candidate_code to a temporary file for Lynette analysis
                import os
                import tempfile

                with tempfile.NamedTemporaryFile(mode="w", suffix=".rs", delete=False) as temp_f:
                    temp_f.write(candidate_code)
                    temp_candidate_path = temp_f.name

                logger.debug(
                    f"📝 Created temporary file for Lynette analysis: {temp_candidate_path}"
                )

                # Import Lynette functions to get all assertions from candidate code
                from lynette import lynette

                # Get all assertions from the candidate code
                all_assertions = lynette.get_assertions(temp_candidate_path)
                logger.debug(f"   Found {len(all_assertions)} total assertions in candidate code")

                # Find the target assertion using is_similar_text
                target_found = False
                candidate_lines = candidate_code.split("\n")

                for assertion in all_assertions:
                    # Each assertion should have location info
                    if "start_line" in assertion and "end_line" in assertion:
                        assertion_range = (
                            assertion["start_line"],
                            assertion["end_line"],
                        )

                        # Extract assertion text from candidate_code lines
                        start_idx = max(0, assertion["start_line"] - 1)
                        end_idx = min(len(candidate_lines), assertion["end_line"])
                        assertion_text = "\n".join(candidate_lines[start_idx:end_idx]).strip()

                        logger.debug(
                            f"   Checking assertion at {assertion_range}: '{assertion_text[:50]}...'"
                        )

                        # Use is_similar_text to check if this is our target assertion
                        target_trace_text = (
                            target_assertion.get_trace_text()
                            if hasattr(target_assertion, "get_trace_text")
                            else target_assertion.error_text
                        )

                        if target_assertion.is_similar_text(target_trace_text, assertion_text):
                            target_range = assertion_range
                            target_found = True
                            logger.debug(
                                f"🎯 TARGET FOUND in candidate code at range: {target_range}"
                            )
                            logger.debug(f"   Matched assertion text: '{assertion_text[:100]}...'")
                            break

                # Clean up temporary file
                os.unlink(temp_candidate_path)

                if not target_found:
                    logger.warning("⚠️  TARGET NOT FOUND in candidate code assertions")
            except Exception as e:
                logger.debug(f"❌ Error using Lynette to analyze candidate code: {e}")
                logger.debug("   Will fall back to using original assertion location")
                import traceback

                logger.debug(f"   Traceback: {traceback.format_exc()}")

        # Fallback: Use original assertion location if Lynette approach fails
        if not target_range:
            logger.warning("Failed to find target assertion in candidate code")

            return (
                False,
                "ACCEPT?: Target assertion fixed and failed to find target assertion in candidate code",
            )
            logger.warning("🔄 FALLBACK: Using target assertion location from before file")
            if (
                hasattr(target_assertion, "assertion_locations")
                and target_assertion.assertion_locations
            ):
                first_assertion = target_assertion.assertion_locations[0]
                target_range = (
                    first_assertion["start_line"],
                    first_assertion["end_line"],
                )
                logger.debug(
                    f"🎯 TARGET RANGE (fallback): Using assertion_locations: {target_range}"
                )
            elif hasattr(target_assertion, "trace") and target_assertion.trace:
                target_range = target_assertion.trace[0].lines
                logger.debug(f"🎯 TARGET RANGE (fallback): Using trace lines: {target_range}")
            else:
                logger.debug("❌ No target range available - cannot perform containment check")

        new_failures_inside_target = []
        new_failures_outside_target = []

        logger.debug("🔍 CONTAINMENT ANALYSIS:")
        logger.debug(f"   Target range: {target_range}")
        logger.debug(f"   Checking {len(new_failures)} new failures for containment")

        for i, new_failure in enumerate(new_failures):
            new_range = None
            if hasattr(new_failure, "assertion_locations") and new_failure.assertion_locations:
                first_assertion = new_failure.assertion_locations[0]
                new_range = (first_assertion["start_line"], first_assertion["end_line"])

            logger.debug(f"   New failure {i+1}: {new_failure.error_text}")
            logger.debug(f"      New failure range: {new_range}")

            # Check if new failure is inside target assertion body
            if target_range and new_range:
                target_start, target_end = target_range
                new_start, new_end = new_range

                # Check containment
                is_contained = (
                    target_start <= new_start <= target_end
                    and target_start <= new_end <= target_end
                )

                if is_contained:
                    new_failures_inside_target.append((new_failure, new_range))
                    logger.debug(f"      ✅ INSIDE target: {new_range} is within {target_range}")
                else:
                    new_failures_outside_target.append((new_failure, new_range))
                    logger.debug(
                        f"      ❌ OUTSIDE target: {new_range} is NOT within {target_range}"
                    )
            else:
                # If we can't determine ranges, assume outside target for safety
                new_failures_outside_target.append((new_failure, None))
                logger.debug("      ❌ UNKNOWN range: Assuming OUTSIDE target for safety")

        # REJECT if any new failures are outside target assertion body
        if new_failures_outside_target:
            details = []
            for new_f, new_range in new_failures_outside_target[:3]:
                if new_range:
                    details.append(f"new_failure@{new_range} outside target@{target_range}")
                else:
                    new_lines = (
                        [trace.lines for trace in new_f.trace]
                        if hasattr(new_f, "trace")
                        else "unknown"
                    )
                    details.append(f"new_failure@{new_lines} outside target (range unknown)")

            detail_str = "; ".join(details)
            if len(new_failures_outside_target) > 3:
                detail_str += "..."

            return (
                True,
                f"REJECT: Found {len(new_failures_outside_target)} new failure(s) outside target assertion body: {detail_str}",
            )

        # ACCEPT if all new failures are inside target assertion body
        if new_failures_inside_target:
            details = []
            for _new_f, new_range in new_failures_inside_target[:3]:
                details.append(f"new_failure@{new_range} inside target@{target_range}")

            detail_str = "; ".join(details)
            if len(new_failures_inside_target) > 3:
                detail_str += "..."

            return (
                False,
                f"ACCEPT: Target assertion fixed, {len(new_failures_inside_target)} new failure(s) only inside target body: {detail_str}",
            )

        # Should not reach here, but fallback to ACCEPT
        return (
            False,
            "ACCEPT: Target assertion fixed, containment analysis inconclusive",
        )

    except Exception as e:
        logger.warning(f"Error in proof block bandaid detection: {e}")
        return False, f"Detection failed: {e}"


@dataclass
class AcceptanceEvaluator:
    """Evaluates whether an action should be accepted based on specific criteria"""

    criteria: AcceptanceCriteria
    threshold: float = 0.0  # Additional threshold parameter
    custom_evaluator: Callable | None = None  # Custom evaluation function

    def evaluate(
        self,
        error_to_repair: VerusError,
        before_score: EvalScore,
        after_score: EvalScore,
        action_result: "ActionResult",
        metadata: dict = None,
    ) -> tuple[bool, str]:
        """Evaluate if action should be accepted"""
        logger.warning(f"Evaluating acceptance criteria: {self.criteria}")

        logger.debug(f"Evaluate for {error_to_repair.error}")
        last_target_error_count = before_score.error_type_count.get(error_to_repair.error, 0)
        current_target_error_count = after_score.error_type_count.get(error_to_repair.error, 0)
        logger.debug(
            f"Target error count before: {last_target_error_count}, after: {current_target_error_count}"
        )

        reduce_target_error_count = last_target_error_count - current_target_error_count

        if self.custom_evaluator:
            return self.custom_evaluator(before_score, after_score, action_result, metadata)

        if self.criteria == AcceptanceCriteria.DONT_AFFECT_VERIFIED:
            accepted = after_score.is_good_repair(before_score)
            reason = "Dont affect verified" if accepted else "Affect verified"
            logger.debug(f"Dont affect verified evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.DONT_AFFECT_VERIFIED_EXLOOP:
            verified_change = before_score.verified - after_score.verified
            accepted = after_score.compilation_error == 0 and verified_change <= 1
            reason = "Didn't affect verified much" if accepted else "Affect verified too much"
            logger.debug(f"Dont affect verified exloop evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.COMPLETE_FIX:
            accepted = after_score.is_correct()
            reason = "Completely fixed all errors" if accepted else "Did not fix all errors"
            logger.debug(f"Complete fix evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.ERROR_REDUCTION:
            error_reduction = before_score.verus_errors - after_score.verus_errors
            accepted = error_reduction > 0 and after_score.is_good_repair(before_score)
            reason = f"Reduced errors by {error_reduction}" if accepted else "No error reduction"
            logger.debug(f"Error reduction evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.DONT_AFFECT_VERIFIED_NO_ERROR_INCREASE:
            # Check both: verified count not affected AND error count does not increase
            verified_ok = after_score.is_good_repair(before_score)
            error_increase = after_score.verus_errors - before_score.verus_errors
            accepted = verified_ok and error_increase <= 0

            if not verified_ok:
                reason = "Affected verified count"
            elif error_increase > 0:
                reason = f"Error count increased by {error_increase}"
            else:
                reason = "Verified count not affected and errors did not increase"

            logger.debug(f"Dont affect verified + no error increase evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.NO_BANDAID_ASSERTS:
            # First check basic improvement
            if not after_score.is_good_repair(before_score):
                accepted = False
                reason = "No verification improvement"
                logger.debug(f"No bandaid asserts evaluation: {reason}")
            else:
                # Get failed assertion errors from metadata
                failed_errors_before = metadata.get("failed_errors_before", []) if metadata else []
                failed_errors_after = metadata.get("failed_errors_after", []) if metadata else []

                # If metadata doesn't contain failed errors, we can't perform bandaid detection
                if not failed_errors_before and not failed_errors_after:
                    logger.warning(
                        "No failed error details available for bandaid detection - accepting by default"
                    )
                    accepted = True
                    reason = f"Fix the target error by {reduce_target_error_count} (bandaid detection skipped)"
                    logger.debug(f"No bandaid asserts evaluation: {reason}")
                else:
                    # Perform bandaid detection using Lynette-enriched error information
                    is_bandaid, bandaid_reason = detect_new_assertion_in_proof_block(
                        failed_errors_before,
                        failed_errors_after,
                        target_assertion=error_to_repair,
                        metadata=metadata,
                    )

                    if is_bandaid:
                        accepted = False
                        reason = f"Bandaid fix detected: {bandaid_reason}"
                        logger.debug(f"No bandaid asserts evaluation: {reason}")
                    else:
                        accepted = True
                        reason = f"Fix the target error by {reduce_target_error_count} without bandaid assertions"
                        logger.debug(f"No bandaid asserts evaluation: {reason}")

        elif self.criteria == AcceptanceCriteria.FIX_PRECONDITION:
            accepted = after_score.is_good_repair(before_score) and reduce_target_error_count > 0
            if accepted:
                reason = f"Fix the precondition error by {reduce_target_error_count}"
            else:
                before_precond_text = before_score.error_type_text.get(
                    VerusErrorType.PreCondFail, "N/A"
                )
                after_precond_text = after_score.error_type_text.get(
                    VerusErrorType.PreCondFail, "N/A"
                )
                logger.debug(
                    f"Precondition texts - before: '{before_precond_text}', after: '{after_precond_text}'"
                )

                if before_precond_text != after_precond_text:
                    accepted = True
                    reason = "Precondition error text changed, indicating a fix attempt"

        else:  # VERIFICATION_IMPROVEMENT (default)
            accepted = after_score.is_good_repair(before_score) and reduce_target_error_count > 0
            reason = (
                f"Fix the target error by {reduce_target_error_count}"
                if accepted
                else "No verification improvement"
            )
            logger.debug(f"Verification improvement evaluation: {reason}")

        return accepted, reason


@dataclass
class Observation:
    """Structured observation of the current code state and error"""

    code: str
    error: Any  # VerusError
    error_location: tuple[int, int]  # (start_line, end_line)
    error_text: str
    surrounding_context: str
    error_type: str = ""
    additional_context: dict[str, Any] = field(default_factory=dict)
    failure_history: list[ActionFailureRecord] = field(
        default_factory=list
    )  # Previous failures for this state

    def __post_init__(self):
        """Set error type from error object"""
        if hasattr(self.error, "error") and hasattr(self.error.error, "name"):
            self.error_type = self.error.error.name

    def to_dict(self) -> dict[str, Any]:
        """Convert observation to dictionary for logging/debugging"""
        return {
            "error_type": self.error_type,
            "error_location": self.error_location,
            "error_text": self.error_text,
            "additional_context": self.additional_context,
        }


@dataclass
class ActionResult:
    """Result of an action execution"""

    action_taken: Any  # ActionType
    explanation: str
    candidates: list[str] = field(default_factory=list)  # Multiple candidate solutions
    action_parameters: dict[str, Any] = field(
        default_factory=dict
    )  # Store the LLM-provided parameters
    acceptance_evaluator: AcceptanceEvaluator | None = None  # Action-specific acceptance criteria
    candidate_diffs: list[CandidateDiff] = None  # Diff information for each candidate
    original_code: str = ""  # Store original code for diff generation

    # REMOVED FIELDS (now computed properties):
    # - success: bool (computed from len(candidates) > 0)
    # - modified_code: str (alias for candidates[0])
    # - accepted: bool (determined during evaluation, not generation)

    def __post_init__(self):
        """Initialize candidates list and generate diffs if not provided"""
        # Generate diff information for candidates if not provided
        if self.candidate_diffs is None and self.original_code and self.candidates:
            self.candidate_diffs = self._generate_candidate_diffs()

    def _generate_candidate_diffs(self) -> list[CandidateDiff]:
        """Generate diff information for all candidates"""
        diffs = []
        for i, candidate in enumerate(self.candidates):
            unified_diff = generate_unified_diff(
                self.original_code, candidate, "original", f"candidate_{i+1}"
            )
            simple_diff = generate_simple_diff(self.original_code, candidate)
            search_replace_format = generate_search_replace_diff(self.original_code, candidate)

            candidate_diff = CandidateDiff(
                candidate_index=i + 1,
                unified_diff=unified_diff,
                simple_diff=simple_diff,
                search_replace_format=search_replace_format,
            )
            diffs.append(candidate_diff)

        return diffs

    def set_original_code(self, original_code: str):
        """Set the original code and regenerate diffs"""
        self.original_code = original_code
        if self.candidates:
            self.candidate_diffs = self._generate_candidate_diffs()

    # Properties for backward compatibility (replacing removed fields)
    @property
    def success(self) -> bool:
        """Whether action successfully generated candidates"""
        return len(self.candidates) > 0

    @property
    def modified_code(self) -> str:
        """Get the best (first) candidate - alias for backward compatibility"""
        return self.candidates[0] if self.candidates else ""

    @property
    def accepted(self) -> bool:
        """Accepted status - always False here (determined during evaluation)"""
        # Note: This is just for backward compatibility during transition
        # Acceptance is determined in apply_action, not in ActionResult
        return False

    def get_best_candidate(self) -> str:
        """Get the best (first) candidate"""
        return self.candidates[0] if self.candidates else ""

    def get_all_candidates(self) -> list[str]:
        """Get all candidates"""
        return self.candidates

    def get_candidate_diff(self, candidate_index: int) -> CandidateDiff | None:
        """Get diff information for a specific candidate (1-indexed)"""
        if self.candidate_diffs and 0 < candidate_index <= len(self.candidate_diffs):
            return self.candidate_diffs[candidate_index - 1]
        return None

    def get_diff_summary(self) -> str:
        """Get a summary of all candidate diffs"""
        if not self.candidate_diffs:
            return "No diff information available"

        summaries = []
        for diff in self.candidate_diffs:
            summaries.append(f"C{diff.candidate_index}: {diff.get_summary()}")

        return " | ".join(summaries)

    def to_dict(self) -> dict[str, Any]:
        """Convert action result to dictionary for logging"""
        result = {
            "success": self.success,
            "accepted": self.accepted,
            "action": self.action_taken.value,  # action_taken is always ActionType enum
            "explanation": self.explanation,
            "diff_summary": self.get_diff_summary(),
        }

        # Include acceptance criteria info if available
        if self.acceptance_evaluator:
            result["acceptance_criteria"] = self.acceptance_evaluator.criteria.value

        # Include detailed diff information if available
        if self.candidate_diffs:
            result["candidate_diffs"] = []
            for diff in self.candidate_diffs:
                result["candidate_diffs"].append(
                    {
                        "candidate_index": diff.candidate_index,
                        "summary": diff.get_summary(),
                        "stats": diff.stats,
                        "simple_diff": (
                            diff.simple_diff[:500] + "..."
                            if len(diff.simple_diff) > 500
                            else diff.simple_diff
                        ),
                    }
                )

        return result

    def get_parameter_summary(self) -> str:
        """Get a readable summary of the action parameters"""
        if not self.action_parameters:
            return "No parameters"

        summary_parts = []
        for key, value in self.action_parameters.items():
            if isinstance(value, list) and value:
                summary_parts.append(f"{key}: {', '.join(map(str, value))}")
            elif value:
                summary_parts.append(f"{key}: {value}")

        return "; ".join(summary_parts) if summary_parts else "No parameters"


@dataclass
class ReasoningResult:
    """Result of the reasoning/planning phase"""

    primary_action: Any  # ActionType
    secondary_actions: list[Any]  # List[ActionType]
    reasoning_explanation: str
    action_parameters: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        """Convert reasoning result to dictionary for logging"""
        return {
            "primary_action": self.primary_action.value,  # primary_action is always ActionType enum
            "secondary_actions": [
                a.value for a in self.secondary_actions  # All actions are ActionType enums
            ],
            "reasoning": self.reasoning_explanation,
            "parameters": self.action_parameters,
        }

    def copy(self) -> "ReasoningResult":
        """Create a copy of this reasoning result"""
        return ReasoningResult(
            primary_action=self.primary_action,
            secondary_actions=self.secondary_actions.copy(),
            reasoning_explanation=self.reasoning_explanation,
            action_parameters=self.action_parameters.copy(),
        )


def write_to_temp_dir(
    temp_dir,
    file_name,
    content,
    error_trace=None,
    score=None,
    is_safe=None,
    metadata=None,
    agent_info=None,
    reasoning_trace=None,
    prompt_output=None,
):
    """Helper function to write content to a file in the temp directory"""
    if not temp_dir:
        return

    file_path = temp_dir / file_name

    # Start with the content
    output = ""

    # Add comprehensive metadata if provided
    if metadata:
        output += "\n\n// ===== AGENT METADATA =====\n"
        output += "// Agent Framework Information:\n"

        # Agent information
        if agent_info:
            output += f"// Agent: {agent_info.get('agent', 'Unknown')}\n"
            output += f"// Error Type: {agent_info.get('error_type', 'Unknown')}\n"
            output += f"// Attempt: {agent_info.get('attempt', 'Unknown')}\n"

        # Observation details
        if "observation" in metadata:
            obs = metadata["observation"]
            output += "// \n// OBSERVATION PHASE:\n"
            output += f"// Error Location: {obs.get('error_location', 'Unknown')}\n"
            output += f"// Error Type: {obs.get('error_type', 'Unknown')}\n"
            error_text = obs.get("error_text", "Unknown")
            error_text = error_text.replace("\n", "\n//")
            if len(error_text) < 200:
                output += f"// Error Text: {error_text}\n"
            else:
                output += f"// Error Text: {error_text[:200]}...\n"

        # Reasoning details
        if "reasoning" in metadata:
            reasoning = metadata["reasoning"]
            output += "// \n// REASONING PHASE:\n"
            output += f"// Primary Action: {reasoning.get('primary_action', 'Unknown')}\n"
            output += f"// Secondary Actions: {reasoning.get('secondary_actions', [])}\n"
            output += f"// Reasoning: {reasoning.get('reasoning', 'Unknown')}\n"
            if "parameters" in reasoning:
                output += "// Parameters:\n"
                for key, value in reasoning["parameters"].items():
                    output += f"//   {key}: {value}\n"

        # Action details
        if "action" in metadata:
            action = metadata["action"]
            # ActionResult always has to_dict() method
            action_dict = action.to_dict()
            output += "// \n// ACTION PHASE:\n"
            output += f"// Action Type: {action_dict.get('action', 'Unknown')}\n"
            output += f"// Success: {action_dict.get('success', 'Unknown')}\n"
            output += f"// Accepted: {action_dict.get('accepted', 'Unknown')}\n"
            output += f"// Explanation: {action_dict.get('explanation', 'Unknown')}\n"

            # Action parameters (ActionResult always has action_parameters field)
            if action.action_parameters:
                output += "// Action Parameters:\n"
                for key, value in action.action_parameters.items():
                    output += f"//   {key}: {value}\n"

            # Candidates information (ActionResult always has candidates field)
            candidates = action.candidates
            output += "// \n// CANDIDATES:\n"
            output += f"// Total Candidates: {len(candidates)}\n"
            output += (
                f"// Has Multiple Candidates: {metadata.get('has_multiple_candidates', False)}\n"
            )

        # Agent-specific information
        if "agent" in metadata:
            output += f"// Agent Class: {metadata['agent']}\n"

        # Error comparison for NO_BANDAID_ASSERTS criteria
        if "failed_errors_before" in metadata:
            output += "// \n// ERROR COMPARISON:\n"
            failed_errors_before = metadata["failed_errors_before"]
            output += f"// Failed Errors Before: {len(failed_errors_before)}\n"
            for i, error in enumerate(failed_errors_before[:3]):  # Show first 3 errors
                error_type = error.error.name if hasattr(error.error, "name") else str(error.error)
                error_text = error.get_text().replace("\n", "\n//")
                output += f"//   {i+1}: {error_type} - {error_text[:100]}...\n"
            if len(failed_errors_before) > 3:
                output += f"//   ... and {len(failed_errors_before) - 3} more errors\n"

        if "failed_errors_after" in metadata:
            failed_errors_after = metadata["failed_errors_after"]
            output += f"// Failed Errors After: {len(failed_errors_after)}\n"
            for i, error in enumerate(failed_errors_after[:3]):  # Show first 3 errors
                error_type = error.error.name if hasattr(error.error, "name") else str(error.error)
                error_text = error.get_text()
                output += f"//   {i+1}: {error_type} - {error_text[:100]}...\n"
            if len(failed_errors_after) > 3:
                output += f"//   ... and {len(failed_errors_after) - 3} more errors\n"

    # Add reasoning trace if provided
    if reasoning_trace:
        output += "\n\n// ===== REASONING TRACE =====\n"
        if isinstance(reasoning_trace, dict):
            for phase, details in reasoning_trace.items():
                output += f"// \n// {phase.upper()}:\n"
                if isinstance(details, dict):
                    for key, value in details.items():
                        output += f"//   {key}: {value}\n"
                else:
                    details_lines = str(details).splitlines()
                    for line in details_lines:
                        output += f"//   {line}\n"
        else:
            reasoning_lines = str(reasoning_trace).splitlines()
            for line in reasoning_lines:
                output += f"// {line}\n"

    # Add prompt and output information if provided
    if prompt_output:
        output += "\n\n// ===== PROMPT & OUTPUT =====\n"
        if isinstance(prompt_output, dict):
            if "prompt" in prompt_output:
                output += "// \n// PROMPT:\n"
                prompt = str(prompt_output["prompt"])
                if len(prompt) > 500:
                    prompt_lines = prompt[:500].splitlines()
                    for line in prompt_lines:
                        output += f"// {line}\n"
                    output += "// ... (truncated)\n"
                else:
                    prompt_lines = prompt.splitlines()
                    for line in prompt_lines:
                        output += f"// {line}\n"
            if "output" in prompt_output:
                output += "// \n// OUTPUT:\n"
                output_text = str(prompt_output["output"])
                if len(output_text) > 500:
                    output_lines = output_text[:500].splitlines()
                    for line in output_lines:
                        output += f"// {line}\n"
                    output += "// ... (truncated)\n"
                else:
                    output_lines = output_text.splitlines()
                    for line in output_lines:
                        output += f"// {line}\n"
            if "model" in prompt_output:
                output += f"// \n// Model: {prompt_output['model']}\n"
            if "tokens" in prompt_output:
                output += f"// Input Tokens: {prompt_output['tokens'].get('input', 'Unknown')}\n"
                output += f"// Output Tokens: {prompt_output['tokens'].get('output', 'Unknown')}\n"
        else:
            prompt_lines = str(prompt_output).splitlines()
            for line in prompt_lines:
                output += f"// {line}\n"

    # Add error trace if provided
    if error_trace:
        output += "\n\n// ===== ERROR TRACE =====\n"
        error_lines = error_trace.splitlines()
        for line in error_lines:
            output += f"// {line}\n"

    # Add score if provided
    if score:
        output += "\n\n// ===== VERIFICATION SCORE =====\n"
        score_lines = str(score).splitlines()
        for line in score_lines:
            output += f"// {line}\n"

    # Add safe indication if provided
    if is_safe is not None:
        output += "\n// ===== SAFETY CHECK =====\n"
        output += f"// Safe: {is_safe}"

    new_output = content + "\n\n"

    for line in output.splitlines():
        if not line.startswith("//"):
            line = "// " + line
        new_output += line + "\n"

    file_path.write_text(new_output, encoding="utf-8")
