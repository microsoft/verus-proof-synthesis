"""
Failure History Manager
Tracks and manages action failures to prevent repeating failed attempts.
"""

from collections import defaultdict

from loguru import logger

from .shared_types import ActionFailureRecord, generate_state_hash


class FailureHistoryManager:
    """Manages failure history to avoid repeating failed actions"""

    def __init__(self, max_attempts_per_action: int = 3):
        self.max_attempts_per_action = max_attempts_per_action
        # Maps state_hash -> list of ActionFailureRecord
        self.failures_by_state: dict[str, list[ActionFailureRecord]] = defaultdict(list)
        # Maps (state_hash, action_type) -> count for quick lookup
        self.attempt_counts: dict[tuple, int] = defaultdict(int)

    def record_failure(
        self,
        code: str,
        action_type: str,
        failure_reason: str,
        action_parameters: dict = None,
        error_context: str = "",
        attempted_changes: str = "",
        detailed_failure_reason: str = "",
    ) -> None:
        """Record a failed action attempt with code changes and detailed reasons"""
        if action_parameters is None:
            action_parameters = {}

        state_hash = generate_state_hash(code, error_context)

        failure_record = ActionFailureRecord(
            state_hash=state_hash,
            action_type=action_type,
            failure_reason=failure_reason,
            action_parameters=action_parameters,
            timestamp="",  # Will be set in __post_init__
            attempted_changes=attempted_changes,
            detailed_failure_reason=detailed_failure_reason,
        )

        self.failures_by_state[state_hash].append(failure_record)
        self.attempt_counts[(state_hash, action_type)] += 1

        logger.debug(
            f"Recorded failure: {action_type} on state {state_hash[:8]} - {failure_reason}"
        )

    def get_failures_for_state(
        self, code: str, action_type: str | None = None, error_context: str = ""
    ) -> list[ActionFailureRecord]:
        """Get all failures for a given state, optionally filtered by action type"""
        state_hash = generate_state_hash(code, error_context)
        failures = self.failures_by_state.get(state_hash, [])

        if action_type:
            failures = [f for f in failures if f.action_type == action_type]

        return failures

    def should_skip_action(self, code: str, action_type: str, error_context: str = "") -> bool:
        """Check if action should be skipped due to too many failures"""
        state_hash = generate_state_hash(code, error_context)
        attempts = self.attempt_counts.get((state_hash, action_type), 0)

        should_skip = attempts >= self.max_attempts_per_action
        if should_skip:
            logger.info(
                f"Skipping {action_type} on state {state_hash[:8]} - "
                f"already failed {attempts} times"
            )

        return should_skip

    def generate_failure_context_prompt(
        self, code: str, action_type: str, error_context: str = ""
    ) -> str:
        """Generate a prompt section with failure context for this action"""
        failures = self.get_failures_for_state(code, action_type, error_context)

        if not failures:
            logger.debug(f"No failure context for {action_type} - no previous failures")
            return ""

        # Sort by timestamp to get most recent failures first
        failures.sort(key=lambda f: f.timestamp, reverse=True)

        context_lines = [
            "\n## ⚠️ Previous Failed Attempts",
            f"WARNING: The {action_type} action has failed {len(failures)} time(s) on this exact code state.",
            "Learn from these failures to avoid repeating the same mistakes:\n",
        ]

        for i, failure in enumerate(
            failures[:2], 1
        ):  # Show max 2 most recent failures for readability
            # More readable failure reason mapping
            readable_reason = {
                "no_error_reduction": "❌ No Error Reduction",
                "compilation_error": "❌ Compilation Error (Syntax)",
                "verification_timeout": "⏱️ Verification Timeout",
                "target_error_not_fixed": "❌ Target Error Not Fixed",
                "bandaid_assertions": "❌ Bandaid Assertions",
                "unsafe_changes": "❌ Unsafe Code Changes",
                "errors_increased": "❌ Introduced New Errors",
                "evaluation_rejected": "❌ Evaluation Rejected",
            }.get(
                failure.failure_reason,
                f"❌ {failure.failure_reason.replace('_', ' ').title()}",
            )

            context_lines.append(f"### Attempt #{i}: {readable_reason}")

            # Show detailed failure reason
            if failure.detailed_failure_reason:
                context_lines.append(f"**Why it failed:** {failure.detailed_failure_reason}")

                # Add specific hints for compilation errors using centralized patterns
                if failure.failure_reason == "compilation_error" and failure.attempted_changes:
                    from .verus_syntax_patterns import get_syntax_hint

                    hint = get_syntax_hint(failure.attempted_changes)
                    if hint:
                        context_lines.append(f"💡 **Hint:** {hint}")

            # Show the attempted changes (candidates or diff)
            if failure.attempted_changes:
                if "=== Candidate #" in failure.attempted_changes:
                    # Show detailed candidate information
                    context_lines.append("**Candidates tried:**")
                    context_lines.append("```")
                    for line in failure.attempted_changes.split("\n"):
                        if line.strip():
                            context_lines.append(line)
                    context_lines.append("```")
                else:
                    # Show simple diff
                    context_lines.append("**What was tried:**")
                    context_lines.append("```diff")
                    for line in failure.attempted_changes.split("\n"):
                        if line.strip():
                            context_lines.append(line)
                    context_lines.append("```")

            # Show key parameters that were tried
            if failure.action_parameters:
                key_params = {
                    k: v
                    for k, v in failure.action_parameters.items()
                    if k in ["guidance", "target", "location"] and v
                }
                if key_params:
                    context_lines.append(f"**Parameters used:** {key_params}")

            context_lines.append("")  # Add blank line between failures

        if len(failures) > 2:
            context_lines.append(f"*... and {len(failures) - 2} more previous failures*")

        context_lines.extend(
            [
                "\n🎯 **Your Task:** Try a fundamentally different approach that addresses the specific failure reasons above.",
                "Avoid the same syntax patterns, parameters, or logic that previously failed.\n",
            ]
        )

        failure_context = "\n".join(context_lines)
        logger.info(
            f"Generated failure context for {action_type}: {len(failures)} previous failures"
        )
        return failure_context

    def get_summary_stats(self) -> dict:
        """Get summary statistics about failure history"""
        total_failures = sum(len(failures) for failures in self.failures_by_state.values())

        # Count failures by action type
        action_failure_counts = defaultdict(int)
        failure_reason_counts = defaultdict(int)

        for failures in self.failures_by_state.values():
            for failure in failures:
                action_failure_counts[failure.action_type] += 1
                failure_reason_counts[failure.failure_reason] += 1

        return {
            "total_failures": total_failures,
            "unique_states_with_failures": len(self.failures_by_state),
            "action_failure_counts": dict(action_failure_counts),
            "failure_reason_counts": dict(failure_reason_counts),
            "blocked_actions": len(
                [k for k, v in self.attempt_counts.items() if v >= self.max_attempts_per_action]
            ),
        }

    def clear_history(self) -> None:
        """Clear all failure history"""
        self.failures_by_state.clear()
        self.attempt_counts.clear()
        logger.info("Cleared failure history")

    def get_blocked_actions(self, code: str, error_context: str = "") -> set[str]:
        """Get set of action types that are blocked for the current state"""
        state_hash = generate_state_hash(code, error_context)
        blocked = set()

        for (s_hash, action_type), count in self.attempt_counts.items():
            if s_hash == state_hash and count >= self.max_attempts_per_action:
                blocked.add(action_type)

        return blocked
