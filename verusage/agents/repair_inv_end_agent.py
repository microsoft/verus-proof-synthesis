"""
Invariant End Repair Agent for Verus Code Repair
Specialized agent for handling invariant failures at the end of loops with direct action invocation.
"""

from global_config import GlobalConfig
from veval import VerusError, VerusErrorType

from .actions import ActionType, action_registry
from .base_agent import ActionResult, BaseAgent, Observation, ReasoningResult


class InvariantEndErrorAgent(BaseAgent):
    def __init__(self):
        super().__init__()

    def can_handle(self, error: VerusError) -> bool:
        return error.error == VerusErrorType.InvFailEnd

    def observe(self, code: str, error: VerusError) -> Observation:
        """Observe invariant end failure and analyze context"""
        error_trace = error.trace[0]
        error_location = (error_trace.lines[0], error_trace.lines[1])
        error_text = error_trace.get_text()

        # Extract surrounding context (15 lines before and after for loop context)
        lines = code.splitlines()
        start_line = max(0, error_location[0] - 15)
        end_line = min(len(lines), error_location[1] + 15)
        surrounding_context = "\n".join(lines[start_line:end_line])

        return Observation(
            code=code,
            error=error,
            error_location=error_location,
            error_text=error_text,
            surrounding_context=surrounding_context,
        )

    def reason(self, observation: Observation) -> ReasoningResult:
        """Simple reasoning that directly selects invariant end repair action"""
        self.logger.info("Using direct invariant end repair action")

        # Direct action selection - no complex reasoning needed
        return ReasoningResult(
            primary_action=ActionType.INVARIANT_END_REPAIR,
            secondary_actions=[ActionType.MODIFY_LOOP_INVARIANT],
            reasoning_explanation="Direct invariant end repair for InvFailEnd error",
            action_parameters={
                "guidance": "Fix the invariant failure at loop exit by adding assertions about the failed invaiant within the loop body or updating the loop invariants if needed",
                "error_location": observation.error_location,
                "error_text": observation.error_text,
                "repair_type": "end",
            },
        )

    def act(self, observation: Observation, reasoning: ReasoningResult) -> ActionResult:
        """Execute the invariant end repair action using the action registry"""
        action_type = reasoning.primary_action
        params = reasoning.action_parameters
        self.logger.info(f"Executing invariant end repair action: {action_type}")

        try:
            # Get the action class from the registry
            action_class = action_registry.get_action_class(action_type)

            # Create an instance of the action
            action_instance = action_class()

            # Execute the action
            result = action_instance.execute(observation, params)

            return result

        except Exception as e:
            self.logger.error(f"Invariant end repair action failed: {e}")
            return ActionResult(
                success=False,
                modified_code=observation.code,
                action_taken=action_type,
                explanation=f"Invariant end repair action execution failed: {e}",
            )

    def mark_last_action_accepted(self, accepted: bool, feedback: str = ""):
        """Mark the last action as accepted or rejected with optional feedback"""
        repair_history = GlobalConfig.get_metadata_store().get_all_attempts()
        if repair_history:
            last_attempt = repair_history[-1]
            status = "accepted" if accepted else "rejected"
            self.logger.info(f"Action {last_attempt.primary_action} marked as {status}")
            if feedback:
                self.logger.info(f"Feedback: {feedback}")
