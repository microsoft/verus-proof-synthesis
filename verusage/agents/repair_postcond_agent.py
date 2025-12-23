"""
Postcondition Repair Agent for Verus Code Repair
Specialized agent for handling postcondition failures with direct action invocation.
"""

from global_config import GlobalConfig
from veval import VerusError, VerusErrorType

from .actions import ActionType, action_registry
from .base_agent import ActionResult, BaseAgent, Observation, ReasoningResult


class PostconditionErrorAgent(BaseAgent):
    def __init__(self):
        super().__init__()

    def can_handle(self, error: VerusError) -> bool:
        return error.error == VerusErrorType.PostCondFail

    def observe(self, code: str, error: VerusError) -> Observation:
        """Observe postcondition failure and analyze context"""
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
        """Simple reasoning that directly selects postcondition repair action"""
        self.logger.info("Using direct postcondition repair action")

        # Direct action selection - no complex reasoning needed
        return ReasoningResult(
            primary_action=ActionType.POSTCONDITION_REPAIR,
            secondary_actions=[],
            reasoning_explanation="Direct postcondition repair for PostCondFail error",
            action_parameters={
                "guidance": "Fix the postcondition failure by strengthening ensures clauses or adding intermediate assertions",
                "error_location": observation.error_location,
                "error_text": observation.error_text,
            },
        )

    def act(self, observation: Observation, reasoning: ReasoningResult) -> ActionResult:
        """Execute the postcondition repair action using the action registry"""
        action_type = reasoning.primary_action
        params = reasoning.action_parameters
        self.logger.info(f"Executing postcondition repair action: {action_type}")

        try:
            # Get the action class from the registry
            action_class = action_registry.get_action_class(action_type)

            # Create an instance of the action
            action_instance = action_class()

            # Execute the action
            result = action_instance.execute(observation, params)

            return result

        except Exception as e:
            self.logger.error(f"Postcondition repair action failed: {e}")
            return ActionResult(
                success=False,
                modified_code=observation.code,
                action_taken=action_type,
                explanation=f"Postcondition repair action execution failed: {e}",
            )

    def mark_last_action_accepted(self, accepted: bool, feedback: str = ""):
        """Mark the last action as accepted or rejected with optional feedback"""
        # Get repair history from global metadata store
        repair_history = GlobalConfig.get_metadata_store().get_all_attempts()
        if repair_history:
            last_attempt = repair_history[-1]
            status = "accepted" if accepted else "rejected"
            self.logger.info(f"Action {last_attempt.primary_action} marked as {status}")
            if feedback:
                self.logger.info(f"Feedback: {feedback}")
