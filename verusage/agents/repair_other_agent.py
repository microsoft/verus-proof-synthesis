"""
Default/Other Error Repair Agent for Verus Code Repair
Handles VerusError.Other errors which typically include syntax errors,
unexpected tokens, and other miscellaneous compilation issues.
"""

from global_config import GlobalConfig
from veval import VerusError, VerusErrorType

from .actions import ActionType, action_registry
from .base_agent import ActionResult, BaseAgent, Observation, ReasoningResult


class OtherErrorAgent(BaseAgent):
    """Agent for handling VerusError.Other - typically syntax and compilation errors"""

    def __init__(self):
        super().__init__()

    def can_handle(self, error: VerusError) -> bool:
        """This agent handles VerusError.Other errors"""
        return error.error == VerusErrorType.Other

    def observe(self, code: str, error: VerusError) -> Observation:
        """Observe Other error type and analyze context"""
        # For Other errors, we often don't have detailed trace information
        # Extract what we can from the error
        error_text = error.get_text() if hasattr(error, "get_text") else str(error)

        # Try to extract line information if available
        error_location = (0, 0)  # Default if no line info
        if error.trace and len(error.trace) > 0:
            error_trace = error.trace[0]
            if hasattr(error_trace, "lines") and len(error_trace.lines) >= 2:
                error_location = (error_trace.lines[0], error_trace.lines[1])

        # Extract surrounding context if we have line numbers
        surrounding_context = ""
        if error_location != (0, 0):
            lines = code.splitlines()
            start_line = max(0, error_location[0] - 30)
            end_line = min(len(lines), error_location[1] + 30)
            surrounding_context = "\n".join(lines[start_line:end_line])
        else:
            # If no specific location, provide the whole code as context
            surrounding_context = code

        return Observation(
            code=code,
            error=error,
            error_location=error_location,
            error_text=error_text,
            surrounding_context=surrounding_context,
        )

    def reason(self, observation: Observation) -> ReasoningResult:
        """Determine appropriate action for Other error types"""
        # Use PLAIN_TEXT_REPAIR for unknown/other error types
        primary_action = ActionType.PLAIN_TEXT_REPAIR
        reasoning_explanation = "Using plain text repair for Other error type"

        self.logger.info(f"OtherErrorAgent reasoning: {reasoning_explanation}")

        return ReasoningResult(
            primary_action=primary_action,
            secondary_actions=[],
            reasoning_explanation=reasoning_explanation,
            action_parameters={
                "guidance": f"Fix the error: {observation.error_text}",
                "error_text": observation.error_text,
            },
        )

    def act(self, observation: Observation, reasoning: ReasoningResult) -> ActionResult:
        """Execute the selected repair action"""
        action_type = reasoning.primary_action
        params = reasoning.action_parameters
        self.logger.info(f"OtherErrorAgent executing action: {action_type}")

        try:
            # Get the action class from the registry
            action_class = action_registry.get_action_class(action_type)

            # Create an instance of the action
            action_instance = action_class()

            # Execute the action
            result = action_instance.execute(observation, params)

            # Log the outcome
            if result.success:
                self.logger.info(f"OtherErrorAgent successfully applied {action_type}")
            else:
                self.logger.warning(f"OtherErrorAgent failed to apply {action_type}")

            return result

        except Exception as e:
            self.logger.error(f"OtherErrorAgent action failed: {e}")
            # Return a failure result with original code
            return ActionResult(
                success=False,
                modified_code=observation.code,
                action_taken=action_type,
                explanation=f"Action execution failed: {e}",
                candidates=[observation.code],
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
