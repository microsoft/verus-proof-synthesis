"""
Main Repair Loop - Simplified
Contains the main repair_veval function without checkpointing overhead.
"""

from pathlib import Path
from typing import Any

from global_config import GlobalConfig
from llm_utils import insert_loop_isolation
from veval import VerusError, VerusErrorType, VEval

from utils import proof_completion_code_change_is_safe, verusfmt_code

from .failure_history import FailureHistoryManager
from .preprocessing import CodeAnalysis, CodePreprocessor
from .shared_types import write_to_temp_dir


class RepairMainLoop:
    """Main repair loop - simplified without checkpointing"""

    def __init__(self, agent_orchestrator=None):
        """
        Initialize with agent orchestrator.

        Args:
            agent_orchestrator: AgentOrchestrator instance
        """
        self.agent_orchestrator = agent_orchestrator

        # Get global resources
        self.config = GlobalConfig.get_config()
        self.logger = GlobalConfig.get_logger()
        self.llm = GlobalConfig.get_llm()

        # Preprocessing
        self.preprocessor: CodePreprocessor | None = None
        self.code_analysis: CodeAnalysis | None = None

        # Failure history management
        self.failure_manager = FailureHistoryManager(max_attempts_per_action=3)

    def setup_failure_manager(self):
        """Set up failure manager connection with agent orchestrator"""
        if self.agent_orchestrator:
            self.agent_orchestrator.set_failure_manager(self.failure_manager)
            self.logger.info("Failure manager connected to agent orchestrator")
        else:
            self.logger.warning("Could not connect failure manager - agent orchestrator not found")

    def setup_preprocessing(self):
        """Setup the preprocessor for code analysis"""
        if not self.preprocessor:
            self.preprocessor = CodePreprocessor(self.logger)
            self.logger.info("Preprocessor initialized")

    def perform_preprocessing(self, code: str, func_name: str | None = None) -> CodeAnalysis:
        """Perform static analysis on the code"""
        if not self.preprocessor:
            self.setup_preprocessing()

        self.code_analysis = self.preprocessor.analyze_code(code, func_name)
        self.logger.info(f"Code analysis completed: {self.code_analysis.function_count} functions")
        return self.code_analysis

    def share_preprocessing_with_agents(self):
        """Share preprocessing results with all agents in the orchestrator"""
        if not self.code_analysis or not self.agent_orchestrator:
            self.logger.warning(
                "Cannot share preprocessing - missing code_analysis or agent_orchestrator"
            )
            return

        # Share with all agents
        for agent in self.agent_orchestrator.agents:
            agent.code_analysis = self.code_analysis
            self.logger.debug(f"Shared code analysis with {agent.__class__.__name__}")

    def repair_veval(
        self,
        code: str,
        max_attempt: int = 5,
        func_name: str | None = None,
        temp_dir: Path | None = None,
        temp: float = 1.0,
        tree_search: bool = False,
        args: dict | None = None,
    ) -> tuple[str, bool]:
        """
        Main repair function - simplified version without checkpointing.

        Args:
            code: Source code to repair
            max_attempt: Maximum number of repair attempts
            func_name: Optional specific function to focus on
            temp_dir: Directory for temporary files
            temp: LLM temperature
            tree_search: Whether to use tree search
            args: Additional arguments

        Returns:
            Tuple of (repaired_code, is_verified)
        """
        args = args or {}
        self.logger.info(f"Starting repair with max_attempt={max_attempt}, func_name={func_name}")

        # Setup failure manager and preprocessing
        self.setup_failure_manager()
        self.setup_preprocessing()

        # Perform preprocessing
        self.perform_preprocessing(code, func_name)
        self.share_preprocessing_with_agents()

        failed_last_time = 0
        attempt = 0
        code_version = 0  # Incremented each time a repair is accepted

        # Ensure loop isolation is present
        if "loop_isolation(false)" not in code:
            code = insert_loop_isolation(code)

        # Set up temp directory - use provided or get from GlobalConfig
        if temp_dir:
            temp_dir = Path(temp_dir)
            GlobalConfig.set_temp_dir(temp_dir)
        else:
            temp_dir = GlobalConfig.get_temp_dir()

        code = verusfmt_code(code)
        # Write initial input if temp_dir is set
        write_to_temp_dir(temp_dir, f"fix-v{code_version}-input.rs", code)

        while attempt < max_attempt:
            attempt += 1
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Repair attempt {attempt}/{max_attempt}")
            self.logger.info(f"{'='*60}")

            # Evaluate current code
            veval = VEval(code, self.logger)
            veval.eval()
            score = veval.get_score()

            self.logger.info(f"Current score: {score}")

            # Check if verification succeeded
            if score.is_correct():
                self.logger.info("✓ Verification successful!")
                write_to_temp_dir(temp_dir, f"fix-v{code_version}-success.rs", code)
                return code, True

            # Get failures
            failures = veval.get_failures()
            if not failures:
                self.logger.info("No failures found but verification not complete")
                return code, False

            # Get one failure to fix
            current_failure = self._get_one_failure(failures)
            if not current_failure:
                self.logger.warning("No fixable failure found")
                return code, False

            self.logger.info(f"Target error: {current_failure.error}")
            self.logger.info(f"Error text: {current_failure.get_text()[:200]}...")

            # Try to repair using agent framework
            success, new_code, metadata = self._try_agent_repair(
                code, current_failure, attempt, args
            )

            if success and new_code and new_code != code:
                # Validate the change
                if self._validate_code_change(code, new_code, current_failure):
                    code = new_code
                    code_version += 1
                    failed_last_time = 0

                    action_name = metadata.get("success_action", "unknown_action")

                    # Write repaired code
                    write_to_temp_dir(
                        temp_dir, f"fix-v{code_version}-a{attempt}-success-{action_name}.rs", code
                    )
                    self.logger.info(f"✓ Repair accepted (version {code_version})")

                    # Mark agent action as accepted
                    if self.agent_orchestrator.last_agent:
                        self.agent_orchestrator.last_agent.mark_last_action_accepted(
                            True, "Code change validated and accepted"
                        )
                else:
                    self.logger.warning("✗ Repair rejected (validation failed)")
                    failed_last_time += 1

                    # Mark agent action as rejected
                    if self.agent_orchestrator.last_agent:
                        self.agent_orchestrator.last_agent.mark_last_action_accepted(
                            False, "Code change validation failed"
                        )
            else:
                self.logger.warning("✗ Repair failed to generate new code")
                failed_last_time += 1

            # Check if we're stuck
            if failed_last_time >= 3:
                self.logger.warning(f"Failed {failed_last_time} times in a row, may be stuck")

        self.logger.warning(f"Max attempts ({max_attempt}) reached without full success")
        return code, False

    def _get_one_failure(
        self,
        verus_errors: list[VerusError],
    ) -> VerusError | None:
        """
        Get one failure to fix, with prioritization.

        Args:
            failures: List of failures
            func_name: Optional function name to focus on
            args: Additional arguments

        Returns:
            Selected failure or None
        """
        # type error gets first priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.MismatchedType:
                return verus_error

        # array-length precondition gets second priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.PreCondFailVecLen:
                return verus_error

        # arith overflow 3rd priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.ArithmeticFlow:
                return verus_error

        # inv-fail before loop 4th priority
        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.InvFailFront:
                return verus_error

        for verus_error in verus_errors:
            if verus_error.error == VerusErrorType.InvFailEnd:
                return verus_error

        # default
        return verus_errors[0]

    def _try_agent_repair(
        self,
        code: str,
        error: VerusError,
        attempt: int,
        args: dict | None = None,
    ) -> tuple[bool, str, dict[str, Any]]:
        """
        Try to repair using agent framework.

        Returns:
            (success, new_code, metadata)
        """
        if not self.agent_orchestrator:
            self.logger.error("Agent orchestrator not available")
            return False, code, {}

        try:
            success, new_code, metadata = self.agent_orchestrator.repair_with_agent(
                code, error, attempt
            )
            return success, new_code, metadata
        except Exception as e:
            self.logger.error(f"Agent repair failed with exception: {e}")
            import traceback

            self.logger.error(traceback.format_exc())
            return False, code, {"error": str(e)}

    def _validate_code_change(
        self,
        old_code: str,
        new_code: str,
        error: VerusError,
    ) -> bool:
        """
        Validate that a code change is safe and reasonable.

        Args:
            old_code: Original code
            new_code: Modified code
            error: The error being fixed

        Returns:
            True if change is valid, False otherwise
        """
        # Check if code actually changed
        if old_code == new_code:
            self.logger.warning("Code didn't change")
            return False

        is_safe = proof_completion_code_change_is_safe(old_code, new_code, self.logger)
        if not is_safe:
            self.logger.warning("Code change failed safety check")
            return False

        self.logger.info("✓ Code change passed validation")
        return True
