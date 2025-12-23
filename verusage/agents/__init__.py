"""
Agents module for Verus Code Repair Framework
Contains specialized agents for different types of verification errors.
"""

from typing import Any

from global_config import GlobalConfig
from veval import VerusError

from .base_agent import (
    AcceptanceCriteria,
    AcceptanceEvaluator,
    ActionResult,
    ActionType,
    BaseAgent,
    Observation,
    ReasoningResult,
)
from .preprocessing import CodeAnalysis, CodePreprocessor
from .repair_arithmetic_agent import ArithmeticOverflowErrorAgent
from .repair_assert_agent import AssertionErrorAgent
from .repair_bitvassert_agent import BitVAssertErrorAgent
from .repair_decfailend_agent import DecFailEndAgent
from .repair_inv_end_agent import InvariantEndErrorAgent
from .repair_inv_front_agent import InvariantFrontErrorAgent
from .repair_loopnodec_agent import LoopNoDecAgent
from .repair_other_agent import OtherErrorAgent
from .repair_postcond_agent import PostconditionErrorAgent
from .repair_precond_agent import PreconditionErrorAgent
from .repair_precond_veclen_agent import VeclenPreconditionErrorAgent
from .repair_termination_agent import TerminationErrorAgent
from .repair_type_agent import TypeMismatchErrorAgent
from .repair_unsupportedbitv_agent import UnsupportedBitVAgent
from .repair_use_agent import MethodNotFoundAgent


class AgentOrchestrator:
    """Orchestrates multiple agents for comprehensive code repair"""

    def __init__(
        self,
        ablation_mode=False,
        accept_rule="default",
        args=None,
    ):
        # Access global configuration and resources
        self.config = GlobalConfig.get_config()
        self.logger = GlobalConfig.get_logger()

        self.ablation_mode = ablation_mode
        self.args = args
        self.swap_case_compute = args.get("swap_case_compute", False) if args else False
        self.failure_manager = None  # Will be set by main loop

        self.agents = [
            AssertionErrorAgent(
                ablation_mode=ablation_mode,
                accept_rule=accept_rule,
                args=args,
            ),
            PostconditionErrorAgent(),
            PreconditionErrorAgent(),
            VeclenPreconditionErrorAgent(),
            InvariantFrontErrorAgent(),
            InvariantEndErrorAgent(),
            ArithmeticOverflowErrorAgent(),
            TypeMismatchErrorAgent(),
            MethodNotFoundAgent(),
            BitVAssertErrorAgent(),
            TerminationErrorAgent(),
            DecFailEndAgent(),
            LoopNoDecAgent(),
            OtherErrorAgent(),
            UnsupportedBitVAgent(),
        ]

        # Set swap_case_compute flag for all agents
        for agent in self.agents:
            agent.swap_case_compute = self.swap_case_compute
            if self.swap_case_compute:
                self.logger.info(f"Enabled swap_case_compute for {agent.__class__.__name__}")

        self.repair_history = []
        self.last_agent = None  # Track the last agent used for acceptance marking
        self.current_temp_dir = None  # Track current temp_dir for agents

    def set_failure_manager(self, failure_manager):
        """Set the failure manager for all agents and actions"""
        self.failure_manager = failure_manager
        # Pass failure manager to all agents
        for agent in self.agents:
            if hasattr(agent, "set_failure_manager"):
                agent.set_failure_manager(failure_manager)

    def get_agent_for_error(self, error: VerusError) -> BaseAgent | None:
        """Select the appropriate agent for the given error"""
        for agent in self.agents:
            if agent.can_handle(error):
                return agent
        self.logger.warning(f"No agent found for error type: {error.error}")
        return None

    def repair_with_agent(
        self,
        code: str,
        error: VerusError,
        attempt: int,
        tree_search=False,
    ) -> tuple[bool, str, dict[str, Any]]:
        """Repair code using the agent framework"""
        agent = self.get_agent_for_error(error)

        if not agent:
            self.logger.warning(f"No agent available for error type: {error.error}")
            return False, code, {"error": "No suitable agent found"}

        self.logger.info(f"Using {agent.__class__.__name__} for repair")
        self.last_agent = agent  # Track the agent being used
        success, repaired_code, metadata = agent.repair(code, error, attempt, tree_search)

        # Get candidate information from metadata store (not from return dict)
        attempt_id = metadata.get("attempt_id", attempt)
        attempt_metadata = GlobalConfig.get_metadata_store().get_attempt(attempt_id)

        if attempt_metadata:
            candidates_count = len(attempt_metadata.candidates)
            # Enhance metadata with action result details for backward compatibility
            metadata["candidates"] = [c.candidate_code for c in attempt_metadata.candidates]
            metadata["candidates_count"] = candidates_count
            metadata["has_multiple_candidates"] = candidates_count > 1
        else:
            # Fallback: just use repaired_code
            candidates_count = 1 if repaired_code else 0
            metadata["candidates"] = [repaired_code] if repaired_code else []
            metadata["candidates_count"] = candidates_count
            metadata["has_multiple_candidates"] = False

        self.logger.info(f"Agent generated {candidates_count} repair candidates")

        # Log the repair attempt
        repair_record = {
            "agent": agent.__class__.__name__,
            "error_type": error.error.name,
            "success": success,
            "metadata": metadata,
            "candidates_generated": candidates_count,
        }
        self.repair_history.append(repair_record)

        return success, repaired_code, metadata

    def get_repair_statistics(self) -> dict[str, Any]:
        """Get statistics about repair attempts"""
        total_repairs = len(self.repair_history)
        successful_repairs = sum(1 for r in self.repair_history if r["success"])

        agent_stats = {}
        error_stats = {}

        for record in self.repair_history:
            agent_name = record["agent"]
            error_type = record["error_type"]

            if agent_name not in agent_stats:
                agent_stats[agent_name] = {"total": 0, "successful": 0}
            agent_stats[agent_name]["total"] += 1
            if record["success"]:
                agent_stats[agent_name]["successful"] += 1

            if error_type not in error_stats:
                error_stats[error_type] = {"total": 0, "successful": 0}
            error_stats[error_type]["total"] += 1
            if record["success"]:
                error_stats[error_type]["successful"] += 1

        return {
            "total_repairs": total_repairs,
            "successful_repairs": successful_repairs,
            "success_rate": successful_repairs / total_repairs if total_repairs > 0 else 0,
            "agent_statistics": agent_stats,
            "error_statistics": error_stats,
        }


__all__ = [
    "BaseAgent",
    "Observation",
    "ReasoningResult",
    "ActionResult",
    "ActionType",
    "ActionBranch",
    "AcceptanceCriteria",
    "AcceptanceEvaluator",
    "AssertionErrorAgent",
    "PostconditionErrorAgent",
    "PreconditionErrorAgent",
    "VeclenPreconditionErrorAgent",
    "DecFailEndAgent",
    "LoopNoDecAgent",
    "InvariantFrontErrorAgent",
    "InvariantEndErrorAgent",
    "ArithmeticOverflowErrorAgent",
    "TypeMismatchErrorAgent",
    "MethodNotFoundAgent",
    "OtherErrorAgent",
    "AgentOrchestrator",
    "BitVAssertErrorAgent",
    "TerminationErrorAgent",
    "UnsupportedBitVAgent",
    "CodeAnalysis",
    "CodePreprocessor",
]
