"""
Repair Runner - Simplified Entry Point
Direct interface to agent-based repair without refinement layer.
"""

from typing import Any

from agent_framework import AgentOrchestrator
from agents.main_loop import RepairMainLoop
from global_config import GlobalConfig


class RepairRunner:
    """
    Simplified repair runner that works directly with AgentOrchestrator.

    No refinement dependency - just agents and the main repair loop.
    """

    def __init__(self, ablation_mode=False, accept_rule="default", args=None):
        """
        Initialize the repair runner.

        Args:
            ablation_mode: Whether to use ablation mode (merged prompts)
            accept_rule: Acceptance rule for repairs ('least', 'most', 'default')
            args: Additional arguments dict
        """
        self.config = GlobalConfig.get_config()
        self.logger = GlobalConfig.get_logger()

        # Initialize agent orchestrator directly
        self.agent_orchestrator = AgentOrchestrator(
            ablation_mode=ablation_mode, accept_rule=accept_rule, args=args
        )

        # Initialize the repair main loop
        # Pass agent_orchestrator directly instead of refinement
        self.repair_main_loop = RepairMainLoop(agent_orchestrator=self.agent_orchestrator)

    def run(self, input_file: str, output_file: str, args: dict = None) -> int:
        """
        Run repair on a file.

        Args:
            input_file: Path to input file
            output_file: Path to output file
            args: Additional arguments

        Returns:
            Exit code: 0 if verified and safe, 233 otherwise
        """
        args = args or {}

        content = open(input_file).read()

        func_name = args.get("func_name", None)
        repair = args.get("repair", 2)

        if func_name:
            print(f"Handling function: {func_name}")
        print(f"Maximum repair steps: {repair}")

        code, is_verified = self.run_code(content, func_name, repair, args)

        # Write output file
        with open(output_file, "w", encoding="utf-8") as wf:
            wf.write(code)

        # Determine exit code (safety already checked in repair_veval)
        exit_code = 0 if is_verified else 233

        self.logger.info(f"{'='*60}")
        self.logger.info(f"FINAL RESULT: {'VERIFIED' if is_verified else 'FAILED'}")
        self.logger.info(f"Exit code: {exit_code}")
        self.logger.info(f"{'='*60}")

        return exit_code

    def run_code(
        self, code: str, func_name=None, repair_num=5, args: dict = None
    ) -> tuple[str, bool]:
        """
        Run repair on code string.

        Args:
            code: Source code to repair
            func_name: Optional function name to focus on
            repair_num: Maximum number of repair attempts
            args: Additional arguments

        Returns:
            Tuple of (repaired_code, is_verified)
        """
        args = args or {}

        self.logger.info("Starting repair process...")
        if func_name:
            self.logger.info(f"  Target function: {func_name}")
        self.logger.info(f"  Max repair attempts: {repair_num}")

        tree_search = args.get("tree_search", False)
        self.logger.info(f"  Tree search: {'enabled' if tree_search else 'disabled'}")

        accept_rule = args.get("accept_rule", "default")
        self.logger.info(f"  Accept strategy: {accept_rule}")

        ablation_mode = args.get("ablation_mode", False)
        if ablation_mode:
            self.logger.info("  Mode: Ablation (merged prompt)")
        else:
            self.logger.info("  Mode: Normal (action decomposition)")

        # Run repair through main loop
        code, is_verified = self.repair_main_loop.repair_veval(
            code=code,
            max_attempt=repair_num,
            func_name=func_name,
            temp=1.0,
            tree_search=tree_search,
            args=args,
        )

        self.logger.info("Repair process finished!")
        return code, is_verified

    def get_statistics(self) -> dict[str, Any]:
        """Get repair statistics from the agent orchestrator."""
        stats = self.agent_orchestrator.get_repair_statistics()

        # Add agent-specific statistics if available
        if self.agent_orchestrator.last_agent:
            agent_stats = self.agent_orchestrator.last_agent.get_action_statistics()
            stats["last_agent_stats"] = agent_stats

        return stats
