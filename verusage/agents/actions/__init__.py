"""
Agent Actions Module
Provides a registry-based system for managing repair actions.
"""

from loguru import logger

from .action_types import ActionType

# Import action implementations
from .add_trigger_assert import AddTriggerAssertAction
from .arithmetic_overflow_repair import ArithmeticOverflowRepairAction
from .base_action import BaseAction
from .bit_vector_reasoning import BitVectorReasoningAction
from .bitvassert_repair import BitVAssertRepairAction
from .case_analysis import CaseAnalysisAction
from .compute import ComputeAction
from .decfailend_repair import DecFailEndRepairAction
from .expected_parentheses_repair import ExpectedParenthesesRepairAction
from .extensional_equality import ExtensionalEqualityAction
from .fallback_llm_repair import FallbackLLMRepairAction
from .induction import InductionAction
from .inductive_lemma import InductiveLemmaAction
from .instantiate_exists import InstantiateExistsAction
from .instantiate_forall import InstantiateForallAction
from .integer_ring import IntegerRingAction
from .invariant_repair import InvariantEndRepairAction, InvariantFrontRepairAction
from .loopinv import LoopInvAction
from .loopnodec_repair import LoopNoDecRepairAction
from .merged_prompt_ablation import MergedPromptAblationAction
from .modify_loop_invariant import ModifyLoopInvariantAction
from .nonlinear_arithmetic import NonlinearArithmeticAction
from .postcondition_repair import PostconditionRepairAction
from .precondition_repair import PreconditionRepairAction
from .precondition_veclen_repair import PreconditionVeclenRepairAction
from .reveal_opaque import RevealOpaqueAction
from .reveal_with_fuel import RevealWithFuelAction
from .seqsetmap import SeqSetMapAction
from .special_repair import PlainTextRepairAction
from .syntax_repair import SyntaxRepairAction
from .termination_repair import TerminationRepairAction
from .type_repair import TypeRepairAction, UseRepairAction
from .unsupbitvassert_repair import UnsupBitVAssertRepairAction
from .uselemma import UseLemmaAction


class ActionRegistry:
    """Registry for managing repair actions"""

    def __init__(self):
        self._actions: dict[ActionType, type[BaseAction]] = {}
        self._register_default_actions()

    def _register_default_actions(self):
        """Register all default actions"""
        self.register(ActionType.ADD_TRIGGER_ASSERT, AddTriggerAssertAction)
        self.register(ActionType.INSTANTIATE_FORALL, InstantiateForallAction)
        self.register(ActionType.INSTANTIATE_EXISTS, InstantiateExistsAction)
        self.register(ActionType.EXTENSIONAL_EQUALITY, ExtensionalEqualityAction)
        self.register(ActionType.INDUCTION, InductionAction)
        self.register(ActionType.INDUCTIVE_LEMMA, InductiveLemmaAction)
        self.register(ActionType.FALLBACK_LLM_REPAIR, FallbackLLMRepairAction)
        self.register(ActionType.MODIFY_LOOP_INVARIANT, ModifyLoopInvariantAction)
        self.register(ActionType.CASE_ANALYSIS, CaseAnalysisAction)
        self.register(ActionType.NONLINEAR_ARITHMETIC, NonlinearArithmeticAction)
        self.register(ActionType.INTEGER_RING, IntegerRingAction)
        self.register(ActionType.REVEAL_OPAQUE, RevealOpaqueAction)
        self.register(ActionType.REVEAL_WITH_FUEL, RevealWithFuelAction)
        self.register(ActionType.BIT_VECTOR_REASONING, BitVectorReasoningAction)
        self.register(ActionType.COMPUTE, ComputeAction)
        self.register(ActionType.SEQSETMAP, SeqSetMapAction)
        self.register(ActionType.USELEMMA, UseLemmaAction)
        self.register(ActionType.LOOPINV, LoopInvAction)

        # Register repair actions for different error types
        self.register(ActionType.DECFAILEND_REPAIR, DecFailEndRepairAction)
        self.register(ActionType.LOOPNODEC_REPAIR, LoopNoDecRepairAction)
        self.register(ActionType.ARITHMETIC_OVERFLOW_REPAIR, ArithmeticOverflowRepairAction)
        self.register(ActionType.PRECONDITION_REPAIR, PreconditionRepairAction)
        self.register(ActionType.PRECONDITION_VECLEN_REPAIR, PreconditionVeclenRepairAction)
        self.register(ActionType.POSTCONDITION_REPAIR, PostconditionRepairAction)
        self.register(ActionType.INVARIANT_FRONT_REPAIR, InvariantFrontRepairAction)
        self.register(ActionType.INVARIANT_END_REPAIR, InvariantEndRepairAction)
        self.register(ActionType.TYPE_REPAIR, TypeRepairAction)
        self.register(ActionType.USE_REPAIR, UseRepairAction)
        self.register(ActionType.PLAIN_TEXT_REPAIR, PlainTextRepairAction)
        self.register(ActionType.SYNTAX_REPAIR, SyntaxRepairAction)
        self.register(ActionType.EXPECTED_PARENTHESES_REPAIR, ExpectedParenthesesRepairAction)
        self.register(ActionType.MERGED_PROMPT_ABLATION, MergedPromptAblationAction)
        self.register(ActionType.BITVASSERT_REPAIR, BitVAssertRepairAction)
        self.register(ActionType.TERMINATION_REPAIR, TerminationRepairAction)
        self.register(ActionType.UNSUPBITVASSERT_REPAIR, UnsupBitVAssertRepairAction)

    def register(self, action_type: ActionType, action_class: type[BaseAction]):
        """Register a new action"""
        self._actions[action_type] = action_class

    def get_action_class(self, action_type: ActionType) -> type[BaseAction]:
        """Get the action class for a given action type"""
        if action_type not in self._actions:
            raise ValueError(f"Unknown action type: {action_type}")
        return self._actions[action_type]

    def get_action_type(self, action_class: type[BaseAction]) -> ActionType:
        """Get the action type for a given action class"""
        for action_type, cls in self._actions.items():
            if cls == action_class:
                return action_type
        raise ValueError(f"Action class {action_class.__name__} is not registered")

    def get_all_actions(self) -> list[ActionType]:
        """Get all registered action types"""
        return list(self._actions.keys())

    def get_action_metadata(self, action_type: ActionType) -> dict:
        """Get metadata for an action"""
        action_class = self.get_action_class(action_type)
        return {
            "name": action_type.value,
            "description": action_class.get_description(),
            "guidance_template": action_class.get_guidance_template(),
            "when_to_apply": action_class.get_when_to_apply(),
            "acceptance_criteria": action_class.get_acceptance_criteria(),
        }

    def generate_system_prompt_section(self) -> str:
        """Generate the action descriptions for the system prompt"""
        sections = []
        for action_type in self._actions.keys():
            action_class = self._actions[action_type]
            sections.append(
                f"**For {action_type.value.upper()}**: {action_class.get_guidance_template()}"
            )
        return "\n\n".join(sections)


# Global registry instance
action_registry = ActionRegistry()

# Verify registration happened correctly
logger.info(f"Action registry initialized with {len(action_registry._actions)} actions")
logger.info(f"Registered actions: {[action.value for action in action_registry._actions.keys()]}")

# Export the main components
__all__ = ["ActionType", "BaseAction", "action_registry"]
