"""
Action Types for Agent Framework
Contains the ActionType enum definition to avoid circular imports.
"""

from enum import Enum


class ActionType(Enum):
    """Enumeration of all available repair actions"""

    ADD_TRIGGER_ASSERT = "add_trigger_assert"
    INSTANTIATE_FORALL = "instantiate_forall"
    INSTANTIATE_EXISTS = "instantiate_exists"
    FALLBACK_LLM_REPAIR = "fallback_llm_repair"
    MODIFY_LOOP_INVARIANT = "modify_loop_invariant"
    CASE_ANALYSIS = "case_analysis"
    NONLINEAR_ARITHMETIC = "nonlinear_arithmetic"
    INTEGER_RING = "integer_ring"
    REVEAL_OPAQUE = "reveal_opaque"
    REVEAL_WITH_FUEL = "reveal_with_fuel"
    BIT_VECTOR_REASONING = "bit_vector_reasoning"
    EXTENSIONAL_EQUALITY = "extensional_equality"
    INDUCTION = "induction"
    INDUCTIVE_LEMMA = "inductive_lemma"
    COMPUTE = "compute"
    SEQSETMAP = "seqsetmap"
    USELEMMA = "uselemma"
    LOOPINV = "loopinv"
    MERGED_PROMPT_ABLATION = "merged_prompt_ablation"

    # Repair actions for different error types
    DECFAILEND_REPAIR = "decfailend_repair"
    LOOPNODEC_REPAIR = "loopnodec_repair"
    ARITHMETIC_OVERFLOW_REPAIR = "arithmetic_overflow_repair"
    PRECONDITION_REPAIR = "precondition_repair"
    PRECONDITION_VECLEN_REPAIR = "precondition_veclen_repair"
    POSTCONDITION_REPAIR = "postcondition_repair"
    INVARIANT_FRONT_REPAIR = "invariant_front_repair"
    INVARIANT_END_REPAIR = "invariant_end_repair"
    TYPE_REPAIR = "type_repair"
    USE_REPAIR = "use_repair"
    PLAIN_TEXT_REPAIR = "plain_text_repair"
    SYNTAX_REPAIR = "syntax_repair"
    EXPECTED_PARENTHESES_REPAIR = "expected_parentheses_repair"
    BITVASSERT_REPAIR = "bitvassert_repair"
    TERMINATION_REPAIR = "termination_repair"
    UNSUPBITVASSERT_REPAIR = "unsupbitvassert_repair"
