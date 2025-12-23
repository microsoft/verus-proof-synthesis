# Verus Agent Actions System

This directory contains **35 self-contained repair actions** for the Verus repair agent framework. Each action represents a specific repair strategy for different types of verification errors.

> **See Also**: [../README.md](../README.md) for agent framework | [../../ARCHITECTURE.md](../../ARCHITECTURE.md) for full system architecture

## Overview

The action system transforms verification error repair from a multi-file, cross-cutting concern into a single-file, self-contained implementation. Each action encapsulates:

- **Error analysis and repair logic**
- **LLM prompts and instructions**
- **Acceptance criteria for evaluating success**
- **Direct access to repair infrastructure**

## Action Catalog (35 Actions)

### Assertion Repair Actions (16)

Used by `AssertionErrorAgent` for LLM-guided action selection:

| Action | Purpose |
|--------|---------|
| `INSTANTIATE_FORALL` | Instantiate universal quantifiers with concrete values |
| `INSTANTIATE_EXISTS` | Instantiate existential quantifiers |
| `CASE_ANALYSIS` | Split proof into cases for conditional reasoning |
| `REVEAL_OPAQUE` | Reveal opaque function definitions for verification |
| `REVEAL_WITH_FUEL` | Reveal recursive functions with specific fuel amount |
| `EXTENSIONAL_EQUALITY` | Prove equality via extensionality for collections |
| `INDUCTION` | Apply induction on data structures |
| `INDUCTIVE_LEMMA` | Use inductive lemma patterns |
| `COMPUTE` | Add computation hints for constant expressions |
| `SEQSETMAP` | Sequence/Set/Map operations and lemmas |
| `NONLINEAR_ARITHMETIC` | Nonlinear arithmetic hints |
| `INTEGER_RING` | Integer ring reasoning |
| `BIT_VECTOR_REASONING` | Bit-vector proofs with `by (bit_vector)` |
| `ADD_TRIGGER_ASSERT` | Add assertions to trigger quantifier instantiation |
| `USELEMMA` | Invoke existing lemmas to help prove assertions |
| `LOOPINV` | Add/modify loop invariants |

### Error-Type-Specific Actions (14)

Directly invoked by specialized agents:

| Action | Target Error | Agent |
|--------|-------------|-------|
| `PRECONDITION_REPAIR` | `PreCondFail` | PreconditionErrorAgent |
| `PRECONDITION_VECLEN_REPAIR` | `PreCondFail` (vec length) | VeclenPreconditionErrorAgent |
| `POSTCONDITION_REPAIR` | `PostCondFail` | PostconditionErrorAgent |
| `INVARIANT_FRONT_REPAIR` | `InvFailFront` | InvariantFrontErrorAgent |
| `INVARIANT_END_REPAIR` | `InvFailEnd` | InvariantEndErrorAgent |
| `MODIFY_LOOP_INVARIANT` | Loop invariant issues | InvariantAgents (secondary) |
| `ARITHMETIC_OVERFLOW_REPAIR` | `ArithmeticFlow` | ArithmeticOverflowErrorAgent |
| `TYPE_REPAIR` | `MismatchedType` | TypeMismatchErrorAgent |
| `USE_REPAIR` | `MethodNotFound` | MethodNotFoundAgent |
| `BITVASSERT_REPAIR` | `BitVAssertFail` | BitVAssertErrorAgent |
| `TERMINATION_REPAIR` | `TerminationFail` | TerminationErrorAgent |
| `DECFAILEND_REPAIR` | `DecFailEnd` | DecFailEndAgent |
| `LOOPNODEC_REPAIR` | `LoopNoDec` | LoopNoDecAgent |
| `UNSUPBITVASSERT_REPAIR` | `UnsupportedForBitVector` | UnsupportedBitVAgent |

### Utility Actions (5)

| Action | Purpose |
|--------|---------|
| `PLAIN_TEXT_REPAIR` | Generic LLM repair for `Other` error types |
| `SYNTAX_REPAIR` | Fix compilation/syntax errors (delegates to sub-actions) |
| `EXPECTED_PARENTHESES_REPAIR` | Fix parenthesis-related syntax errors |
| `FALLBACK_LLM_REPAIR` | Default when LLM returns unknown action |
| `MERGED_PROMPT_ABLATION` | Ablation study mode with merged prompts |

## Acceptance Criteria System

All actions use standardized acceptance criteria based on the `AcceptanceCriteria` enum:

### Criteria Types

| Criteria | Description |
|----------|-------------|
| `VERIFICATION_IMPROVEMENT` | Must fix the target error and improve verification (default) |
| `ERROR_REDUCTION` | Must reduce overall error count |
| `NO_BANDAID_ASSERTS` | Must not add bandaid assertions (assume/admit) |
| `DONT_AFFECT_VERIFIED` | Must not break already verified code |

### Action-Specific Criteria

Most actions use `VERIFICATION_IMPROVEMENT`. Notable exceptions:

| Action | Criteria | Rationale |
|--------|----------|-----------|
| `ARITHMETIC_OVERFLOW_REPAIR` | `NO_BANDAID_ASSERTS` | Prevent unsafe admits |
| `ADD_TRIGGER_ASSERT` | `ERROR_REDUCTION` | Must reduce overall errors |

### Implementation Example

```python
@classmethod
def get_acceptance_criteria(cls) -> Dict[str, Any]:
    return {
        "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
        "threshold": 0.0
    }
```

## Architecture

```
actions/
├── __init__.py           # ActionRegistry - central action management
├── base_action.py        # BaseAction abstract class
├── action_types.py       # ActionType enum (35 types)
├── prompt_loader.py      # Prompt loading utility
│
├── # Assertion actions (16 files)
├── instantiate_forall.py, instantiate_exists.py, ...
│
├── # Error-specific actions (14 files)
├── precondition_repair.py, postcondition_repair.py, ...
│
└── # Utility actions (5 files)
    fallback_llm_repair.py, syntax_repair.py, ...
```

## Adding New Actions

1. Create action file in `actions/` directory
2. Extend `BaseAction` class
3. Implement required methods:
   - `get_description()` - Short description
   - `get_guidance_template()` - LLM guidance
   - `get_acceptance_criteria()` - Evaluation criteria
   - `execute()` - Main repair logic
4. Add to `ActionType` enum in `action_types.py`
5. Register in `ActionRegistry` in `__init__.py`
6. Create prompt file in `prompts/` if needed
