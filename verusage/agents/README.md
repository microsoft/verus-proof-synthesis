# Verus Agent Framework

This directory contains the modular agent framework for intelligent Verus code repair using the **Observation-Reasoning-Action (ORA)** pattern.

## Architecture Overview

```
agents/
├── __init__.py                   # AgentOrchestrator + all agent exports
├── base_agent.py                 # BaseAgent abstract class (ORA pattern)
├── main_loop.py                  # RepairMainLoop (core repair loop)
├── shared_types.py               # Shared dataclasses and types
├── preprocessing.py              # Static code analysis
├── failure_history.py            # Failure tracking and learning
│
├── repair_assert_agent.py        # Assertion failures (most complex)
├── repair_precond_agent.py       # Precondition failures
├── repair_postcond_agent.py      # Postcondition failures
├── repair_inv_front_agent.py     # Invariant at loop entry
├── repair_inv_end_agent.py       # Invariant at loop end
├── repair_arithmetic_agent.py    # Overflow/underflow errors
├── repair_type_agent.py          # Type mismatch errors
├── repair_termination_agent.py   # Termination proof failures
├── repair_decfailend_agent.py    # Decreases clause failures
├── repair_loopnodec_agent.py     # Missing loop decreases
├── repair_bitvassert_agent.py    # Bit-vector assertions
├── repair_use_agent.py           # Method not found errors
├── repair_unsupportedbitv_agent.py # Unsupported bit-vector ops
├── repair_other_agent.py         # Catch-all for other errors
│
├── actions/                      # 35 repair action implementations
│   ├── __init__.py               # ActionRegistry
│   ├── base_action.py            # BaseAction abstract class
│   ├── action_types.py           # ActionType enum
│   │
│   │   # Assertion Actions (for LLM reasoning)
│   ├── add_trigger_assert.py     # Add assert to trigger quantifiers
│   ├── instantiate_forall.py     # Instantiate universal quantifiers
│   ├── instantiate_exists.py     # Instantiate existential quantifiers
│   ├── case_analysis.py          # Split proof into cases
│   ├── reveal_opaque.py          # Reveal opaque functions
│   ├── reveal_with_fuel.py       # Reveal with specific fuel
│   ├── extensional_equality.py   # Prove equality via extensionality
│   ├── induction.py              # Apply induction
│   ├── inductive_lemma.py        # Use inductive lemma patterns
│   ├── compute.py                # Add computation hints
│   ├── seqsetmap.py              # Seq/Set/Map operations
│   ├── nonlinear_arithmetic.py   # Nonlinear arithmetic hints
│   ├── integer_ring.py           # Integer ring reasoning
│   ├── bit_vector_reasoning.py   # Bit-vector proofs
│   ├── uselemma.py               # Invoke existing lemmas
│   ├── loopinv.py                # Add/modify loop invariants
│   ├── modify_loop_invariant.py  # Modify existing invariants
│   │
│   │   # Error-Type-Specific Actions (direct invocation)
│   ├── precondition_repair.py    # PreCondFail errors
│   ├── precondition_veclen_repair.py # Vec length preconditions
│   ├── postcondition_repair.py   # PostCondFail errors
│   ├── invariant_repair.py       # InvFailFront/End errors
│   ├── arithmetic_overflow_repair.py # ArithmeticFlow errors
│   ├── type_repair.py            # MismatchedType errors
│   ├── decfailend_repair.py      # DecFailEnd errors
│   ├── loopnodec_repair.py       # LoopNoDec errors
│   ├── bitvassert_repair.py      # BitVAssertFail errors
│   ├── termination_repair.py     # TerminationFail errors
│   ├── unsupbitvassert_repair.py # UnsupportedForBitVector errors
│   │
│   │   # Utility Actions
│   ├── syntax_repair.py          # Compilation/syntax errors
│   ├── expected_parentheses_repair.py # Parenthesis fixes
│   ├── special_repair.py         # PlainTextRepairAction
│   ├── fallback_llm_repair.py    # Default when action unknown
│   └── merged_prompt_ablation.py # Ablation study mode
│
└── prompts/                      # LLM prompt templates
```

## Core Components

### 1. AgentOrchestrator (`__init__.py`)

Manages and routes errors to the appropriate specialized agent:

```python
class AgentOrchestrator:
    def __init__(self, ablation_mode=False, accept_rule="default", args=None):
        self.agents = [
            AssertionErrorAgent(...),
            PostconditionErrorAgent(),
            PreconditionErrorAgent(),
            # ... 15 total agents
        ]

    def get_agent_for_error(self, error: VerusError) -> BaseAgent:
        """Select appropriate agent for the error type"""

    def repair_with_agent(self, code, error, attempt) -> Tuple[bool, str, Dict]:
        """Run repair using the matching agent"""
```

### 2. BaseAgent (`base_agent.py`)

Abstract base class implementing the three-phase ORA pattern:

```python
class BaseAgent(ABC):
    @abstractmethod
    def can_handle(self, error: VerusError) -> bool:
        """Check if this agent can handle the given error type"""

    @abstractmethod
    def observe(self, code: str, error: VerusError) -> Observation:
        """Phase 1: Analyze code context and error details"""

    @abstractmethod
    def reason(self, observation: Observation) -> ReasoningResult:
        """Phase 2: LLM-based reasoning for repair strategy"""

    @abstractmethod
    def act(self, observation, reasoning) -> ActionResult:
        """Phase 3: Execute the planned repair action"""

    def repair(self, code, error, attempt):
        """Main entry: observe → reason → act → validate"""
```

### 3. RepairMainLoop (`main_loop.py`)

Core repair loop that orchestrates the iterative repair process:

```python
def repair_veval(self, code, max_attempt=5, func_name=None):
    # 1. Preprocess code
    self.perform_preprocessing(code, func_name)

    # 2. Iterative repair
    for attempt in range(max_attempt):
        score = verus_eval(code)
        if score.verified:
            return code, True

        error = self._get_one_failure(score.errors)
        success, new_code = self._try_agent_repair(code, error)
        if success:
            code = new_code

    return code, score.verified
```

## The ORA Pattern

### Phase 1: Observation
Collects all relevant context about the error:

```python
@dataclass
class Observation:
    code: str                    # Full source code
    error: VerusError            # The error to fix
    error_context: str           # Surrounding code context
    quantifier_analysis: Dict    # Extracted forall/exists info
    spec_functions: List         # Spec functions in scope
    loop_context: Optional[str]  # Loop information if applicable
```

### Phase 2: Reasoning
LLM determines the best repair strategy:

```python
@dataclass
class ReasoningResult:
    primary_action: ActionType        # Main repair action to try
    secondary_actions: List           # Fallback actions
    confidence: float                 # LLM confidence (0-1)
    reasoning_explanation: str        # Why this action was chosen
    action_parameters: Dict           # Action-specific parameters
```

### Phase 3: Action
Executes the repair and generates candidates:

```python
@dataclass
class ActionResult:
    success: bool
    candidates: List[str]    # Generated code candidates
    action_type: ActionType  # Which action was executed
    metadata: Dict           # Additional action info
```

## Specialized Agents

| Agent | Error Types | Description |
|-------|-------------|-------------|
| `AssertionErrorAgent` | `AssertFail` | Most complex; uses 20+ action types |
| `PreconditionErrorAgent` | `PreCondFail` | Strengthens function contracts |
| `PostconditionErrorAgent` | `PostCondFail` | Adds proof steps at exits |
| `InvariantFrontErrorAgent` | `InvFailFront` | Loop invariant at entry |
| `InvariantEndErrorAgent` | `InvFailEnd` | Loop invariant at end |
| `ArithmeticOverflowErrorAgent` | `ArithmeticFlow` | Overflow bounds |
| `TypeMismatchErrorAgent` | `MismatchedType` | Type fixes |
| `MethodNotFoundAgent` | `MethodNotFound` | Method resolution |
| `BitVAssertErrorAgent` | `BitVAssertFail` | Bit-vector assertions |
| `TerminationErrorAgent` | `TerminationFail` | Termination proofs |
| `DecFailEndAgent` | `DecFailEnd` | Decreases clauses |
| `LoopNoDecAgent` | `LoopNoDec` | Missing loop decreases |
| `UnsupportedBitVAgent` | `UnsupportedForBitVector` | Unsupported ops |
| `OtherErrorAgent` | Various | Catch-all for unhandled errors |

## Usage

### Creating an Agent

```python
from agents import AssertionErrorAgent

agent = AssertionErrorAgent(
    ablation_mode=False,     # Use action decomposition
    accept_rule="default"    # Standard acceptance rules
)

if agent.can_handle(verus_error):
    success, repaired_code, metadata = agent.repair(code, verus_error, attempt=1)
```

### Using the Orchestrator

```python
from agents import AgentOrchestrator

orchestrator = AgentOrchestrator()
success, repaired_code, metadata = orchestrator.repair_with_agent(code, error, attempt=1)
```

## Acceptance Criteria

Each action specifies its acceptance criteria:

```python
class AcceptanceCriteria(Enum):
    COMPLETE_FIX = "complete_fix"                     # Must fix all errors
    ERROR_REDUCTION = "error_reduction"               # Must reduce error count
    VERIFICATION_IMPROVEMENT = "verification_improvement"  # Standard improvement
    DONT_AFFECT_VERIFIED = "dont_affect_verified"    # Don't break working code
```

## Adding a New Agent

1. Create `repair_my_agent.py`:
```python
class MyAgent(BaseAgent):
    def can_handle(self, error):
        return error.error == VerusErrorType.MyErrorType

    def observe(self, code, error):
        # Collect context
        return Observation(...)

    def reason(self, observation):
        # LLM reasoning
        return ReasoningResult(...)

    def act(self, observation, reasoning):
        # Execute action
        return ActionResult(...)
```

2. Register in `__init__.py`:
```python
self.agents.append(MyAgent())
```

## Key Files

| File | Purpose |
|------|---------|
| `__init__.py` | AgentOrchestrator, all exports |
| `base_agent.py` | BaseAgent ABC (ORA pattern) |
| `main_loop.py` | RepairMainLoop.repair_veval() |
| `shared_types.py` | Observation, ReasoningResult, ActionResult |
| `preprocessing.py` | Static code analysis |
| `repair_assert_agent.py` | Most complex agent example |

## See Also

- [actions/README.md](actions/README.md) - Complete action catalog (40+ actions)
- [../ARCHITECTURE.md](../ARCHITECTURE.md) - Full system architecture
