# VeruSAGE Architecture Documentation

A comprehensive guide to the VeruSAGE codebase for intelligent Verus code verification and repair.

## Table of Contents
1. [Overview](#overview)
2. [High-Level Architecture](#high-level-architecture)
3. [Core Components](#core-components)
4. [Agent System](#agent-system)
5. [Action Framework](#action-framework)
6. [Verus Integration](#verus-integration)
7. [Execution Flow](#execution-flow)
8. [Configuration](#configuration)

---

## Overview

**VeruSAGE** is an LLM-powered automated repair framework for [Verus](https://github.com/verus-lang/verus), a verification tool for Rust programs. The system uses a multi-agent architecture with specialized agents that follow an **Observation-Reasoning-Action (ORA)** pattern to intelligently fix verification failures.

### Key Features
- 🤖 **15 Specialized Agents** - Each handles specific Verus error types
- 🔧 **35 Repair Actions** - Comprehensive action catalog for different repair strategies
- 🧠 **LLM-Based Reasoning** - Uses GPT-4, Claude, etc. for intelligent repair planning
- 📊 **Acceptance Criteria** - Structured evaluation of repair attempts

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         main.py                                  │
│                     (Entry Point)                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      RepairRunner                                │
│              (repair_runner.py)                                  │
│  - Initializes AgentOrchestrator                                 │
│  - Initializes RepairMainLoop                                    │
│  - Orchestrates overall repair process                           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      RepairMainLoop                              │
│              (agents/main_loop.py)                               │
│  - Core repair_veval() function                                  │
│  - Preprocessing and analysis                                    │
│  - Error prioritization                                          │
│  - Iterative repair attempts                                     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    AgentOrchestrator                             │
│              (agents/__init__.py)                                │
│  - Manages 15 specialized agents                                 │
│  - Routes errors to appropriate agent                            │
│  - Tracks repair statistics                                      │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Specialized Agents                            │
│  ┌──────────────┐ ┌───────────────┐ ┌──────────────────┐        │
│  │ Assertion    │ │ Precondition  │ │ Postcondition    │        │
│  │ Agent        │ │ Agent         │ │ Agent            │        │
│  └──────────────┘ └───────────────┘ └──────────────────┘        │
│                                                                  │
│  ┌──────────────┐ ┌───────────────┐ ┌──────────────────┐        │
│  │ Invariant    │ │ Arithmetic    │ │ Type Mismatch    │        │
│  │ Agents       │ │ Agent         │ │ Agent            │        │
│  └──────────────┘ └───────────────┘ └──────────────────┘        │
│                        ...and more                               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     ActionRegistry                               │
│              (agents/actions/__init__.py)                        │
│  - 35 registered repair actions                                  │
│  - Self-contained action implementations                         │
│  - Standardized acceptance criteria                              │
└─────────────────────────────────────────────────────────────────┘
```

---

## Core Components

### 1. Entry Point (`main.py`)

The main entry point handles:
- **Argument Parsing**: Configuration file, input/output files, repair parameters
- **Global Configuration**: Initializes `GlobalConfig` singleton
- **Mode Selection**: `agent` or `debug` modes
- **RepairRunner Initialization**: Creates and runs the repair pipeline

```python
# Key command-line arguments
--config      # Path to config JSON file
--mode        # "agent" or "debug"
--input       # Input Rust/Verus file
--output      # Output repaired file
--repair      # Max repair attempts (default: 20)
--ablation    # Enable ablation mode (merged prompts)
```

### 2. RepairRunner (`repair_runner.py`)

Simplified entry point to the agent-based repair system:

```python
class RepairRunner:
    def __init__(self, ablation_mode, accept_rule, args):
        self.agent_orchestrator = AgentOrchestrator(...)
        self.repair_main_loop = RepairMainLoop(agent_orchestrator)

    def run(self, input_file, output_file, args):
        code = open(input_file).read()
        code, is_verified = self.repair_main_loop.repair_veval(code, ...)
        # Write output and return exit code
```

### 3. RepairMainLoop (`agents/main_loop.py`)

The core repair function implementing the iterative repair loop:

```python
def repair_veval(self, code, max_attempt=5, func_name=None, ...):
    # 1. Preprocessing: Analyze code structure
    self.perform_preprocessing(code, func_name)

    # 2. Initial verification
    score = verus_eval(code)

    # 3. Iterative repair loop
    for attempt in range(max_attempt):
        if score.verified:
            return code, True

        # 4. Select one error to fix
        error = self._get_one_failure(score.errors)

        # 5. Agent-based repair
        success, new_code, metadata = self._try_agent_repair(code, error)

        if success:
            code = new_code
            score = verus_eval(code)

    return code, score.verified
```

### 4. GlobalConfig (`global_config.py`)

Singleton pattern for global configuration and resource access:

```python
class GlobalConfig:
    @classmethod
    def initialize(cls, config, logger, temp_dir):
        # Creates LLM, Houdini, MetadataStore

    @classmethod
    def get_llm(cls): ...
    @classmethod
    def get_logger(cls): ...
    @classmethod
    def get_config(cls): ...
    @classmethod
    def get_metadata_store(cls): ...
```

---

## Agent System

### BaseAgent (`agents/base_agent.py`)

Abstract base class implementing the **Observation-Reasoning-Action (ORA)** pattern:

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

    def repair(self, code, error, attempt, tree_search=True):
        """Main repair method: observe → reason → act → validate"""
```

### The Three-Phase Pattern

#### Phase 1: Observation
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

#### Phase 2: Reasoning
```python
@dataclass
class ReasoningResult:
    primary_action: ActionType        # Main repair action
    secondary_actions: List           # Fallback actions
    confidence: float                 # LLM confidence score
    reasoning_explanation: str        # Why this action was chosen
    action_parameters: Dict           # Action-specific parameters
```

#### Phase 3: Action
```python
@dataclass
class ActionResult:
    success: bool
    candidates: List[str]    # Generated code candidates
    action_type: ActionType  # Action that was executed
    metadata: Dict           # Additional action info
```

### Specialized Agents

| Agent | Handles | Description |
|-------|---------|-------------|
| `AssertionErrorAgent` | `AssertFail` | Most complex agent, handles assertion failures with 20+ action types |
| `PreconditionErrorAgent` | `PreCondFail` | Repairs precondition failures |
| `PostconditionErrorAgent` | `PostCondFail` | Repairs postcondition failures |
| `InvariantFrontErrorAgent` | `InvFailFront` | Invariant failures at loop entry |
| `InvariantEndErrorAgent` | `InvFailEnd` | Invariant failures at loop end |
| `ArithmeticOverflowErrorAgent` | `ArithmeticFlow` | Overflow/underflow errors |
| `TypeMismatchErrorAgent` | `MismatchedType` | Type errors and compilation issues |
| `MethodNotFoundAgent` | `MethodNotFound` | Missing method errors |
| `BitVAssertErrorAgent` | `BitVAssertFail` | Bit-vector assertion failures |
| `TerminationErrorAgent` | `TerminationFail` | Termination proof failures |
| `DecFailEndAgent` | `DecFailEnd` | Decreases clause failures |
| `LoopNoDecAgent` | `LoopNoDec` | Missing loop decreases |
| `OtherErrorAgent` | Various | Catch-all for unhandled errors |
| `UnsupportedBitVAgent` | `UnsupportedForBitVector` | Unsupported bit-vector operations |

---

## Action Framework

### ActionRegistry (`agents/actions/__init__.py`)

Central registry for all repair actions:

```python
class ActionRegistry:
    def __init__(self):
        self._actions: Dict[ActionType, Type[BaseAction]] = {}
        self._register_default_actions()

    def register(self, action_type, action_class): ...
    def get_action_class(self, action_type): ...
    def get_action_metadata(self, action_type): ...
```

### BaseAction (`agents/actions/base_action.py`)

Self-contained action implementation:

```python
class BaseAction(ABC):
    @abstractmethod
    def execute(self, observation, reasoning, params) -> ActionResult:
        """Execute the repair action"""

    @classmethod
    def get_description(cls) -> str: ...

    @classmethod
    def get_guidance_template(cls) -> str: ...

    @classmethod
    def get_acceptance_criteria(cls) -> Dict: ...
```

### Action Catalog (35 Actions)

#### Assertion Repair Actions (16)
Used by `AssertionErrorAgent` for LLM-guided action selection:
- `INSTANTIATE_FORALL` - Instantiate universal quantifiers
- `INSTANTIATE_EXISTS` - Instantiate existential quantifiers
- `CASE_ANALYSIS` - Split into cases
- `REVEAL_OPAQUE` - Reveal opaque functions
- `REVEAL_WITH_FUEL` - Reveal with fuel
- `EXTENSIONAL_EQUALITY` - Use extensional equality
- `INDUCTION` - Apply induction
- `INDUCTIVE_LEMMA` - Use inductive lemma patterns
- `COMPUTE` - Add computation hints
- `SEQSETMAP` - Sequence/Set/Map operations
- `NONLINEAR_ARITHMETIC` - Nonlinear arithmetic hints
- `INTEGER_RING` - Integer ring reasoning
- `BIT_VECTOR_REASONING` - Bit-vector proofs
- `ADD_TRIGGER_ASSERT` - Add assertions to trigger quantifiers
- `USELEMMA` - Invoke existing lemmas
- `LOOPINV` - Add/modify loop invariants

#### Error-Type-Specific Actions (14)
Directly invoked by specialized agents:
- `PRECONDITION_REPAIR` - Fix precondition failures
- `PRECONDITION_VECLEN_REPAIR` - Fix vec length preconditions
- `POSTCONDITION_REPAIR` - Fix postcondition failures
- `INVARIANT_FRONT_REPAIR` - Fix loop invariant at entry
- `INVARIANT_END_REPAIR` - Fix loop invariant at end
- `MODIFY_LOOP_INVARIANT` - Modify existing invariants
- `ARITHMETIC_OVERFLOW_REPAIR` - Fix overflow/underflow
- `TYPE_REPAIR` - Fix type mismatches
- `USE_REPAIR` - Fix method not found
- `BITVASSERT_REPAIR` - Fix bit-vector assertions
- `TERMINATION_REPAIR` - Fix termination proofs
- `DECFAILEND_REPAIR` - Fix decreases clause failures
- `LOOPNODEC_REPAIR` - Fix missing loop decreases
- `UNSUPBITVASSERT_REPAIR` - Fix unsupported bit-vector ops

#### Utility Actions (5)
- `PLAIN_TEXT_REPAIR` - Generic LLM repair
- `SYNTAX_REPAIR` - Fix syntax errors
- `EXPECTED_PARENTHESES_REPAIR` - Fix parenthesis issues
- `FALLBACK_LLM_REPAIR` - Default when action unknown
- `MERGED_PROMPT_ABLATION` - Ablation study mode

### Acceptance Criteria

```python
class AcceptanceCriteria(Enum):
    COMPLETE_FIX = "complete_fix"                           # Must fix all errors
    ERROR_REDUCTION = "error_reduction"                     # Must reduce error count
    VERIFICATION_IMPROVEMENT = "verification_improvement"   # Standard improvement
    DONT_AFFECT_VERIFIED = "dont_affect_verified"          # Don't break working code
```

---

## Verus Integration

### veval.py

Core Verus verification integration:

```python
# Error Types
class VerusErrorType(Enum):
    PreCondFail = 1      # Precondition failure
    PostCondFail = 2     # Postcondition failure
    InvFailEnd = 3       # Invariant fails at loop end
    InvFailFront = 4     # Invariant fails at loop entry
    AssertFail = 11      # Assertion failure
    MismatchedType = 13  # Type mismatch
    ArithmeticFlow = 14  # Arithmetic overflow/underflow
    # ... 25+ error types

# Verification evaluation
def verus_eval(code: str) -> EvalScore:
    """Run Verus on code and return structured results"""
    # Writes code to temp file
    # Runs Verus with JSON output
    # Parses errors into VerusError objects
    # Returns EvalScore with verified status and error list

@dataclass
class EvalScore:
    verified: bool
    errors: List[VerusError]
    time: float
```

### VerusError Structure

```python
class VerusError:
    error: VerusErrorType    # Error type enum
    traces: List[ErrorTrace] # Stack trace
    trigger_expr: List[str]  # Trigger expressions
    assertion_ranges: List   # Assertion line ranges

    def get_text(self, snippet=True) -> str:
        """Get error text with surrounding code context"""
```

---

## Execution Flow

### Complete Repair Cycle

```
1. main.py
   ├── Parse arguments
   ├── Load config
   └── Initialize GlobalConfig
           │
           ▼
2. RepairRunner.run()
   ├── Read input file
   └── Call repair_main_loop.repair_veval()
           │
           ▼
3. RepairMainLoop.repair_veval()
   ├── Preprocess code (static analysis)
   ├── Initial verus_eval()
   └── For each attempt:
       │
       ├── Select error (_get_one_failure)
       ├── _try_agent_repair()
       │       │
       │       ▼
       │   4. AgentOrchestrator.repair_with_agent()
       │      ├── get_agent_for_error()
       │      └── agent.repair()
       │              │
       │              ▼
       │          5. Agent ORA Cycle:
       │             ├── observe() → Observation
       │             ├── reason()  → ReasoningResult
       │             ├── act()     → ActionResult
       │             └── apply_action() → Validate candidates
       │                     │
       │                     ▼
       │                 6. For each candidate:
       │                    ├── Compile check
       │                    ├── Safety check
       │                    ├── verus_eval()
       │                    └── Acceptance evaluation
       │
       └── Update code if improved
```

---

## Configuration

### Config File Format

```json
{
    "verus_path": "/path/to/verus",
    "llm_type": "anthropic",
    "llm_model": "claude-sonnet-4-20250514",
    "api_key": "your-api-key",
    "temperature": 1.0,
    "top_p": 1.0,
    "n": 4
}
```

### Supported LLM Providers
- **OpenAI**: GPT-4, GPT-4-turbo, o4-mini
- **Anthropic**: Claude 3.5 Sonnet, Claude 4 Sonnet
- **Google**: Gemini models

---

## Key Files Reference

| File | Purpose |
|------|---------|
| `main.py` | Entry point and argument parsing |
| `repair_runner.py` | High-level repair orchestration |
| `agents/main_loop.py` | Core repair loop implementation |
| `agents/__init__.py` | AgentOrchestrator and agent exports |
| `agents/base_agent.py` | BaseAgent abstract class |
| `agents/shared_types.py` | Shared dataclasses and types |
| `agents/repair_assert_agent.py` | Assertion repair specialist |
| `agents/actions/__init__.py` | ActionRegistry |
| `agents/actions/base_action.py` | BaseAction abstract class |
| `veval.py` | Verus integration and evaluation |
| `global_config.py` | Global configuration singleton |
| `infer.py` | LLM inference wrapper |
| `houdini.py` | Houdini invariant inference |
| `utils.py` | Utility functions |

---

## Further Reading

- [agents/README.md](agents/README.md) - Agent framework details
- [agents/actions/README.md](agents/actions/README.md) - Complete action catalog
- [agents/DEBUG_README.md](agents/DEBUG_README.md) - Debugging guide
