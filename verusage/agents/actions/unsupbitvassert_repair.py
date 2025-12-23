"""
Unsupported Bit-Vector Assert Error Repair Action
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class UnsupBitVAssertRepairAction(BaseAction):
    """Action to repair unsupported bit-vector assert errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair unsupported bit-vector assert errors by rewriting the bit-vector assert statement"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Features like spec function and constant variables are NOT supported by the bit-vector prover, and has to be rewritten."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """should improve verification"""
        return {
            "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the unsupported bitvector assert error repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_unsupbitvassert(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.UNSUPBITVASSERT_REPAIR, repaired_codes, guidance
        )

    def _repair_unsupbitvassert(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained unsupported bit-vector assert error repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        error_trace = verus_error.trace[0]

        instruction = f"""Your mission is to fix the unsupported bit-vector assert error ` {error_trace.get_highlights()[0]}' in line `{error_trace.get_text().strip()}' of the program."""

        instruction += """
        There are several code features that are NOT supported by the bit_vector prover yet, and have to be avoided.

        First, You CANNOT use a spec fn inside an expression with `by (bit_vector)`. Instead, you should inline the definition of the spec function inside the assertion using `by (bit_vector)`.

For example, the following code would lead to compilation errors as the `get_bit` spec function is not supported by the bit_vector prover:
```rust
spec fn get_bit(a: u32, b: u32) -> bool {
    (0x1u32 & (a >> b)) == 1
}

proof fn test_macro(x: u32)
    requires x & 2 == 1
{
    assert(get_bit(x, 1)) by (bit_vector)
        requires
            x & 2 == 1
    ; // Unsupported Bitvector ERROR
}
```

To fix the above error, you should rewrite the bit_vector assert statement to the following by inlining the spec function:
```
    assert(get_bit(x, 1)) by {
        assert((0x1u32 & (x >> 1)) == 1) by (bit_vector)
            requires
                x & 2 == 1
        ; // SUCCEEDS
    }
}
```

Second, You CANNOT use a constant variable inside `by (bit_vector)`. Instead, assign the constant variable to another ghost variable, and then use `by (bit_vector)` on the expression that involves that ghost variable.

For example, the following code would lead to unsupported-bit-vector error, as constant variable is NOT supported by bit_vector.
```rust
    pub const MYCONST: u32 = 10;

    assert( MYCONST & 3 == 10 & 3) by (bit_vector)
        requires
            MYCONST == 10,
    ; // MYCONST cannot be directly used here, as bit_vector prover does NOT support const
```

Instead, you should do the following, using a variable with equal value as MYCONST in the bit_vector assert:

```rust
    pub const MYCONST: u32 = 10;

    let ghost tmp = MYCONST; //needed here!

    assert( tmp & 3 == 10 & 3) by (bit_vector)
        requires
            tmp == 10,
    ; // SUCCEED
```
        """

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare query
        line_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info = line_info + error_trace.get_text() + "\n"
        query = self.format_query_template("unsupbitvassert_error", inv_info, code)

        return self.invoke_llm(
            engine,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
