"""
Bit-Vector Assert Error Repair Action
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class BitVAssertRepairAction(BaseAction):
    """Action to repair bit-vector assert errors"""

    @classmethod
    def get_description(cls) -> str:
        return (
            "Repair bit-vector assert errors by adding requires or convert it into a normal assert"
        )

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Either feed more information to the bit-vector prover through requires clause, or convert this bit-vector assert to a normal assert."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """should improve verification"""
        return {"criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the bitvector assert error repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_bitvassert(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.BITVASSERT_REPAIR, repaired_codes, guidance
        )

    def _repair_bitvassert(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained bit-vector assert error repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        error_trace = verus_error.trace[0]

        instruction = f"""Your mission is to fix the bit-vector assert error ` {error_trace.get_highlights()[0]}' in line `{error_trace.get_text().strip()}' of the program."""

        instruction += """
        There are three solutions:

        Solution 1 (Basic requires): This bit-vector assert does ***not*** propagate any facts from the context about variables, such as from preconditions or variable assignments. So, any facts about variables in a bitwise expression ***must*** be included in the `requires` clause.

Example:
```rust
proof fn test_and(x: u32, y: u32)
  requires x == y
{
    assert(x & 3 == y & 3) by (bit_vector);  // FAILS
    assert(x & 3 == y & 3) by (bit_vector)
        requires x == y;  // SUCCEEDS
}
```

        Solution 2 (Advanced requires): The bit-vector prover CANNOT see the surrounding context, including let-bindings, preconditions, or prior assertions. You must explicitly provide the value/definition of EVERY variable in the bit_vector assertion through the `requires` clause.

CRITICAL: Even if a variable is defined by a let-binding immediately before the assertion, you MUST include its definition in the requires clause!

Example (CORRECT - all variable definitions provided):
```rust
proof fn test_complex(a: u32, b: u32)
{
    let mask = a & 0xff;
    assert(b == a << 8 | mask);

    // Need to prove: (b & 0xff) == mask
    assert((b & 0xff) == mask) by (bit_vector)
        requires
            mask == a & 0xff,        // Must include! Even though mask is defined above
            b == a << 8 | mask;      // Must include! Even though we just asserted it
    // SUCCEEDS - prover knows what both mask and b are
}
```

Example (WRONG - missing variable definitions):
```rust
proof fn test_complex(a: u32, b: u32)
{
    let mask = a & 0xff;
    assert(b == a << 8 | mask);

    assert((b & 0xff) == mask) by (bit_vector)
        requires
            b == a << 8 | mask;      // Only provided b's definition
    // FAILS - prover doesn't know what mask is!
}
```

Key principle: For EVERY variable appearing in the bit_vector assertion, you must add a requires clause that:
- Defines its value (e.g., `mask == a & 0xff`)
- OR relates it to other variables whose values are also specified in requires

The bit_vector prover is completely isolated - treat it as if it has no access to ANY surrounding code.

        Solution 3: It is possible that the asserted expression just cannot be proved by the bit vector prover at this point. In that case, just turn this assert statement into a normal assert. That is, turn `assert(P) by (bit_vector) ...` to `assert(P)`.

"""

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare query
        line_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info = line_info + error_trace.get_text() + "\n"
        query = self.format_query_template("decfailend_error", inv_info, code)

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
