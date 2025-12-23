"""
Arithmetic Overflow Repair Action
Repairs arithmetic overflow/underflow errors by adding bound assertions.
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class ArithmeticOverflowRepairAction(BaseAction):
    """Action to repair arithmetic overflow/underflow errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair arithmetic overflow/underflow errors by adding bound-related loop invariants or assertions"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Explain what properties should be added as loop invariants or assert statements to help prove the expression will not overflow/underflow."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Arithmetic overflow repairs should fix the overflow error"""
        return {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the arithmetic overflow repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_arithmetic_overflow(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.ARITHMETIC_OVERFLOW_REPAIR, repaired_codes, guidance
        )

    def _repair_arithmetic_overflow(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained arithmetic overflow repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        error_trace = verus_error.trace[0]

        # Build the instruction based on code content
        # TODO: let's trust the model in deciding when to handle recusive
        # if "decreases" in code:
        #    instruction = f"""Your mission is to fix the arithmetic underflow/overflow error for the following code. Basically, add an assertion about the bound of `{error_trace.get_highlights()[0]}' right BEFORE the line `{error_trace.get_text()}' in the code. Note that, if the value of this expression is related to a recursively defined spec function in the program, generate a lemma function that shows the monotonicity of this expression could help prove its bound. Please look at the example below to see how a monotonicity lemma function can help eliminate arithmetic underflow/overflow concerns. Only make the minimal changes necessary to fix the arithmetic error."""
        #            examples = GlobalConfig.get_refinement().get_examples("aritherr-recur")
        #        else:
        instruction = f"""Your mission is to fix the arithmetic underflow/overflow error reported for the expression ` {error_trace.get_highlights()[0]}' in line `{error_trace.get_text().strip()}' of the program.

        First of all, please think about what should be the bound of this expression ` {error_trace.get_highlights()[0]}` and add assert statements right before this line to state that bound.

        Then, if this expression is inside a loop, add proper loop invariants that can help Verus prove the bound of this expression.

        Otherwise, add proper assert statements, if needed, about the values/bounds of variables involved in this expression to help Verus reason about the bound of this expression.

        If the value of this expression is related to a recursively defined spec function in the program, you may need to generate a lemma function that shows the monotonicity of this expression in order to prove the expression's bound.
"""

        instruction += """
            If you plan to add loop invariants, keep in mind that loop invariants should hold upon the initial entry to the loop and still holds at the end of the loop body (i.e., maintained across iterations). All invariants should be put in the ```invariant``` block of the loop, like:
            ```
            let x = 0;
            while x < 10
                invariant
                    x >= 0,
                    x <= 10,
                decreases
                    10 - x,
            {
                x = x + 1;
            }
            ```

        Note: The invariant block HAS to be put before the decreases expression, NOT after it. Also, you are NOT allowed to use curly brackets to enclose the invariant block.
            """

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare query
        line_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info = line_info + error_trace.get_text() + "\n"
        query = self.format_query_template("arithmetic_error", inv_info, code)

        # Use the existing repair infrastructure
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
