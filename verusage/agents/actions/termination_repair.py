"""
Cannot prover termination error repair Action
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class TerminationRepairAction(BaseAction):
    """Action to repair cannot-prove-termination errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair termination errors by analyzing the decrease clause of recursive calls"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Look at the decrease clause of the recursive call and add an assert statement accordingly."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """should improve verification"""
        return {
            "criteria": AcceptanceCriteria.VERIFICATION_IMPROVEMENT,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the termination repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_termination(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.TERMINATION_REPAIR, repaired_codes, guidance
        )

    def _repair_termination(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained termination repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        error_trace = verus_error.trace[0]

        instruction = f"""Your mission is to fix the cannot-prove termination error caused by the call of a recursive function, ` {error_trace.get_highlights()[0]}', in line `{error_trace.get_text().strip()}' of the program. """

        instruction += """
        This cannot-prove termination error happens when the program invokes a recursive proof function F inside function F. In Verus, to prove that recursion will terminate, each recursive function (e.g., F) has a `decreases` clause, specifying an expression E whose value should strictly decrease at each invocation (E is an expression about F's parameters). When Verus cannot prove the value of E decreases from one invocation to the next, this cannot-prove termination error will occur.

        To fix this error, please check the `decreases` clause of the recursive function involved here. And then, add an assert statement stating the fact that the decreases clause is satisfied. This assert statement will then become the proof target for follow-up proof steps, and the cannot-prove termination error will disappear.


        Hhere is an example:
        This code may trigger a cannot-prove termination error.
        ```
        proof fn foo( v: u32)
        ensures
            xxx,
        decreases v,
        {
            ...
            foo (u);
        }
        ```

        We can easily fix this error in the following:
        ```
        proof fn foo( v: u32)
        ensures
            xxx,
        decreases v,
        {
            ...
            assert(u < v); //assert the decrease clause
            foo (u);
        }
        ```

        Of course, if you realize that the decrease clause may indeed not be satisfied, you should adjust the corresponding parameter(s) of the recursive proof function.

"""

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare query
        line_info = f"Line {error_trace.lines[0]}-{error_trace.lines[1]}:\n"
        inv_info = line_info + error_trace.get_text() + "\n"
        query = self.format_query_template("decfailend_error", inv_info, code)

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
