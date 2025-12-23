"""
Precondition Vector Length Repair Action
Repairs vector/array length precondition failure errors by adding loop invariants.
Contains the full repair implementation including prompts and examples.
"""

from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation


class PreconditionVeclenRepairAction(BaseAction):
    """Action to repair vector/array length precondition failure errors"""

    @classmethod
    def get_description(cls) -> str:
        return "Repair vector/array length precondition failure errors by adding loop invariants about array lengths and bounds"

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Add loop invariants specifying array lengths and bounds to ensure array accesses are always within bounds."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Vector length precondition repairs should improve verification"""
        return {"criteria": AcceptanceCriteria.FIX_PRECONDITION, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the vector length precondition repair action"""
        guidance = params.get("guidance", "")

        # Use the self-contained repair implementation
        repaired_codes = self._repair_precondition_veclen_failure(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.PRECONDITION_VECLEN_REPAIR, repaired_codes, guidance
        )

    def _repair_precondition_veclen_failure(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ) -> list[str]:
        """Self-contained vector length precondition failure repair implementation"""

        # Use the provided candidate number
        engine = self.config.aoai_generation_model

        # Get error information
        error_line = verus_error.trace[1].lines[0]
        error_code = verus_error.trace[1].get_text().strip()

        # Build the specific instruction for vector length errors
        instruction = (
            "Your mission is to help Verus prove the array access in the expression `"
            + error_code.strip()
            + f"' is always in bound --- this expression is on Line {error_line}"
            + " of the following program. Basically, you should identify all the arrays accessed (e.g., A[k] or A.set(k,..)) in this expression `"
            + error_code.strip()
            + "' and add the following loop invariants for EACH array: 1. an invariant that specify the array length (i.e., A.len() == ...); 2. an invariant about the array index not under bound (e.g., k >= 0). \n"
        )

        instruction += """
        Response requirements:
        1. Only make the minimal changes necessary to fix the precondition error.
        2. You should only add loop invariants, and you should NOT make any other changes to the program.
        3. You should NOT change function's pre condition or post conditions.
        4. A loop invariant should be specified in the following form:
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant
            idx <= n,
            sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        decreases n - idx,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }

        """

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        query = code

        # Get examples (empty for this specific repair type)

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
