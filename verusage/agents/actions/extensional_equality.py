"""
Extensional Equality Action for sequence/map/set equality repair
"""

from typing import Any

from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt


class ExtensionalEqualityAction(BaseAction):
    """Action to handle extensional equality by comparing collection elements pointwise"""

    @classmethod
    def get_action_type(cls) -> ActionType:
        return ActionType.EXTENSIONAL_EQUALITY

    @classmethod
    def get_description(cls) -> str:
        return "Transform collection equality assertions into element-wise comparisons using extensional equality. Handles sequences (Seq<T>), maps (Map<K,V>), sets (Set<T>), and nested structures by first establishing length/domain equality, then proving element-wise equality through quantified assertions."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "Analyze collection equality patterns and nesting depth. For sequences: establish `seq1.len() == seq2.len()` then `assert forall |i| 0 <= i < seq1.len() implies seq1[i] == seq2[i]`. For maps: establish domain equality then `assert forall |k| map1.dom().contains(k) implies map1[k] == map2[k]`. For sets: use `assert forall |x| set1.contains(x) <==> set2.contains(x)`."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the assertion involves collection equality (`seq1 == seq2`, `map1 == map2`, `set1 == set2`) or collection properties requiring element-wise reasoning. Most effective for sequences, maps, sets, and nested structures where the verifier needs explicit length/domain equality followed by element-wise comparison."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """Extensional equivalence should not affect verified code"""
        from ..shared_types import AcceptanceCriteria

        return {"criteria": AcceptanceCriteria.NO_BANDAID_ASSERTS, "threshold": 0.0}

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the extensional equivalence action"""
        guidance = params.get("guidance", "Apply extensional equivalence for sequence equality")

        # Use self-contained implementation
        repaired_codes = self._extensional_equivalence_repair(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(
            observation, ActionType.EXTENSIONAL_EQUALITY, repaired_codes, guidance
        )

    def _extensional_equivalence_repair(
        self, code: str, verus_error, guidance: str = "", num: int = None, temp: float = 1.0
    ):
        """Self-contained extensional equivalence repair implementation"""

        # Use the provided candidate number

        instruction = load_prompt("extensional_equality")

        # Add guidance if provided
        if guidance:
            instruction += f"\n\nSpecific guidance: {guidance}"

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""Fix this failed assertion using extensional equivalence:

{assertion_info}

Target code:
```verus
{code}
```"""

        # Get examples from the existing example system

        # Use the repair infrastructure to call LLM
        return self.invoke_llm(
            self.config.aoai_debug_model,
            instruction,
            query,
            self.default_system,
            answer_num=num,
            max_tokens=4096,
            temp=temp,
            original_code=code,
        )
