"""
Proof by compute
Contains full implementation with prompts and examples.
Enhanced with dynamic vstd library retrieval.
"""

import re
from pathlib import Path
from typing import Any

from ..shared_types import AcceptanceCriteria
from .action_types import ActionType
from .base_action import ActionResult, BaseAction, Observation
from .prompt_loader import load_prompt

# Import vstd library components
try:
    from vstd_library import ResultFormatter, VstdSearchEngine

    VSTD_AVAILABLE = True
except ImportError:
    VSTD_AVAILABLE = False


class SeqSetMapAction(BaseAction):
    """Action to reason about Seq/Set/Map and their APIs in the proof"""

    def __init__(self):
        super().__init__()
        self.vstd_engine = None
        self.vstd_formatter = None

        # Initialize vstd search if available
        if VSTD_AVAILABLE:
            try:
                # vstd_index.json should be in vstd_library directory
                index_path = (
                    Path(__file__).parent.parent.parent / "vstd_library" / "vstd_index.json"
                )
                if index_path.exists():
                    self.vstd_engine = VstdSearchEngine(str(index_path))
                    self.vstd_formatter = ResultFormatter(search_engine=self.vstd_engine)
                    self.logger.info(f"vstd search engine initialized from {index_path}")
                else:
                    self.logger.warning(f"vstd index not found at {index_path}")
            except Exception as e:
                self.logger.warning(f"Failed to initialize vstd search engine: {e}")

    @classmethod
    def get_description(cls) -> str:
        return "Some proof requires an understanding of Seq/Set/Map/Vec/Multiset APIs, axioms, and available lemma functions."

    @classmethod
    def get_guidance_template(cls) -> str:
        return "This action is an expert in Verus data structure: Seq, Set, and Map."

    @classmethod
    def get_when_to_apply(cls) -> str:
        return "Apply when the asserted expression involves APIs of Seq/Set/Map."

    @classmethod
    def get_acceptance_criteria(cls) -> dict[str, Any]:
        """seq/set/map should reduce error count"""
        return {
            # TODO
            "criteria": AcceptanceCriteria.ERROR_REDUCTION,
            "threshold": 0.0,
        }

    def execute(self, observation: Observation, params: dict[str, Any]) -> ActionResult:
        """Execute the seq/set/map action"""
        guidance = params.get("guidance", "")

        # Use self-contained repair implementation
        repaired_codes = self._compute(
            observation.code,
            observation.error,
            guidance=guidance,
            num=self.get_action_candidate_num(),
            temp=1.0,
        )

        return self._create_result(observation, ActionType.SEQSETMAP, repaired_codes, guidance)

    def _compute(
        self, code: str, verus_error, guidance: str = "", num: int = 5, temp: float = 1.0
    ) -> list[str]:
        """seq/set/map proof with dynamic vstd retrieval"""

        # Detect which data structures are involved
        data_structures = self._detect_data_structures(code, str(verus_error))

        # Get dynamic vstd content if available
        if self.vstd_engine and self.vstd_formatter and data_structures:
            instruction = self._build_dynamic_instruction(data_structures)
            self.logger.info(f"Using dynamic vstd content for: {data_structures}")
        else:
            # Fall back to static prompt
            instruction = load_prompt("seqsetmap")
            if not self.vstd_engine:
                self.logger.warning("vstd search not available, using static prompt")

        # Prepare assertion info
        error_trace = verus_error.trace[0]
        assertion_info = error_trace.get_text() + "\n"

        query = f"""Fix this failed assertion:

{assertion_info}

Target code:
```verus
{code}
```"""

        # Use the existing repair infrastructure
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

    def _detect_data_structures(self, code: str, error: str) -> list[str]:
        """Detect which data structures are involved in the code/error"""
        detected = []
        combined_text = code + " " + error

        # Check for each data structure type
        for ds in ["Seq", "Set", "Map", "Vec", "Multiset"]:
            # Look for type annotations, API calls, etc.
            patterns = [
                rf"\b{ds}<",  # Type annotation: Seq<int>
                rf"::{ds}\b",  # Qualified name: vstd::seq::Seq
                rf"\b{ds}::",  # API call: Seq::empty()
            ]
            if any(re.search(pattern, combined_text) for pattern in patterns):
                detected.append(ds)

        return detected

    def _build_dynamic_instruction(self, data_structures: list[str]) -> str:
        """Build instruction with dynamic vstd content for detected data structures"""

        # Get content for each detected data structure
        data_by_type = {}
        for ds in data_structures:
            try:
                content = self.vstd_engine.get_all_for_data_structure(ds)
                if content:
                    data_by_type[ds] = content
            except Exception as e:
                self.logger.warning(f"Failed to retrieve vstd content for {ds}: {e}")

        if not data_by_type:
            # No content retrieved, fall back to static
            return load_prompt("seqsetmap")

        # Format comprehensive instruction
        try:
            instruction = self.vstd_formatter.format_for_seqsetmap(
                data_by_type, include_bodies=False  # Don't include bodies for token efficiency
            )
            return instruction
        except Exception as e:
            self.logger.error(f"Failed to format vstd content: {e}")
            return load_prompt("seqsetmap")
