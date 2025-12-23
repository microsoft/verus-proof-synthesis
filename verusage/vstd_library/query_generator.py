"""
Query Generator for vstd Search

Uses LLM to analyze errors and generate search queries for vstd library content.
"""

import json
import logging

from .search_engine import SearchQuery


class QueryGenerator:
    """Generates search queries from error context using LLM"""

    def __init__(self, llm, config):
        """Initialize query generator

        Args:
            llm: LLM instance (from global_config)
            config: Configuration dict
        """
        self.llm = llm
        self.config = config
        self.logger = logging.getLogger(__name__)

    def generate_queries(
        self, error_context: str, code: str, surrounding_context: str = ""
    ) -> list[SearchQuery]:
        """Generate search queries based on error analysis

        Args:
            error_context: Error message and location
            code: Full code
            surrounding_context: Code surrounding error

        Returns:
            List of SearchQuery objects
        """
        # Build analysis prompt
        analysis_prompt = self._build_analysis_prompt(error_context, code, surrounding_context)

        # Call LLM
        try:
            responses = self.llm.infer_llm(
                engine=self.config.aoai_debug_model,
                instruction=self._get_system_instruction(),
                exemplars=[],
                query=analysis_prompt,
                system_info="You are a Verus expert. Output valid JSON only.",
                answer_num=1,
                max_tokens=2048,
            )

            if not responses:
                self.logger.warning("No response from LLM for query generation")
                return []

            # Parse JSON response
            queries = self._parse_llm_response(responses[0])
            self.logger.info(f"Generated {len(queries)} search queries")

            print(queries)

            return queries

        except Exception as e:
            self.logger.error(f"Failed to generate queries: {e}")
            # Fallback: generate simple queries based on keywords
            return self._fallback_queries(error_context, code)

    def _build_analysis_prompt(
        self, error_context: str, code: str, surrounding_context: str
    ) -> str:
        """Build prompt for LLM analysis"""

        prompt = f"""You are analyzing a Verus verification error to determine what knowledge
from the vstd library would be helpful for fixing it.

## Error Information
{error_context}

## Code Context
```rust
{surrounding_context if surrounding_context else code[:500]}
```

## Your Task
Analyze this error and generate 2-5 search queries to find relevant vstd library content.

Output a JSON object with this structure:
{{
  "data_structures_involved": ["Seq", "Set", "Map", ...],
  "operations_involved": ["take", "len", "push", ...],
  "proof_concepts_needed": ["forall instantiation", "trigger patterns", ...],
  "search_queries": [
    {{
      "query": "Seq take length relationship",
      "purpose": "Find lemmas/axioms relating Seq::take to length",
      "type": "lemma",
      "filters": {{
        "data_structure": "Seq",
        "operations": ["take", "len"]
      }}
    }},
    {{
      "query": "proof examples with Seq bounds",
      "purpose": "See how to prove properties with index constraints",
      "type": "example"
    }}
  ]
}}

Guidelines:
- Be specific in your queries
- Focus on the actual error, not general concepts
- Query type can be: "lemma", "axiom", "open_spec", "example", or "any"
- Include filters when you know specific data structures or operations
- Generate 2-5 queries (more specific is better than general)

Output ONLY the JSON object, no other text.
"""

        return prompt

    def _get_system_instruction(self) -> str:
        """Get system instruction for LLM"""
        return """You are a Verus verification expert helping to find relevant vstd library content.
Your task is to analyze errors and generate precise search queries."""

    def _parse_llm_response(self, response: str) -> list[SearchQuery]:
        """Parse LLM JSON response into SearchQuery objects"""

        # Try to extract JSON from response
        response = response.strip()

        # Sometimes LLM wraps in markdown code blocks
        if response.startswith("```json"):
            response = response.split("```json")[1].split("```")[0].strip()
        elif response.startswith("```"):
            response = response.split("```")[1].split("```")[0].strip()

        try:
            data = json.loads(response)
        except json.JSONDecodeError as e:
            self.logger.error(f"Failed to parse JSON response: {e}")
            self.logger.debug(f"Response was: {response[:200]}")
            return []

        # Extract search queries
        queries = []
        for q in data.get("search_queries", []):
            try:
                query = SearchQuery.from_dict(q)
                queries.append(query)
            except Exception as e:
                self.logger.warning(f"Failed to parse query: {e}")
                continue

        return queries

    def _fallback_queries(self, error_context: str, code: str) -> list[SearchQuery]:
        """Generate simple fallback queries based on keyword extraction

        This fallback handles ALL types of errors, not just data structures:
        - Arithmetic (division, modulo, multiplication)
        - Bit operations (shifts, bitwise and/or/xor)
        - Data structures (Seq, Set, Map, Vec, Multiset)
        - Quantifiers (forall, exists)
        - Recursion and fuel

        Args:
            error_context: Error message
            code: Source code

        Returns:
            List of basic SearchQuery objects
        """
        queries = []
        combined = (error_context + " " + code).lower()

        # Detect data structures
        data_structures = []
        for ds in ["Seq", "Set", "Map", "Vec", "Multiset", "Array"]:
            if ds in error_context or ds in code:
                data_structures.append(ds)

        # Detect collection operations
        operations = []
        operation_keywords = [
            "take",
            "push",
            "len",
            "insert",
            "remove",
            "contains",
            "subrange",
            "union",
            "intersect",
            "filter",
            "index",
        ]
        for op in operation_keywords:
            if op in combined:
                operations.append(op)

        # Detect arithmetic operations
        arithmetic_ops = []
        if any(x in combined for x in ["div", "division", "/"]):
            arithmetic_ops.append("division")
        if any(x in combined for x in ["mod", "modulo", "%"]):
            arithmetic_ops.append("modulo")
        if any(x in combined for x in ["mul", "multiply", "*"]):
            arithmetic_ops.append("multiplication")
        if any(x in combined for x in ["pow", "power", "exponent"]):
            arithmetic_ops.append("power")

        # Detect bit operations
        bit_ops = []
        if any(x in combined for x in ["<<", ">>", "shift"]):
            bit_ops.append("shift")
        if any(x in combined for x in ["&", "bitwise and"]):
            bit_ops.append("bitwise and")
        if any(x in combined for x in ["|", "bitwise or"]):
            bit_ops.append("bitwise or")
        if any(x in combined for x in ["^", "xor"]):
            bit_ops.append("xor")
        if "leading_zeros" in combined or "trailing_zeros" in combined:
            bit_ops.append("count zeros")

        # Detect quantifiers
        has_forall = "forall" in combined
        has_exists = "exists" in combined

        # Generate queries for data structures
        for ds in data_structures[:2]:
            query = SearchQuery(
                query=f"{ds} {' '.join(operations[:2])}",
                purpose=f"Find {ds} functions related to error",
                type="any",
                filters={"data_structure": ds, "operations": operations[:3]},
            )
            queries.append(query)

        # Generate queries for arithmetic
        if arithmetic_ops:
            query = SearchQuery(
                query=f"arithmetic {' '.join(arithmetic_ops[:2])}",
                purpose="Find arithmetic lemmas and axioms",
                type="lemma",
            )
            queries.append(query)

        # Generate queries for bit operations
        if bit_ops:
            query = SearchQuery(
                query=f"bit operations {' '.join(bit_ops[:2])}",
                purpose="Find bit vector reasoning functions",
                type="any",
            )
            queries.append(query)

        # Generate queries for quantifiers
        if has_forall or has_exists:
            query = SearchQuery(
                query="quantifier instantiation trigger",
                purpose="Find examples of quantifier handling",
                type="example",
            )
            queries.append(query)

        # Add a general query if we have operations
        if operations and not data_structures:
            query = SearchQuery(
                query=" ".join(operations[:3]),
                purpose="Find functions for operations mentioned in error",
                type="lemma",
            )
            queries.append(query)

        # If no specific patterns found, do a very general search
        if not queries:
            # Extract key terms from error message
            error_terms = [w for w in error_context.lower().split() if len(w) > 4 and w.isalpha()][
                :3
            ]
            if error_terms:
                query = SearchQuery(
                    query=" ".join(error_terms),
                    purpose="General search based on error message",
                    type="any",
                )
                queries.append(query)

        self.logger.info(f"Generated {len(queries)} fallback queries")
        return queries


def main():
    """Test query generator (requires LLM setup)"""

    logging.basicConfig(level=logging.INFO)

    print("Query Generator Test")
    print("=" * 70)
    print("Note: This requires LLM setup. Testing fallback mode only.\n")

    # Create a dummy query generator without LLM
    class DummyLLM:
        pass

    class DummyConfig:
        aoai_debug_model = "test"

    generator = QueryGenerator(DummyLLM(), DummyConfig())

    # Test fallback queries
    error_context = "assertion failed: s.take(i).len() == i"
    code = """
    fn test(s: Seq<int>, i: int) {
        requires(0 <= i <= s.len());
        assert(s.take(i).len() == i);
    }
    """

    queries = generator._fallback_queries(error_context, code)

    print(f"Generated {len(queries)} fallback queries:\n")
    for i, q in enumerate(queries, 1):
        print(f"{i}. Query: '{q.query}'")
        print(f"   Purpose: {q.purpose}")
        print(f"   Type: {q.type}")
        print(f"   Filters: {q.filters}")
        print()


if __name__ == "__main__":
    main()
