"""
Result Formatter for vstd Search

Formats search results for LLM consumption in different contexts:
- Reasoning phase examples
- seqsetmap action comprehensive reference
"""

import logging

from .search_engine import SearchResult


class ResultFormatter:
    """Formats search results for LLM consumption"""

    def __init__(self, search_engine=None):
        """Initialize formatter

        Args:
            search_engine: Optional VstdSearchEngine to look up context functions
        """
        self.logger = logging.getLogger(__name__)
        self.search_engine = search_engine

    def format_for_reasoning(self, results: list[SearchResult], max_results: int = 3) -> str:
        """Format results as examples for reasoning phase

        Shows doc comment + signature + body for each example.
        Also includes context: helper lemmas/specs called by the main function.

        Args:
            results: List of SearchResult objects
            max_results: Maximum number of results to include

        Returns:
            Formatted string for LLM prompt
        """
        if not results:
            return ""

        formatted = "## Relevant vstd Library Examples\n\n"

        for i, result in enumerate(results[:max_results], 1):
            func = result.content

            # Function name
            formatted += f"### Example {i}: {func['name']}\n\n"

            # Add doc comment if available
            if func.get("doc_comment"):
                doc = func["doc_comment"].strip()
                formatted += f"{doc}\n\n"

            # Main function: Signature + body
            formatted += "```rust\n"

            # The signature field already contains requires/ensures
            signature = func.get("signature", "")
            if signature:
                formatted += signature

            # Add body if available (skip for axioms - they're just declarations)
            func_type = func.get("type", "")
            func_name = func.get("name", "")
            # Check both type and name pattern
            is_axiom = func_type in {"axiom", "broadcast_axiom"} or func_name.startswith("axiom_")

            body = func.get("body", "")
            if body and not is_axiom:
                # Remove trailing comma from signature if present
                if formatted.endswith(","):
                    formatted = formatted.rstrip(",")
                formatted += "\n" + body

            formatted += "\n```\n\n"

        # After formatting all examples, extract context from ALL examples
        # Collect unique callees across all examples (that are proof/spec functions)
        if self.search_engine:
            all_context_funcs = self._extract_all_context_functions(
                [r.content for r in results[:max_results]]
            )

            if all_context_funcs:
                formatted += "**Context (helper functions used across examples):**\n\n"
                formatted += "```rust\n"
                max_context_examples = min(2 * max_results, len(all_context_funcs))
                for ctx_func in all_context_funcs[
                    :max_context_examples
                ]:  # Limit to 5 total context functions
                    formatted += self._format_context_function(ctx_func)
                    formatted += "\n\n"
                formatted += "```\n\n"

        return formatted

    def _extract_all_context_functions(self, funcs: list[dict]) -> list[dict]:
        """Extract unique context functions from multiple examples

        Collects callees from all example functions and deduplicates.
        Only includes proof/axiom/spec functions (not exec).

        Args:
            funcs: List of function dictionaries

        Returns:
            List of unique context function dictionaries
        """
        if not self.search_engine:
            return []

        all_callees = set()
        exclude_names = set()

        # Collect all callees and names to exclude
        for func in funcs:
            func_name = func.get("name")
            if func_name:
                exclude_names.add(func_name)

            callees = func.get("callees", [])
            all_callees.update(callees)

        # Look up each unique callee
        # Separate proof functions from specs for prioritization
        proof_functions = []
        spec_functions = []
        seen_names = set()

        # Helper function to check if two names refer to the same function
        def is_same_function(name1: str, name2: str) -> bool:
            if name1 == name2:
                return True
            if name1.endswith("::" + name2) or name2.endswith("::" + name1):
                return True
            short1 = name1.split("::")[-1]
            short2 = name2.split("::")[-1]
            return short1 == short2

        if hasattr(self.search_engine, "index"):
            # Sort callees for deterministic ordering
            for callee_name in sorted(all_callees):
                # Try exact match
                if callee_name in self.search_engine.index.get("functions", {}):
                    called_func = self.search_engine.index["functions"][callee_name]
                    full_name = called_func.get("name", callee_name)
                    func_type = called_func.get("type", "")

                    # Skip if it's one of the example functions
                    if any(is_same_function(full_name, ex_name) for ex_name in exclude_names):
                        continue

                    # Skip duplicates
                    if full_name in seen_names:
                        continue

                    # Only include proof/axiom/spec functions (not exec)
                    # Prioritize proof/axiom functions over specs
                    if func_type in {"proof", "broadcast_proof", "axiom", "broadcast_axiom"}:
                        proof_functions.append(called_func)
                        seen_names.add(full_name)
                    elif func_type in {"closed_spec", "open_spec", "uninterp_spec"}:
                        spec_functions.append(called_func)
                        seen_names.add(full_name)
                else:
                    # Try partial match
                    for full_name, called_func in self.search_engine.index.get(
                        "functions", {}
                    ).items():
                        if (
                            full_name.endswith("::" + callee_name)
                            or full_name.split("::")[-1] == callee_name
                        ):
                            func_type = called_func.get("type", "")

                            # Skip if it's one of the example functions
                            if any(
                                is_same_function(full_name, ex_name) for ex_name in exclude_names
                            ):
                                continue

                            # Skip duplicates
                            if full_name in seen_names:
                                continue

                            # Only include proof/axiom/spec functions (not exec)
                            # Prioritize proof/axiom functions over specs
                            if func_type in {
                                "proof",
                                "broadcast_proof",
                                "axiom",
                                "broadcast_axiom",
                            }:
                                proof_functions.append(called_func)
                                seen_names.add(full_name)
                                break
                            elif func_type in {"closed_spec", "open_spec", "uninterp_spec"}:
                                spec_functions.append(called_func)
                                seen_names.add(full_name)
                                break

        # Return proof/axiom functions first, then specs
        # This ensures proof examples are prioritized in the limited context window
        return proof_functions + spec_functions

    def _extract_context_functions(self, func: dict, exclude_name: str = None) -> list[dict]:
        """Extract helper functions called by this function

        Uses pre-built callees from the index for efficiency.

        Args:
            func: Function dictionary with callees list
            exclude_name: Function name to exclude from context (avoid duplicates)

        Returns:
            List of function dictionaries for called helpers
        """
        if not self.search_engine:
            return []

        context = []
        seen_names = set()

        # Get callees from the pre-built index
        callees = func.get("callees", [])

        # Helper function to check if two names refer to the same function
        def is_same_function(name1: str, name2: str) -> bool:
            """Check if two function names refer to the same function"""
            if name1 == name2:
                return True
            # Check if one is a short name and the other is a full path
            # e.g., "max_ensures" vs "vstd::seq::max_ensures"
            if name1.endswith("::" + name2) or name2.endswith("::" + name1):
                return True
            # Get the last component of both names
            short1 = name1.split("::")[-1]
            short2 = name2.split("::")[-1]
            return short1 == short2

        # Look up each callee in the index
        if hasattr(self.search_engine, "index"):
            for callee_name in callees:
                # Try exact match first
                if callee_name in self.search_engine.index.get("functions", {}):
                    called_func = self.search_engine.index["functions"][callee_name]
                    full_name = called_func.get("name", callee_name)

                    # Skip if it's the same as the main function (with smart matching)
                    if exclude_name and is_same_function(full_name, exclude_name):
                        continue

                    # Skip duplicates
                    if full_name in seen_names:
                        continue

                    # Only include if it's an allowed type
                    if self.search_engine._should_include_function(called_func):
                        context.append(called_func)
                        seen_names.add(full_name)
                else:
                    # Try partial match (callee might be short name like "lemma_foo")
                    for full_name, called_func in self.search_engine.index.get(
                        "functions", {}
                    ).items():
                        if (
                            full_name.endswith("::" + callee_name)
                            or full_name.split("::")[-1] == callee_name
                        ):
                            # Skip if it's the same as the main function (with smart matching)
                            if exclude_name and is_same_function(full_name, exclude_name):
                                continue

                            # Skip duplicates
                            if full_name in seen_names:
                                continue

                            if self.search_engine._should_include_function(called_func):
                                context.append(called_func)
                                seen_names.add(full_name)
                                break

        return context

    def _format_context_function(self, func: dict) -> str:
        """Format a context function (compact version)

        Args:
            func: Function dictionary

        Returns:
            Formatted string
        """
        lines = []

        # Add comment with function name
        lines.append(f"// {func.get('name', 'unknown')}")

        # Signature
        signature = func.get("signature", "")
        if signature:
            lines.append(signature)

        # Body (skip for axioms - they're just declarations)
        func_type = func.get("type", "")
        func_name = func.get("name", "")
        # Check both type and name pattern
        is_axiom = func_type in {"axiom", "broadcast_axiom"} or func_name.startswith("axiom_")

        if not is_axiom:
            body = func.get("body", "")
            if body:
                # Show full body, no truncation
                lines.append(body)

        return "\n".join(lines)

    def format_for_seqsetmap(
        self, data_by_type: dict[str, dict], include_bodies: bool = False
    ) -> str:
        """Format comprehensive results for seqsetmap action

        Args:
            data_by_type: Dict mapping data_structure -> {open_specs, axioms, lemmas}
            include_bodies: Whether to include function bodies

        Returns:
            Formatted instruction string
        """
        instruction = """This document contains vstd library knowledge about data structures.

In Verus, EVERY proof involving these data structures should be based on:
1) Open spec functions (if that API has an open spec)
2) Axioms

The properties implied by these axioms and open specs are the ONLY knowledge
the prover knows about these data structures. You should construct your proof
so that the conclusion can be reached based on the spec functions and axioms
listed below.

Additionally, lemma functions are available that you can call in your proof.
After calling a lemma function, add assert statements to indicate what
properties are ensured by the lemma.

Note:
- Axiom functions are already known by Verus; do NOT call them
- If an axiom has a precondition, it must hold for the postcondition to apply
- Pay attention to #[trigger] tags - matching expressions must appear for axioms to activate

"""

        for data_structure, content in data_by_type.items():
            instruction += f"\n{'='*70}\n"
            instruction += f"## {data_structure}\n"
            instruction += f"{'='*70}\n\n"

            # Part 1: Open Spec Functions
            if content.get("open_specs"):
                instruction += f"### Part 1: Open Spec Functions of {data_structure}\n\n"
                instruction += "```rust\n"
                for spec in content["open_specs"][:20]:  # Limit to 20
                    instruction += self._format_open_spec(spec)
                    instruction += "\n\n"
                instruction += "```\n\n"

            # Part 2: Axioms
            if content.get("axioms"):
                instruction += f"### Part 2: Axioms about {data_structure}\n\n"
                instruction += "**Do NOT call these - they are automatically known by Verus.**\n\n"
                instruction += "```rust\n"
                for axiom in content["axioms"][:30]:  # Limit to 30
                    instruction += self._format_function_signature(axiom)
                    instruction += "\n\n"
                instruction += "```\n\n"

            # Part 3: Lemma Functions
            if content.get("lemmas"):
                instruction += (
                    f"### Part 3: Lemma Functions from vstd::{data_structure.lower()}_lib\n\n"
                )
                instruction += "**You can call these in your proof.**\n\n"
                instruction += "```rust\n"
                for lemma in content["lemmas"][:40]:  # Limit to 40
                    instruction += self._format_function_signature(
                        lemma, include_body=include_bodies
                    )
                    instruction += "\n\n"
                instruction += "```\n\n"

        return instruction

    def _format_function_signature(self, func: dict, include_body: bool = False) -> str:
        """Format a function signature with requires/ensures

        Args:
            func: Function dictionary
            include_body: Whether to include function body

        Returns:
            Formatted function string
        """
        lines = []

        # Function signature
        sig = func.get("signature", "")
        # Clean up signature (remove extra whitespace)
        sig = " ".join(sig.split())
        lines.append(sig)

        # Requires clauses
        requires = func.get("requires", [])
        if requires:
            lines.append("    requires")
            for req in requires:
                lines.append(f"        {req},")

        # Ensures clauses
        ensures = func.get("ensures", [])
        if ensures:
            lines.append("    ensures")
            for ens in ensures:
                lines.append(f"        {ens},")

        # Body (if requested and available)
        if include_body and func.get("body"):
            body = func["body"]
            # Limit body size
            if len(body) < 500:
                lines.append(body)

        return "\n".join(lines)

    def _format_open_spec(self, spec: dict) -> str:
        """Format an open spec function

        Args:
            spec: Open spec dictionary

        Returns:
            Formatted spec string
        """
        lines = []

        # Signature
        sig = spec.get("signature", "")
        sig = " ".join(sig.split())
        lines.append(sig)

        # Body (if reasonable size)
        body = spec.get("body", "")
        if body and len(body) < 300:
            lines.append(body)

        return "\n".join(lines)

    def _infer_proof_technique(self, func: dict) -> str:
        """Infer what proof technique this function demonstrates

        Args:
            func: Function dictionary

        Returns:
            Description string
        """
        ensures = " ".join(func.get("ensures", []))
        body = func.get("body", "") or ""

        if "forall" in ensures:
            return "quantifier instantiation with forall"
        elif "exists" in ensures:
            return "existential proof"
        elif "trigger" in ensures or func.get("triggers"):
            return "trigger pattern usage"
        elif "decreases" in func.get("signature", ""):
            return "inductive proof with decreases clause"
        elif func.get("type") == "broadcast_proof":
            return "broadcast lemma (automatically available)"
        elif "axiom" in func.get("type", ""):
            return "axiom about data structure properties"
        elif "assert" in body:
            return "proof with explicit assertions"
        else:
            # Try to extract main concept
            keywords = func.get("keywords", [])
            if keywords:
                return f"proof about {', '.join(keywords[:2])}"
            return "proof technique"

    def format_search_summary(self, results: list[SearchResult]) -> str:
        """Format a summary of search results

        Args:
            results: List of SearchResult objects

        Returns:
            Summary string
        """
        if not results:
            return "No results found."

        summary = f"Found {len(results)} results:\n"

        # Group by module
        by_module = {}
        for result in results:
            module = result.content.get("module", "unknown")
            if module not in by_module:
                by_module[module] = []
            by_module[module].append(result)

        # Format by module
        for module, module_results in sorted(by_module.items()):
            summary += f"\n{module}:\n"
            for result in module_results[:5]:  # Show top 5 per module
                summary += f"  - {result.name} ({result.content.get('type', 'unknown')})\n"

        return summary


def main():
    """Test result formatter"""
    import json
    from pathlib import Path

    logging.basicConfig(level=logging.INFO)

    # Load some sample results from index
    index_path = Path(__file__).parent / "vstd_index.json"
    if not index_path.exists():
        print("Error: Index not found. Run build_index.py first.")
        return

    with open(index_path) as f:
        data = json.load(f)

    # Get some sample functions
    functions = list(data["index"]["functions"].values())[:3]

    # Create fake SearchResult objects
    results = []
    for func in functions:
        from .search_engine import SearchResult

        result = SearchResult(
            type="function", name=func["name"], content=func, score=1.0, match_reason="sample"
        )
        results.append(result)

    # Test formatter
    formatter = ResultFormatter()

    print("=" * 70)
    print("Test: Format for Reasoning")
    print("=" * 70)
    formatted = formatter.format_for_reasoning(results)
    print(formatted)

    print("\n" + "=" * 70)
    print("Test: Search Summary")
    print("=" * 70)
    summary = formatter.format_search_summary(results)
    print(summary)


if __name__ == "__main__":
    main()
