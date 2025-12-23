"""
Search Engine for vstd Library

Multi-modal search combining:
- Structured search (by data structure, operation, function type)
- Full-text search (term matching in signatures, ensures, requires)
- Optional semantic search (embeddings - future)
"""

import json
import logging
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class SearchQuery:
    """Represents a search query"""

    query: str
    purpose: str = ""
    type: str = "any"  # "lemma" | "axiom" | "open_spec" | "example" | "any"
    filters: dict[str, any] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, data: dict) -> "SearchQuery":
        """Create SearchQuery from dictionary"""
        return cls(
            query=data.get("query", ""),
            purpose=data.get("purpose", ""),
            type=data.get("type", "any"),
            filters=data.get("filters", {}),
        )


@dataclass
class SearchResult:
    """Result from vstd search"""

    type: str  # "function" | "open_spec"
    name: str
    content: dict
    score: float
    match_reason: str

    def __repr__(self):
        return f"SearchResult({self.name}, score={self.score:.2f}, reason={self.match_reason})"


class VstdSearchEngine:
    """Multi-modal search engine for vstd library"""

    # Function types to INCLUDE in search results
    # Only proof functions (lemma_xyz) are included as main examples
    # Axioms and specs will be included in context if called by proofs
    ALLOWED_FUNCTION_TYPES = {"proof", "broadcast_proof"}

    # Data structures for which we keep open specs
    DATA_STRUCTURES = {"Seq", "Set", "Map", "Vec", "Multiset"}

    def __init__(self, index_path: str):
        """Initialize search engine

        Args:
            index_path: Path to vstd_index.json
        """
        self.logger = logging.getLogger(__name__)
        self.index_path = Path(index_path)
        self.index = None

        # Load index
        self._load_index()

    def _load_index(self):
        """Load index from file"""
        if not self.index_path.exists():
            raise FileNotFoundError(f"Index not found: {self.index_path}")

        with open(self.index_path, encoding="utf-8") as f:
            data = json.load(f)
            self.index = data["index"]

        self.logger.info(f"Loaded index with {len(self.index['functions'])} functions")

    def _should_include_function(self, func: dict) -> bool:
        """Check if a function should be included in search results

        Only includes:
        - proof/broadcast_proof functions
        - axiom/broadcast_axiom functions
        - exec functions

        Excludes:
        - closed_spec functions
        - uninterp_spec functions
        - open_spec functions (these are in a separate index)

        Args:
            func: Function dictionary

        Returns:
            True if function should be included
        """
        func_type = func.get("type", "")
        return func_type in self.ALLOWED_FUNCTION_TYPES

    def _should_include_open_spec(self, spec: dict) -> bool:
        """Check if an open spec should be included in search results

        Only includes open specs for data structures (Seq, Set, Map, Vec, Multiset)

        Args:
            spec: Open spec dictionary

        Returns:
            True if spec should be included
        """
        # Check if it's related to a data structure
        module = spec.get("module", "")
        name = spec.get("name", "")

        # Check module path or function name
        for ds in self.DATA_STRUCTURES:
            if ds.lower() in module.lower() or ds.lower() in name.lower():
                return True

        return False

    def search(self, query: SearchQuery, top_k: int = 10) -> list[SearchResult]:
        """Execute a search query using multiple strategies

        Args:
            query: SearchQuery object
            top_k: Maximum number of results to return

        Returns:
            List of SearchResult objects, ranked by relevance
        """
        results = []

        # Strategy 1: Structured filter search
        if query.filters:
            structured_results = self._structured_search(query.filters)
            results.extend(structured_results)
            self.logger.debug(f"Structured search: {len(structured_results)} results")

        # Strategy 2: Full-text search
        if query.query:
            fulltext_results = self._fulltext_search(query.query)
            results.extend(fulltext_results)
            self.logger.debug(f"Fulltext search: {len(fulltext_results)} results")

        # Deduplicate and rank
        results = self._deduplicate_and_rank(results, query)

        # Filter by query type if specified
        if query.type != "any":
            results = self._filter_by_type(results, query.type)

        return results[:top_k]

    def _structured_search(self, filters: dict) -> list[SearchResult]:
        """Search using structured filters

        Filters:
        - data_structure: "Seq" | "Set" | "Map" | ...
        - operations: ["take", "len", ...]
        - function_type: "proof" | "axiom" | ...
        """
        candidates = set()

        # Filter by data structure
        if "data_structure" in filters:
            ds = filters["data_structure"]
            if ds in self.index["by_type"]:
                candidates.update(self.index["by_type"][ds]["functions"])
                # Note: open_specs are indexed separately

        # Filter by operations (keywords)
        if "operations" in filters:
            for op in filters["operations"]:
                if op in self.index["by_keyword"]:
                    candidates.update(self.index["by_keyword"][op])

        # Convert to SearchResult objects (with filtering)
        results = []
        for func_name in candidates:
            if func_name in self.index["functions"]:
                func = self.index["functions"][func_name]
                # Filter: only include allowed function types
                if not self._should_include_function(func):
                    continue
                results.append(
                    SearchResult(
                        type="function",
                        name=func_name,
                        content=func,
                        score=1.0,
                        match_reason="structured_filter",
                    )
                )

        return results

    def _fulltext_search(self, query: str) -> list[SearchResult]:
        """Full-text search in signatures, ensures, requires

        Args:
            query: Search query string

        Returns:
            List of SearchResult objects
        """
        query_terms = self._extract_search_terms(query)
        results = []

        # Search in functions (with filtering)
        for func_name, func in self.index["functions"].items():
            # Filter: only include allowed function types
            if not self._should_include_function(func):
                continue

            score, matched_terms = self._score_function(func, query_terms)

            if score > 0:
                results.append(
                    SearchResult(
                        type="function",
                        name=func_name,
                        content=func,
                        score=score,
                        match_reason=f"matched {len(matched_terms)}/{len(query_terms)} terms: {', '.join(list(matched_terms)[:3])}",
                    )
                )

        # Skip open specs entirely - user only wants proof/axiom/exec functions
        # Open specs like spec_index, spec_le are just trivial wrappers with no learning value

        return results

    def _extract_search_terms(self, query: str) -> list[str]:
        """Extract search terms from query

        - Converts to lowercase
        - Splits on whitespace
        - Filters out common words
        """
        # Common stop words to ignore
        stop_words = {"a", "an", "the", "is", "are", "be", "of", "in", "to", "for", "and", "or"}

        # Split and clean
        terms = query.lower().split()
        terms = [t.strip() for t in terms if t.strip() and t not in stop_words]

        return terms

    def _score_function(self, func: dict, query_terms: list[str]) -> tuple[float, set[str]]:
        """Score a function against query terms

        Returns:
            (score, matched_terms)
        """
        # Build searchable text
        searchable = " ".join(
            [
                func.get("name", ""),
                func.get("signature", ""),
                " ".join(func.get("ensures", [])),
                " ".join(func.get("requires", [])),
                func.get("doc_comment", "") or "",
                " ".join(func.get("keywords", [])),
            ]
        ).lower()

        # Count matches
        matched_terms = set()
        for term in query_terms:
            if term in searchable:
                matched_terms.add(term)

        if not matched_terms:
            return 0.0, set()

        # Calculate score
        # Base score: proportion of terms matched
        base_score = len(matched_terms) / len(query_terms)

        # Bonus for name matches (highly relevant)
        name = func.get("name", "").lower()
        name_matches = sum(1 for term in matched_terms if term in name)
        if name_matches > 0:
            base_score *= 1.5**name_matches

        # Bonus for doc comment matches
        doc = (func.get("doc_comment", "") or "").lower()
        doc_matches = sum(1 for term in matched_terms if term in doc)
        if doc_matches > 0:
            base_score *= 1.2

        return base_score, matched_terms

    def _score_open_spec(self, spec: dict, query_terms: list[str]) -> tuple[float, set[str]]:
        """Score an open spec against query terms"""
        searchable = " ".join(
            [
                spec.get("name", ""),
                spec.get("signature", ""),
                spec.get("body", "") or "",
                " ".join(spec.get("keywords", [])),
            ]
        ).lower()

        matched_terms = set()
        for term in query_terms:
            if term in searchable:
                matched_terms.add(term)

        if not matched_terms:
            return 0.0, set()

        base_score = len(matched_terms) / len(query_terms)

        # Bonus for name matches
        name = spec.get("name", "").lower()
        if any(term in name for term in matched_terms):
            base_score *= 1.5

        return base_score, matched_terms

    def _deduplicate_and_rank(
        self, results: list[SearchResult], query: SearchQuery
    ) -> list[SearchResult]:
        """Remove duplicates and rank by combined score"""

        # Group by name, keep highest score
        by_name = {}
        for result in results:
            if result.name not in by_name:
                by_name[result.name] = result
            else:
                # Keep the one with higher score
                if result.score > by_name[result.name].score:
                    by_name[result.name] = result

        # Boost scores based on query type preference
        for result in by_name.values():
            result.score = self._apply_type_boost(result, query)
            result.score = self._apply_module_boost(result)

        # Sort by score descending
        ranked = sorted(by_name.values(), key=lambda r: r.score, reverse=True)

        return ranked

    def _apply_type_boost(self, result: SearchResult, query: SearchQuery) -> float:
        """Apply boost based on query type preference"""
        score = result.score
        func = result.content
        func_type = func.get("type", "")

        if query.type == "lemma" and func_type == "proof":
            score *= 1.5
        elif query.type == "axiom" and "axiom" in func_type:
            score *= 1.5
        elif query.type == "example" and func.get("body"):
            # Examples should have bodies
            score *= 1.3
        elif query.type == "open_spec" and result.type == "open_spec":
            score *= 1.5
        elif query.type == "closed_spec" and func_type == "closed_spec":
            score *= 1.5
        elif query.type == "uninterp_spec" and func_type == "uninterp_spec":
            score *= 1.5

        return score

    def _apply_module_boost(self, result: SearchResult) -> float:
        """Apply boost for popular/important modules"""
        score = result.score
        module = result.content.get("module", "")

        # Boost core library modules
        core_modules = [
            "vstd::seq_lib",
            "vstd::set_lib",
            "vstd::map_lib",
            "vstd::seq",
            "vstd::set",
            "vstd::map",
        ]

        if module in core_modules:
            score *= 1.2

        return score

    def _filter_by_type(self, results: list[SearchResult], query_type: str) -> list[SearchResult]:
        """Filter results by type"""
        if query_type == "any":
            return results

        filtered = []
        for result in results:
            func_type = result.content.get("type", "")

            if query_type == "lemma" and func_type in ["proof", "broadcast_proof"]:
                filtered.append(result)
            elif query_type == "axiom" and "axiom" in func_type:
                filtered.append(result)
            elif query_type == "open_spec" and result.type == "open_spec":
                filtered.append(result)
            elif query_type == "closed_spec" and func_type == "closed_spec":
                filtered.append(result)
            elif query_type == "uninterp_spec" and func_type == "uninterp_spec":
                filtered.append(result)
            elif query_type == "example":
                # Examples should have bodies
                if result.content.get("body"):
                    filtered.append(result)

        return filtered

    # Convenience methods for common searches

    def search_by_data_structure(self, data_structure: str, top_k: int = 20) -> list[SearchResult]:
        """Get all functions and specs for a data structure

        Args:
            data_structure: "Seq", "Set", "Map", etc.
            top_k: Maximum results

        Returns:
            List of SearchResult objects
        """
        query = SearchQuery(query=data_structure, filters={"data_structure": data_structure})
        return self.search(query, top_k=top_k)

    def get_all_for_data_structure(self, data_structure: str) -> dict[str, list[dict]]:
        """Get ALL content for a data structure (for seqsetmap action)

        Returns:
            {
                "open_specs": List[spec_dict],
                "axioms": List[func_dict],
                "lemmas": List[func_dict]
            }
        """
        result = {"open_specs": [], "axioms": [], "lemmas": []}

        # Get open specs
        if data_structure in self.index["by_type"]:
            spec_names = self.index["by_type"][data_structure]["open_specs"]
            for name in spec_names:
                if name in self.index["open_specs"]:
                    result["open_specs"].append(self.index["open_specs"][name])

        # Get functions
        if data_structure in self.index["by_type"]:
            func_names = self.index["by_type"][data_structure]["functions"]
            for name in func_names:
                if name in self.index["functions"]:
                    func = self.index["functions"][name]
                    func_type = func.get("type", "")

                    # Categorize by type
                    if "axiom" in func_type:
                        result["axioms"].append(func)
                    elif func_type in ["proof", "broadcast_proof"]:
                        result["lemmas"].append(func)

        return result

    def get_function(self, name: str) -> dict | None:
        """Get function by name"""
        return self.index["functions"].get(name)

    def get_open_spec(self, name: str) -> dict | None:
        """Get open spec by name"""
        return self.index["open_specs"].get(name)


def main():
    """Test search engine"""
    import sys

    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python search_engine.py <query>")
        print("Example: python search_engine.py 'Seq take length'")
        return

    # Load index
    index_path = Path(__file__).parent / "vstd_index.json"
    if not index_path.exists():
        print(f"Error: Index not found at {index_path}")
        print("Run: python -m vstd_library.build_index")
        return

    engine = VstdSearchEngine(str(index_path))

    # Search
    query_text = " ".join(sys.argv[1:])
    query = SearchQuery(query=query_text)

    print(f"\n{'='*70}")
    print(f"Search Query: '{query_text}'")
    print(f"{'='*70}\n")

    results = engine.search(query, top_k=10)

    if not results:
        print("No results found.")
        return

    print(f"Found {len(results)} results:\n")

    for i, result in enumerate(results, 1):
        print(f"{i}. {result.name} (score: {result.score:.2f})")
        print(f"   Type: {result.content.get('type', 'unknown')}")
        print(f"   Module: {result.content.get('module', 'unknown')}")
        print(f"   Match: {result.match_reason}")

        if result.content.get("doc_comment"):
            doc = result.content["doc_comment"]
            preview = doc[:100] + "..." if len(doc) > 100 else doc
            print(f"   Doc: {preview}")

        print()


if __name__ == "__main__":
    main()
