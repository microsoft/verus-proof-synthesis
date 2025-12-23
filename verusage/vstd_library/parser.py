"""
Parser for Verus standard library (vstd) files

Extracts structured information from .rs files including:
- Function signatures and types (proof, spec, axiom, exec)
- Requires and ensures clauses
- Trigger patterns
- Documentation comments
- Function bodies
"""

import logging
import re
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class VstdFunction:
    """Represents a function/lemma/axiom from vstd"""

    name: str
    type: str  # "spec", "proof", "broadcast_proof", "broadcast_axiom", "exec"
    signature: str
    ensures: list[str] = field(default_factory=list)
    requires: list[str] = field(default_factory=list)
    body: str | None = None
    doc_comment: str | None = None
    triggers: list[str] = field(default_factory=list)
    file_path: str = ""
    line_number: int = 0
    module: str = ""
    keywords: list[str] = field(default_factory=list)
    callees: list[str] = field(default_factory=list)  # Functions this function calls

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization"""
        return {
            "name": self.name,
            "type": self.type,
            "signature": self.signature,
            "ensures": self.ensures,
            "requires": self.requires,
            "body": self.body,
            "doc_comment": self.doc_comment,
            "triggers": self.triggers,
            "file_path": self.file_path,
            "line_number": self.line_number,
            "module": self.module,
            "keywords": self.keywords,
            "callees": self.callees,
        }


@dataclass
class VstdOpenSpec:
    """Represents an open spec function definition"""

    name: str
    signature: str
    body: str
    file_path: str = ""
    line_number: int = 0
    module: str = ""
    keywords: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization"""
        return {
            "name": self.name,
            "signature": self.signature,
            "body": self.body,
            "file_path": self.file_path,
            "line_number": self.line_number,
            "module": self.module,
            "keywords": self.keywords,
        }


class VstdParser:
    """Parser for vstd library files"""

    def __init__(self):
        self.logger = logging.getLogger(__name__)

    def parse_file(self, file_path: Path) -> dict:
        """Parse a single vstd file

        Args:
            file_path: Path to .rs file

        Returns:
            {
                "functions": List[VstdFunction],
                "open_specs": List[VstdOpenSpec],
                "module": str
            }
        """
        self.logger.info(f"Parsing {file_path}")

        try:
            content = file_path.read_text(encoding="utf-8")
        except Exception as e:
            self.logger.error(f"Failed to read {file_path}: {e}")
            return {"functions": [], "open_specs": [], "module": ""}

        # Determine module name from path
        module = self._get_module_name(file_path)

        # Extract functions and specs
        functions = self._extract_functions(content, file_path, module)
        open_specs = self._extract_open_specs(content, file_path, module)

        return {"functions": functions, "open_specs": open_specs, "module": module}

    def parse_all_vstd(self, vstd_path: Path) -> list[dict]:
        """Parse all .rs files in vstd directory

        Args:
            vstd_path: Path to vstd directory

        Returns:
            List of parsed file data
        """
        all_files = []

        for rs_file in sorted(vstd_path.rglob("*.rs")):
            # Skip build.rs and test files
            if rs_file.name == "build.rs" or "test" in str(rs_file):
                continue

            parsed = self.parse_file(rs_file)
            if parsed["functions"] or parsed["open_specs"]:
                all_files.append(parsed)

        self.logger.info(f"Parsed {len(all_files)} files")
        return all_files

    def _get_module_name(self, file_path: Path) -> str:
        """Get module name from file path

        Example: /path/to/vstd/seq_lib.rs -> vstd::seq_lib
                 /path/to/vstd/arithmetic/div_mod.rs -> vstd::arithmetic::div_mod
        """
        # Find 'vstd' in path
        parts = file_path.parts
        try:
            vstd_idx = parts.index("vstd")
            # Get parts after 'vstd'
            module_parts = parts[vstd_idx:]
            # Remove .rs extension from last part
            module_parts = list(module_parts[:-1]) + [parts[-1].replace(".rs", "")]
            return "::".join(module_parts)
        except (ValueError, IndexError):
            return str(file_path.stem)

    def _extract_functions(self, content: str, file_path: Path, module: str) -> list[VstdFunction]:
        """Extract all functions from file content"""
        functions = []

        # Pattern to match function definitions
        # Matches: pub [broadcast] [proof|axiom|spec|exec|open spec|closed spec|uninterp spec] fn name...
        fn_pattern = re.compile(
            r"(?:^|\n)\s*((?:///[^\n]*\n\s*)*)"  # Optional doc comments (CAPTURED)
            r"(?:#\[[^\]]+\]\s*)*"  # Optional attributes
            r"pub\s+"
            r"(?:(broadcast)\s+)?"  # Optional broadcast
            r"(?:(proof|axiom|spec|exec|open\s+spec|closed\s+spec|uninterp\s+spec))\s+"
            r"fn\s+"
            r"(\w+)",  # Function name
            re.MULTILINE,
        )

        for match in fn_pattern.finditer(content):
            try:
                doc_comment_match = match.group(1)  # Captured doc comments
                broadcast = match.group(2)
                fn_kind = match.group(3)
                fn_name = match.group(4)
                start_pos = match.start()

                # Extract doc comment from matched text
                doc_comment = (
                    self._parse_doc_comment(doc_comment_match) if doc_comment_match else None
                )

                # Determine function type
                if broadcast and fn_kind in ["proof", "axiom"]:
                    fn_type = f"broadcast_{fn_kind}"
                elif fn_kind == "open spec":
                    continue  # Handle separately as open specs
                elif fn_kind == "closed spec":
                    fn_type = "closed_spec"
                elif fn_kind == "uninterp spec":
                    fn_type = "uninterp_spec"
                else:
                    fn_type = fn_kind

                # Extract the complete function
                func = self._extract_complete_function(
                    content, start_pos, fn_name, fn_type, file_path, module, doc_comment
                )

                if func:
                    functions.append(func)

            except Exception as e:
                self.logger.warning(f"Failed to parse function near {fn_name}: {e}")
                continue

        return functions

    def _extract_complete_function(
        self,
        content: str,
        start_pos: int,
        fn_name: str,
        fn_type: str,
        file_path: Path,
        module: str,
        doc_comment: str | None = None,
    ) -> VstdFunction | None:
        """Extract complete function including signature, requires, ensures, body"""

        remaining = content[start_pos:]

        # Find the end of this function (either at { or ; or next fn)
        # We need to limit our search scope to just this function
        function_scope = self._extract_function_scope(remaining)
        if not function_scope:
            return None

        # Find signature (from pub to { or ;)
        sig_match = re.search(r"pub\s+.*?fn\s+" + re.escape(fn_name) + r"[^{;]*", function_scope)
        if not sig_match:
            return None

        signature = sig_match.group(0).strip()

        # Extract requires clauses (only from this function's scope)
        requires = self._extract_clauses(function_scope, "requires")

        # Extract ensures clauses (only from this function's scope)
        ensures = self._extract_clauses(function_scope, "ensures")

        # Extract triggers from ensures
        triggers = self._extract_triggers(ensures)

        # Extract function body (if it has one)
        body = self._extract_body(function_scope)

        # Extract keywords from signature and clauses
        keywords = self._extract_keywords(signature, requires, ensures)

        # Extract callees (functions called in the body)
        callees = self._extract_callees(body) if body else []

        # Calculate line number
        line_number = content[:start_pos].count("\n") + 1

        return VstdFunction(
            name=fn_name,
            type=fn_type,
            signature=signature,
            ensures=ensures,
            requires=requires,
            body=body,
            doc_comment=doc_comment,
            triggers=triggers,
            file_path=str(file_path),
            line_number=line_number,
            module=module,
            keywords=keywords,
            callees=callees,
        )

    def _extract_function_scope(self, content: str) -> str | None:
        """Extract just the scope of the current function

        Returns content from start of function to either:
        - End of body (closing brace)
        - Semicolon (for declarations)
        - Start of next function
        """
        # Find the opening brace or semicolon
        brace_match = re.search(r"\{", content)
        semicolon_match = re.search(r";", content)

        if brace_match:
            # Function has a body, find matching closing brace
            start = brace_match.start()
            brace_count = 0
            i = start

            while i < len(content):
                if content[i] == "{":
                    brace_count += 1
                elif content[i] == "}":
                    brace_count -= 1
                    if brace_count == 0:
                        # Found end of function
                        return content[: i + 1]
                i += 1

            # Didn't find closing brace, return up to next function or end
            next_fn = re.search(
                r"\n\s*(?:pub\s+)?"
                r"(?:(?:broadcast\s+)?(?:proof|axiom)|"
                r"(?:open|closed|uninterp)\s+spec|"
                r"spec|exec)\s+fn\s+",
                content[start:],
            )
            if next_fn:
                return content[: start + next_fn.start()]
            return content

        elif semicolon_match:
            # Declaration without body
            return content[: semicolon_match.end()]

        else:
            # No brace or semicolon found, return up to next function
            next_fn = re.search(
                r"\n\s*(?:pub\s+)?"
                r"(?:(?:broadcast\s+)?(?:proof|axiom)|"
                r"(?:open|closed|uninterp)\s+spec|"
                r"spec|exec)\s+fn\s+",
                content,
            )
            if next_fn:
                return content[: next_fn.start()]
            return content

    def _parse_doc_comment(self, doc_text: str) -> str | None:
        """Parse doc comment text from matched regex group

        Args:
            doc_text: Raw text containing /// comments

        Returns:
            Cleaned doc comment text
        """
        if not doc_text:
            return None

        lines = doc_text.split("\n")
        doc_lines = []

        for line in lines:
            stripped = line.strip()
            if stripped.startswith("///"):
                # Remove /// and whitespace
                doc_lines.append(stripped[3:].strip())

        result = "\n".join(doc_lines).strip()
        return result if result else None

    def _extract_clauses(self, content: str, clause_type: str) -> list[str]:
        """Extract requires or ensures clauses

        Args:
            content: Function content
            clause_type: 'requires' or 'ensures'
        """
        clauses = []

        # Pattern: requires/ensures followed by conditions until next keyword or {
        pattern = re.compile(
            rf"{clause_type}\s+(.*?)(?=\s*(?:requires|ensures|decreases|recommends|{{|;))",
            re.DOTALL | re.MULTILINE,
        )

        matches = pattern.findall(content)
        for match in matches:
            # Split by comma, but be careful with nested structures
            # For now, treat the whole block as one clause
            clause = match.strip()
            if clause:
                # Try to split by top-level commas
                clauses.extend(self._split_clauses(clause))

        return clauses

    def _split_clauses(self, clause_block: str) -> list[str]:
        """Split a clause block by top-level commas"""
        # Simple heuristic: split by , followed by newline
        # This isn't perfect but handles most cases
        parts = re.split(r",\s*\n", clause_block)
        return [p.strip().rstrip(",") for p in parts if p.strip()]

    def _extract_triggers(self, ensures: list[str]) -> list[str]:
        """Extract #[trigger] patterns from ensures clauses"""
        triggers = []

        for clause in ensures:
            # Pattern: #[trigger] expression
            matches = re.findall(r"#\[trigger\]\s*([^,\n\)]+)", clause)
            triggers.extend([m.strip() for m in matches])

        return triggers

    def _extract_body(self, content: str) -> str | None:
        """Extract function body if present"""
        # Find the opening brace
        brace_match = re.search(r"\{", content)
        if not brace_match:
            return None  # No body (declaration only)

        # Find matching closing brace
        start = brace_match.start()
        brace_count = 0
        i = start

        while i < len(content):
            if content[i] == "{":
                brace_count += 1
            elif content[i] == "}":
                brace_count -= 1
                if brace_count == 0:
                    # Found matching brace
                    body = content[start : i + 1]
                    # Limit body size
                    if len(body) > 2000:
                        return None  # Too large, skip
                    return body
            i += 1

        return None

    def _extract_keywords(
        self, signature: str, requires: list[str], ensures: list[str]
    ) -> list[str]:
        """Extract keywords from function signature and clauses"""
        keywords = set()

        combined_text = signature + " " + " ".join(requires) + " " + " ".join(ensures)

        # Data structure types
        for ds in ["Seq", "Set", "Map", "Vec", "Multiset", "Array"]:
            if ds in combined_text:
                keywords.add(ds)

        # Common operations
        operations = [
            "take",
            "push",
            "insert",
            "remove",
            "contains",
            "len",
            "subrange",
            "union",
            "intersect",
            "difference",
            "filter",
            "map",
            "fold",
            "finite",
            "empty",
        ]

        for op in operations:
            if re.search(rf"\b{op}\b", combined_text):
                keywords.add(op)

        # Proof concepts
        concepts = ["forall", "exists", "trigger", "decreases", "invariant"]
        for concept in concepts:
            if concept in combined_text:
                keywords.add(concept)

        return sorted(keywords)

    def _extract_callees(self, body: str) -> list[str]:
        """Extract function calls from the body

        Extracts function names that are called in the body.
        Handles both simple calls (lemma_foo()) and qualified calls (Module::lemma_foo()).

        Args:
            body: Function body code

        Returns:
            List of called function names
        """
        if not body:
            return []

        callees = set()

        # Pattern to match function calls: function_name(...) or Module::function_name(...)
        # Matches: lemma_foo(), ModINL::lemma_foo(), vstd::seq::take()
        call_pattern = re.compile(r"(?:[A-Z][a-zA-Z0-9_]*::)*([a-z_][a-z0-9_]*)\s*\(")

        # Comprehensive list of Verus/Rust keywords to filter out
        keywords_to_filter = {
            # Control flow
            "if",
            "else",
            "match",
            "while",
            "for",
            "loop",
            "break",
            "continue",
            "return",
            # Variable binding
            "let",
            "mut",
            "ref",
            # Verus proof keywords
            "assert",
            "assume",
            "requires",
            "ensures",
            "decreases",
            "invariant",
            "old",
            "forall",
            "exists",
            "choose",
            # Verus modifiers
            "by",
            "via",
            "reveal",
            "hide",
            # Common methods that are not proof functions
            "is_some",
            "is_none",
            "is_ok",
            "is_err",
            "unwrap",
            "expect",
            "clone",
            "copy",
            "drop",
            # Arithmetic/bit operations (these are typically exec or built-in)
            "add",
            "sub",
            "mul",
            "div",
            "rem",
            "shl",
            "shr",
            "and",
            "or",
            "xor",
            "not",
        }

        # Find all function calls
        for match in call_pattern.finditer(body):
            func_name = match.group(1)
            # Filter out keywords
            if func_name not in keywords_to_filter:
                callees.add(func_name)

        return list(callees)

    def _extract_open_specs(self, content: str, file_path: Path, module: str) -> list[VstdOpenSpec]:
        """Extract open spec function definitions"""
        open_specs = []

        # Pattern for open spec functions
        pattern = re.compile(r"pub\s+open\s+spec\s+fn\s+(\w+)", re.MULTILINE)

        for match in pattern.finditer(content):
            try:
                fn_name = match.group(1)
                start_pos = match.start()

                # Extract signature and body
                remaining = content[start_pos:]

                # Get signature
                sig_match = re.search(
                    r"pub\s+open\s+spec\s+fn\s+" + re.escape(fn_name) + r"[^{]*", remaining
                )
                if not sig_match:
                    continue

                signature = sig_match.group(0).strip()

                # Get body
                body = self._extract_body(remaining)
                if not body:
                    body = ""

                # Extract keywords
                keywords = self._extract_keywords(signature, [], [])

                # Calculate line number
                line_number = content[:start_pos].count("\n") + 1

                open_specs.append(
                    VstdOpenSpec(
                        name=fn_name,
                        signature=signature,
                        body=body,
                        file_path=str(file_path),
                        line_number=line_number,
                        module=module,
                        keywords=keywords,
                    )
                )

            except Exception as e:
                self.logger.warning(f"Failed to parse open spec {fn_name}: {e}")
                continue

        return open_specs


def main():
    """Test parser on a single file"""
    import sys

    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python parser.py <path-to-vstd-file.rs>")
        return

    parser = VstdParser()
    result = parser.parse_file(Path(sys.argv[1]))

    print(f"\n=== Module: {result['module']} ===")
    print(f"\nFunctions found: {len(result['functions'])}")
    for func in result["functions"][:5]:  # Show first 5
        print(f"  - {func.name} ({func.type})")
        print(f"    Keywords: {', '.join(func.keywords)}")
        print(f"    Ensures: {len(func.ensures)} clauses")

    print(f"\nOpen specs found: {len(result['open_specs'])}")
    for spec in result["open_specs"][:5]:  # Show first 5
        print(f"  - {spec.name}")


if __name__ == "__main__":
    main()
