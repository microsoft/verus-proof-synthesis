"""
Centralized Verus Syntax Pattern Checker

This module provides a single source of truth for known invalid Verus syntax patterns.
It can be used across the codebase in:
- Reasoning phase: Filter out invalid patterns before suggesting actions
- Action phase: Validate generated code before compilation
- Syntax repair: Guide repairs with specific pattern knowledge
- Failure history: Provide targeted hints based on detected patterns
"""

import re
from dataclasses import dataclass


@dataclass
class SyntaxPattern:
    """A known invalid Verus syntax pattern"""

    name: str
    regex: str
    flags: int
    error_message: str
    hint: str
    examples_invalid: list[str]
    examples_valid: list[str]


class VerusSyntaxPatterns:
    """Centralized registry of known invalid Verus syntax patterns"""

    # Define all known invalid patterns
    PATTERNS = [
        SyntaxPattern(
            name="choose_ensuring_statement",
            regex=r"choose\s+\w+:\s*\w+\s+ensuring",
            flags=0,
            error_message="Invalid Verus syntax: Cannot use 'choose X: T ensuring ...' as a statement",
            hint="Use 'let x = choose|x: T| condition;' instead. The choose expression syntax requires closures with |variable| notation.",
            examples_invalid=[
                "choose x0: S ensuring s1.contains(x0) && f(x0) == y by { ... }",
                "choose x: int ensuring x > 0 by { assert(exists |y| y > 0); }",
            ],
            examples_valid=[
                "let x0 = choose|x: S| s1.contains(x) && f(x) == y;",
                "let x = choose|x: int| x > 0;",
            ],
        ),
        SyntaxPattern(
            name="choose_such_that_statement",
            regex=r"choose\s+\w+:\s*\w+\s+such\s+that.*?by\s*\{",
            flags=re.DOTALL,
            error_message="Invalid Verus syntax: 'choose X: T such that ...' is not valid",
            hint="Use 'let x = choose|x: T| condition;' to bind witnesses from existential statements.",
            examples_invalid=[
                "choose x0: S such that s1.contains(x0) && f(x0) == y by { ... }",
            ],
            examples_valid=[
                "let x0 = choose|x: S| s1.contains(x) && f(x) == y;",
            ],
        ),
        SyntaxPattern(
            name="choose_ensuring_in_assert_forall",
            regex=r"assert\s+forall.*?choose\s+\w+:\s*\w+\s+ensuring",
            flags=re.DOTALL,
            error_message="Invalid Verus syntax: Cannot use 'choose X: T ensuring ...' inside 'assert forall' block",
            hint="Inside assert forall blocks, use 'let x = choose|x: T| condition;' to extract witnesses. The choose statement form with 'ensuring' is not valid in this context.",
            examples_invalid=[
                """assert forall |y: T| condition by {
    choose x0: S ensuring s1.contains(x0) && f(x0) == y by { ... };
}""",
            ],
            examples_valid=[
                """assert forall |y: T| condition by {
    let x0 = choose|x: S| s1.contains(x) && f(x) == y;
    assert(x0.property());
}""",
            ],
        ),
        SyntaxPattern(
            name="fix_statement",
            regex=r"^\s*fix\s+\w+(\s*:\s*[^;]+)?;",
            flags=re.MULTILINE,
            error_message="Invalid Verus syntax: 'fix variable;' is not valid - fix is not a statement in Verus",
            hint="Verus does not support the 'fix' statement. If you are trying to prove a 'forall' property, use the 'assert forall |vars| ... by { ... }' syntax. In this block, the quantified variables are automatically in scope. Note the difference: 'assert forall |x| P(x) by { ... }' brings 'x' into scope, whereas 'assert(forall |x| P(x)) by { ... }' does not.",
            examples_invalid=[
                """assert forall |v| condition by {
    fix v;  // INVALID!
    assert(v.property());
}""",
                "fix i1; fix i2;  // INVALID!",
                "fix v: V;  // INVALID - even with type annotation",
            ],
            examples_valid=[
                """assert forall |v| condition by {
    // v is already in scope, just use it
    assert(v.property());
}""",
                "// No need for 'fix' - quantified variables are already in scope",
            ],
        ),
        SyntaxPattern(
            name="assume_statement",
            regex=r"^\s*assume\s*\(",
            flags=re.MULTILINE,
            error_message="Invalid Verus syntax: 'assume(...)' is not allowed in proof code",
            hint="Verus does not allow 'assume' statements in proofs - all facts must be proven. If you have a precondition, it should be in the 'requires' clause. If you need a hypothesis in a forall proof, use the implication form: 'assert forall |v| condition ==> conclusion'.",
            examples_invalid=[
                "assume(x < w);  // NOT ALLOWED",
                """assert forall |v| condition by {
    assume(m.contains(v));  // NOT ALLOWED
}""",
            ],
            examples_valid=[
                """// Use 'requires' clause:
proof fn my_proof(x: int, w: int)
    requires x < w
{ // x < w is already known }""",
                """// In forall, use implication:
assert forall |v| m.contains(v) ==> property(v) by {
    // m.contains(v) is available when true
}""",
            ],
        ),
        SyntaxPattern(
            name="semicolon_after_requires",
            regex=r"^\s*(requires|ensures)\s*$.*?^\s*[^;]+;\s*$\s*^\s*(ensures|decreases|recommends|opens_invariants)",
            flags=re.MULTILINE | re.DOTALL,
            error_message="Invalid Verus syntax: semicolon after requires/ensures clause - use comma instead",
            hint="In Verus function signatures, use commas (not semicolons) to separate requires, ensures, decreases, and other clauses. Semicolons are only used at the end of statements inside function bodies.",
            examples_invalid=[
                """fn my_proof(x: int)
    requires x > 0;  // INVALID
    ensures result > 0""",
                """requires
    s.len() == 1;  // INVALID
    ensures
    condition""",
            ],
            examples_valid=[
                """fn my_proof(x: int)
    requires x > 0,  // CORRECT - use comma
    ensures result > 0""",
                """requires
    s.len() == 1,  // CORRECT - use comma
ensures
    condition""",
            ],
        ),
        SyntaxPattern(
            name="intro_statement",
            regex=r"^\s*intro\s+\w+(\s*:\s*[^;]+)?;",
            flags=re.MULTILINE,
            error_message="Invalid Verus syntax: 'intro variable;' is not valid - intro is not a statement in Verus",
            hint="In Verus, there is no 'intro' statement. Like 'fix', quantified variables in 'assert forall' are automatically in scope. Just use the variable directly without introducing it.",
            examples_invalid=[
                """assert forall |x| condition by {
    intro x;  // INVALID
    assert(x.property());
}""",
                "intro base;  // INVALID",
                "intro pte;  // INVALID",
                "intro v: V;  // INVALID - even with type",
            ],
            examples_valid=[
                """assert forall |x| condition by {
    // x is already in scope, just use it
    assert(x.property());
}""",
                "// No equivalent - 'intro' is not needed in Verus",
            ],
        ),
        SyntaxPattern(
            name="reveal_opaque_wrong_syntax",
            regex=r"\breveal\s+(opaque\s+)?(spec\s+fn\s+)?\w+\s*;",
            flags=re.MULTILINE,
            error_message="Invalid Verus syntax: 'reveal opaque spec fn Name;' or 'reveal Name;' is not valid",
            hint="Use 'reveal(FunctionName);' to reveal opaque functions in Verus. The correct syntax uses parentheses and the function name only, without 'opaque', 'spec', or 'fn' keywords.",
            examples_invalid=[
                "reveal opaque spec fn size_of_bin;  // INVALID",
                "reveal size_of_bin;  // INVALID",
                "reveal self::my_function;  // INVALID",
            ],
            examples_valid=[
                "reveal(size_of_bin);  // Correct",
                "reveal(MyStruct::my_method);  // Correct with path",
                "reveal(Seq::filter);  // Correct for vstd functions",
            ],
        ),
    ]

    @classmethod
    def check_all_patterns(cls, code: str) -> tuple[SyntaxPattern, str] | None:
        """
        Check code against all known invalid patterns.

        Returns:
            Tuple of (pattern, match) if invalid pattern found, None otherwise
        """
        for pattern in cls.PATTERNS:
            try:
                match = re.search(pattern.regex, code, pattern.flags)
                if match:
                    return (pattern, match.group(0))
            except re.error:
                # Skip patterns with broken regex
                continue
        return None

    @classmethod
    def get_error_message(cls, code: str) -> str | None:
        """
        Get error message for the first detected invalid pattern.

        Returns:
            Error message string if pattern found, None otherwise
        """
        result = cls.check_all_patterns(code)
        if result:
            pattern, _ = result
            return pattern.error_message
        return None

    @classmethod
    def get_hint(cls, code: str) -> str | None:
        """
        Get helpful hint for fixing the first detected invalid pattern.

        Returns:
            Hint string if pattern found, None otherwise
        """
        result = cls.check_all_patterns(code)
        if result:
            pattern, _ = result
            return pattern.hint
        return None

    @classmethod
    def get_detailed_feedback(cls, code: str) -> dict | None:
        """
        Get detailed feedback about detected pattern including examples.

        Returns:
            Dict with pattern info, or None if no pattern detected
        """
        result = cls.check_all_patterns(code)
        if result:
            pattern, matched_text = result
            return {
                "pattern_name": pattern.name,
                "error_message": pattern.error_message,
                "hint": pattern.hint,
                "matched_text": matched_text,
                "examples_invalid": pattern.examples_invalid,
                "examples_valid": pattern.examples_valid,
            }
        return None

    @classmethod
    def check_specific_pattern(cls, code: str, pattern_name: str) -> bool:
        """Check if code matches a specific pattern by name"""
        for pattern in cls.PATTERNS:
            if pattern.name == pattern_name:
                try:
                    return re.search(pattern.regex, code, pattern.flags) is not None
                except re.error:
                    return False
        return False

    @classmethod
    def get_all_patterns_info(cls) -> list[dict]:
        """Get information about all registered patterns (for documentation)"""
        return [
            {
                "name": p.name,
                "error_message": p.error_message,
                "hint": p.hint,
                "examples_invalid": p.examples_invalid,
                "examples_valid": p.examples_valid,
            }
            for p in cls.PATTERNS
        ]


# Convenience functions for quick access
def check_invalid_verus_syntax(code: str) -> str | None:
    """
    Quick check for invalid Verus syntax patterns.

    Returns:
        Error message if invalid pattern found, None otherwise
    """
    return VerusSyntaxPatterns.get_error_message(code)


def get_syntax_hint(code: str) -> str | None:
    """
    Get a helpful hint for fixing detected syntax issues.

    Returns:
        Hint string if pattern found, None otherwise
    """
    return VerusSyntaxPatterns.get_hint(code)
