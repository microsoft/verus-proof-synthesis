"""
Preprocessing Module for Agent Framework
Analyzes Verus code to identify lemmas, recursive functions, and opaque functions
to influence action selection during repair.
"""

import re
from dataclasses import dataclass


@dataclass
class CodeAnalysis:
    """Results of code analysis for preprocessing"""

    lemmas: list[str] = None
    recursive_functions: list[str] = None
    opaque_functions: list[str] = None
    target_function: str | None = None
    via_fn: int = 0  # the number of proof functions tagged as [via_fn]

    def __post_init__(self):
        if self.lemmas is None:
            self.lemmas = []
        if self.recursive_functions is None:
            self.recursive_functions = []
        if self.opaque_functions is None:
            self.opaque_functions = []

    @property
    def function_count(self) -> int:
        """Total count of all identified functions"""
        return len(self.lemmas) + len(self.recursive_functions) + len(self.opaque_functions)

    def has_lemmas(self) -> bool:
        """Check if there are any lemmas (excluding target function)"""
        # TODO: proof functions tagged with [via_fn] cannot be used as normal lemma
        return len(self.lemmas) - self.via_fn > 0

    def has_recursive_functions(self) -> bool:
        """Check if there are any recursive functions"""
        return len(self.recursive_functions) > 0

    def has_opaque_functions(self) -> bool:
        """Check if there are any opaque functions"""
        return len(self.opaque_functions) > 0

    def get_lemma_names(self) -> list[str]:
        """Get list of lemma function names"""
        return self.lemmas.copy()

    def get_recursive_function_names(self) -> list[str]:
        """Get list of recursive function names"""
        return self.recursive_functions.copy()

    def get_opaque_function_names(self) -> list[str]:
        """Get list of opaque function names"""
        return self.opaque_functions.copy()

    def to_dict(self) -> dict[str, any]:
        """Convert analysis to dictionary for serialization"""
        return {
            "lemmas": self.lemmas,
            "recursive_functions": self.recursive_functions,
            "opaque_functions": self.opaque_functions,
            "target_function": self.target_function,
            "has_lemmas": self.has_lemmas(),
            "via_fn": self.via_fn,
            "has_recursive_functions": self.has_recursive_functions(),
            "has_opaque_functions": self.has_opaque_functions(),
        }


class CodePreprocessor:
    """Preprocessor that analyzes Verus code for function types"""

    def __init__(self, logger=None):
        self.logger = logger or logger.bind()

        # Regex patterns for different function types
        # Pattern 1: proof fn functions starting with lemma_ or containing lemma or axiom
        self.lemma_pattern = re.compile(r"proof\s+fn\s+(\w*lemma\w*|\w*axiom\w*)", re.IGNORECASE)

        # Pattern 2: Any proof fn function (broader detection)
        self.proof_fn_broad_pattern = re.compile(
            r"proof\s+fn\s+([a-zA-Z_][a-zA-Z0-9_]*)", re.IGNORECASE
        )

        # Pattern for recursive functions (functions with decreases clauses)
        self.recursive_pattern = re.compile(
            r"(spec\s+fn|fn|proof\s+fn)\s+([a-zA-Z_][a-zA-Z0-9_]*)[^{]*?decreases",
            re.IGNORECASE | re.DOTALL,
        )

        # Pattern for opaque functions (functions with #[verifier::opaque] attribute)
        self.opaque_pattern = re.compile(
            r"#\[verifier::opaque\]\s*(?:open\s+|closed\s+|pub\s+)*(spec\s+fn|fn)\s+([a-zA-Z_][a-zA-Z0-9_]*)",
            re.IGNORECASE | re.DOTALL,
        )

        # Pattern to identify target function (the main function being proved)
        self.target_function_pattern = re.compile(
            r"#\[verifier::proof\]\s*fn\s+([a-zA-Z_][a-zA-Z0-9_]*)", re.IGNORECASE
        )

        # Pattern for regular fn (not spec fn, not proof fn) - likely the main function
        self.main_fn_pattern = re.compile(
            r"(?<!spec\s)(?<!proof\s)fn\s+([a-zA-Z_][a-zA-Z0-9_]*)", re.IGNORECASE
        )

    def analyze_code(self, code: str, target_function_name: str | None = None) -> CodeAnalysis:
        """
        Analyze Verus code to identify lemmas, recursive functions, and opaque functions

        Args:
            code: The Verus code to analyze
            target_function_name: Optional name of the target function (to exclude from lemmas)

        Returns:
            CodeAnalysis object with the analysis results
        """
        self.logger.info("Starting code preprocessing analysis...")

        analysis = CodeAnalysis()

        # Extract the verus! macro content
        verus_content = self._extract_verus_content(code)
        if not verus_content:
            self.logger.warning("No verus! macro found in code")
            return analysis

        # Find lemmas
        lemmas = self._find_lemmas(verus_content)
        if target_function_name and target_function_name in lemmas:
            lemmas.remove(target_function_name)
        analysis.lemmas = lemmas

        # Find the number of via_fn
        analysis.via_fn = verus_content.count("[via_fn]")
        if analysis.via_fn > 0:
            self.logger.warning(
                f"{analysis.via_fn} via_fn tags are found. Some lemma functions may not count"
            )

        # Find recursive functions
        analysis.recursive_functions = self._find_recursive_functions(verus_content)

        # Find opaque functions
        analysis.opaque_functions = self._find_opaque_functions(verus_content)

        # Determine target function if not provided
        if not target_function_name:
            target_function_name = self._find_target_function(verus_content)
        analysis.target_function = target_function_name

        # Log analysis results
        self.logger.info("Code analysis complete:")
        self.logger.info(f"  Lemmas found: {len(analysis.lemmas)} - {analysis.lemmas}")
        self.logger.info(
            f"  Recursive functions found: {len(analysis.recursive_functions)} - {analysis.recursive_functions}"
        )
        self.logger.info(
            f"  Opaque functions found: {len(analysis.opaque_functions)} - {analysis.opaque_functions}"
        )
        self.logger.info(f"  Target function: {analysis.target_function}")

        return analysis

    def _find_lemmas(self, code: str) -> list[str]:
        """Find all lemma functions in the code"""
        lemmas = []

        # Pattern 1: proof fn functions starting with lemma_ or containing lemma
        matches = self.lemma_pattern.findall(code)
        lemmas.extend(matches)

        # Pattern 2: Any proof fn function (broader detection)
        broad_matches = self.proof_fn_broad_pattern.findall(code)

        # Add proof functions that are likely lemmas (heuristic)
        for func_name in broad_matches:
            if func_name not in lemmas:
                # Check if it's a lemma by checking if it has ensures clause or is used for proving
                func_content = self._extract_function_content(code, func_name)
                # BUG fixing: the func_content does NOT include requires/ensures block.
                # So, the checking below would always fail.
                # I am changing it to search for `unimplemented' as this is the convention
                # in our benchmarks. In reality, I believe ALL proof fn should be treated as lemma
                if func_content and ("unimplemented" in func_content):
                    # if func_content and ('ensures' in func_content or 'assert' in func_content):
                    lemmas.append(func_name)

        return list(set(lemmas))  # Remove duplicates

    def _find_recursive_functions(self, code: str) -> list[str]:
        """Find all recursive functions (functions with decreases clauses)"""
        recursive_functions = []

        # Pattern: function with decreases clause
        # Look for functions followed by decreases
        matches = self.recursive_pattern.findall(code)

        for match in matches:
            func_type, func_name = match
            recursive_functions.append(func_name)

        return list(set(recursive_functions))  # Remove duplicates

    def _find_opaque_functions(self, code: str) -> list[str]:
        """Find all opaque functions (functions with #[verifier::opaque] attribute)"""
        opaque_functions = []
        matches = self.opaque_pattern.findall(code)

        for match in matches:
            func_type, func_name = match
            opaque_functions.append(func_name)

        return list(set(opaque_functions))  # Remove duplicates

    def _extract_verus_content(self, code: str) -> str:
        """Extract the content inside the verus! macro"""
        # Find the verus! macro
        verus_match = re.search(r"verus!\s*\{", code, re.IGNORECASE)
        if not verus_match:
            return ""

        # Find the matching closing brace
        start_pos = verus_match.end() - 1  # Position of opening brace
        brace_count = 1
        pos = start_pos + 1

        while pos < len(code) and brace_count > 0:
            if code[pos] == "{":
                brace_count += 1
            elif code[pos] == "}":
                brace_count -= 1
            pos += 1

        if brace_count == 0:
            return code[start_pos + 1 : pos - 1]  # Extract content between braces
        else:
            # Fallback: return everything after verus! if matching brace not found
            return code[verus_match.end() :]

    def _find_target_function(self, code: str) -> str | None:
        """Find the target function (the main function being proved)"""
        # Look for functions with #[verifier::proof] or similar attributes
        # Or the main function that's not a lemma/spec function

        # Pattern 1: Function with proof attribute
        matches = self.target_function_pattern.findall(code)
        if matches:
            return matches[0]

        # Pattern 2: Regular fn (not spec fn, not proof fn) - likely the main function
        matches = self.main_fn_pattern.findall(code)
        if matches:
            # Return the first regular function found
            return matches[0]

        return None

    def _extract_function_content(self, code: str, func_name: str) -> str:
        """Extract the content of a specific function"""
        # Find the function declaration
        func_pattern = rf"(?:spec\s+fn|fn|proof\s+fn)\s+{re.escape(func_name)}\s*\([^{{]*\{{"
        match = re.search(func_pattern, code, re.IGNORECASE | re.DOTALL)
        if not match:
            return ""

        # Find the matching closing brace
        start_pos = match.end() - 1  # Position of opening brace
        brace_count = 1
        pos = start_pos + 1

        while pos < len(code) and brace_count > 0:
            if code[pos] == "{":
                brace_count += 1
            elif code[pos] == "}":
                brace_count -= 1
            pos += 1

        if brace_count == 0:
            return code[start_pos:pos]
        else:
            return ""

    def get_action_recommendations(self, analysis: CodeAnalysis) -> dict[str, any]:
        """
        Get action recommendations based on code analysis

        Returns:
            Dictionary with action recommendations and reasoning
        """
        recommendations = {
            "use_lemma_enabled": analysis.has_lemmas(),
            "compute_boost": analysis.has_recursive_functions(),
            "reveal_opaque_enabled": analysis.has_opaque_functions(),
            "reasoning": [],
        }

        # Generate reasoning for each recommendation
        if not analysis.has_lemmas():
            recommendations["reasoning"].append(
                "USELEMMA action disabled: No lemmas found in code (excluding target function)"
            )
        else:
            recommendations["reasoning"].append(
                f"USELEMMA action enabled: Found {len(analysis.lemmas)} lemmas: {analysis.lemmas}"
            )

        if analysis.has_recursive_functions():
            recommendations["reasoning"].append(
                f"Please consider more using COMPUTE action: Found {len(analysis.recursive_functions)} recursive functions: {analysis.recursive_functions}"
            )
        else:
            recommendations["reasoning"].append(
                "COMPUTE action: No recursive functions found, standard priority"
            )

        if not analysis.has_opaque_functions():
            recommendations["reasoning"].append(
                "REVEAL_OPAQUE action disabled: No opaque functions found in code"
            )
        else:
            recommendations["reasoning"].append(
                f"REVEAL_OPAQUE action enabled: Found {len(analysis.opaque_functions)} opaque functions: {analysis.opaque_functions}"
            )

        return recommendations

    def filter_actions(self, available_actions: list[str], analysis: CodeAnalysis) -> list[str]:
        """
        Filter available actions based on code analysis

        Args:
            available_actions: List of available action types
            analysis: Code analysis results

        Returns:
            Filtered list of actions with appropriate priorities
        """
        filtered_actions = available_actions.copy()

        # Disable USELEMMA if no lemmas found
        if not analysis.has_lemmas() and "USELEMMA" in filtered_actions:
            filtered_actions.remove("USELEMMA")

        # Disable REVEAL_OPAQUE if no opaque functions found
        if not analysis.has_opaque_functions() and "REVEAL_OPAQUE" in filtered_actions:
            filtered_actions.remove("REVEAL_OPAQUE")

        return filtered_actions

    def boost_action_priority(self, action_list: list[str], analysis: CodeAnalysis) -> list[str]:
        """
        Boost priority of certain actions based on code analysis

        Args:
            action_list: List of actions in priority order
            analysis: Code analysis results

        Returns:
            Reordered action list with boosted priorities
        """
        if not analysis.has_recursive_functions():
            return action_list

        # Boost COMPUTE action if recursive functions are present
        if "COMPUTE" in action_list:
            # Move COMPUTE to higher priority (near the top)
            action_list.remove("COMPUTE")
            # Insert after the first few actions
            insert_position = min(3, len(action_list))
            action_list.insert(insert_position, "COMPUTE")

        return action_list


def create_preprocessor(logger=None) -> CodePreprocessor:
    """Factory function to create a preprocessor instance"""
    return CodePreprocessor(logger)
