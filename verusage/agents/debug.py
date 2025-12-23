#!/usr/bin/env python3
"""
Debug Script for Testing Individual Actions
This script allows you to test any action with custom inputs including code, errors, and parameters.
"""
import glob
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# Add the project root and agents directory to Python path
current_dir = Path(__file__).parent
project_root = current_dir.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(current_dir))

try:
    # Try importing as if we're in the agents package
    from actions import ActionType, action_registry
    from shared_types import ActionResult, Observation
except ImportError:
    # Fallback: try importing from the full path
    try:
        from agents.actions import ActionType, action_registry
        from agents.shared_types import ActionResult, Observation
    except ImportError:
        print("Error: Could not import required modules.")
        print("Please run this script from the project root directory using:")
        print("  python -m agents.debug")
        print("Or from the code directory using:")
        print("  python -m agents.debug")
        sys.exit(1)

# Import real refinement engine and related classes
try:
    # Add the parent directory to path to import from code/
    parent_dir = Path(__file__).parent.parent
    sys.path.insert(0, str(parent_dir))

    from global_config import GlobalConfig
    from refinement import Refinement
    from veval import VerusError, VerusErrorType, verus

    print("[INFO] Successfully imported real Refinement engine")
except ImportError as e:
    print(f"[ERROR] Could not import real Refinement engine: {e}")
    print("Please ensure you have the correct dependencies installed.")
    sys.exit(1)


@dataclass
class DebugConfig:
    """Configuration class for debug script with all required fields"""

    # Azure OpenAI settings
    aoai_debug_model: str = "gpt-4"
    aoai_model: str = "gpt-4"
    aoai_endpoint: str = "https://your-endpoint.openai.azure.com/"
    aoai_api_key: str = ""
    aoai_api_base: list = None
    aoai_api_version: str = "2023-05-15"
    aoai_max_retries: int = 3

    # LLM parameters
    temperature: float = 1.0
    max_tokens: int = 4096
    timeout: int = 30

    # Paths
    example_path: str = "examples"
    lemma_path: str = "lemmas"
    verus_path: str = "verus"  # Path to Verus executable

    # Debug settings
    debug_mode: bool = True
    verbose: bool = False

    def __post_init__(self):
        if self.aoai_api_base is None:
            self.aoai_api_base = [self.aoai_endpoint]
        if isinstance(self.aoai_api_key, str):
            self.aoai_api_key = [self.aoai_api_key] if self.aoai_api_key else [""]


@dataclass
class SimpleLogger:
    """Simple logger for testing"""

    def info(self, msg):
        print(f"[INFO] {msg}")

    def error(self, msg):
        print(f"[ERROR] {msg}")

    def warning(self, msg):
        print(f"[WARNING] {msg}")

    def debug(self, msg):
        print(f"[DEBUG] {msg}")


class ActionDebugger:
    """Main debug class for testing actions"""

    def __init__(self, config=None):
        if config is None:
            print("[ERROR] Configuration is required for real Azure OpenAI integration")
            print("Please provide a valid configuration or create one using --create-config")
            sys.exit(1)

        self.config = config
        self.logger = SimpleLogger()

        # Set up Verus path from config
        self._setup_verus_path()

        # Initialize global config and create real refinement engine
        try:
            GlobalConfig.initialize(self.config, self.logger)
            self.refinement = Refinement()
            print(
                f"[INFO] Real Refinement engine created with model: {self.config.aoai_debug_model}"
            )
            print(f"[INFO] Azure OpenAI endpoint: {self.config.aoai_endpoint}")
        except Exception as e:
            print(f"[ERROR] Failed to create Refinement engine: {e}")
            print("Please check your Azure OpenAI configuration")
            sys.exit(1)

    def _setup_verus_path(self):
        """Set up the Verus path for VEval"""
        if hasattr(self.config, "verus_path") and self.config.verus_path:
            try:
                verus.set_verus_path(self.config.verus_path)
                print(f"[INFO] Verus path set to: {self.config.verus_path}")
            except Exception as e:
                print(f"[ERROR] Failed to set Verus path: {e}")
                print("Please check that the Verus executable path is correct in your config")
                sys.exit(1)
        else:
            print("[WARNING] No verus_path specified in config")
            print("[WARNING] VEval may fail without proper Verus path")
            print("[INFO] Add 'verus_path': '/path/to/verus' to your config file")

    @staticmethod
    def find_config_files():
        """Find all config*.json files in current directory and project root"""
        config_files = []

        # Search in current directory
        current_configs = glob.glob("config*.json")
        config_files.extend([Path(f) for f in current_configs])

        # Search in project root (parent of current file's directory)
        project_root = Path(__file__).parent.parent
        project_configs = glob.glob(str(project_root / "config*.json"))
        config_files.extend([Path(f) for f in project_configs])

        # Search in agents directory
        agents_dir = Path(__file__).parent
        agents_configs = glob.glob(str(agents_dir / "config*.json"))
        config_files.extend([Path(f) for f in agents_configs])

        # Remove duplicates and sort
        unique_configs = list(set(config_files))
        unique_configs.sort(key=lambda x: x.name)

        return unique_configs

    @staticmethod
    def load_config_from_file(config_path: str):
        """Load configuration from a file (JSON or Python module)"""
        config_file = Path(config_path)

        if not config_file.exists():
            print(f"[ERROR] Config file not found: {config_path}")
            return None

        try:
            if config_file.suffix == ".json":
                # Load from JSON file
                with open(config_file) as f:
                    config_data = json.load(f)

                # Create a config object with the loaded data
                config = DebugConfig()
                for key, value in config_data.items():
                    if hasattr(config, key):
                        setattr(config, key, value)
                    else:
                        print(f"[WARNING] Unknown config field: {key}")

                print(f"[INFO] Loaded config from: {config_file}")
                return config

            elif config_file.suffix == ".py":
                # Load from Python module
                import importlib.util

                spec = importlib.util.spec_from_file_location("config", config_file)
                config_module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(config_module)

                # Look for a config object or Config class
                if hasattr(config_module, "config"):
                    return config_module.config
                elif hasattr(config_module, "Config"):
                    return config_module.Config()
                else:
                    print(f"[ERROR] No 'config' object or 'Config' class found in {config_path}")
                    return None
            else:
                print(f"[ERROR] Unsupported config file format: {config_file.suffix}")
                return None

        except Exception as e:
            print(f"[ERROR] Failed to load config from {config_path}: {e}")
            return None

    @staticmethod
    def select_config_interactively():
        """Interactive config file selection"""
        config_files = ActionDebugger.find_config_files()

        if not config_files:
            print("No config*.json files found.")
            print("Please create a configuration file with your Azure OpenAI settings.")
            print("The config file should include fields like:")
            print("  - aoai_api_key, aoai_endpoint, aoai_api_version")
            print("  - verus_path (path to Verus executable)")
            print("  - temperature, max_tokens, etc.")
            return None

        print("Found configuration files:")
        for i, config_file in enumerate(config_files, 1):
            print(f"  {i}. {config_file}")

        while True:
            try:
                choice = input(f"Select config file (1-{len(config_files)}): ").strip()
                choice_num = int(choice)

                if 1 <= choice_num <= len(config_files):
                    selected_config = config_files[choice_num - 1]
                    config = ActionDebugger.load_config_from_file(str(selected_config))
                    if config:
                        return config
                    else:
                        print("Failed to load config. Please try another one.")
                else:
                    print(f"Invalid choice. Please enter 1-{len(config_files)}")
            except ValueError:
                print("Please enter a valid number.")

    def create_observation_from_error(
        self, code: str, error: VerusError, context_lines: int = 10
    ) -> Observation:
        """Create observation from real VerusError - same pattern as agents use"""

        # Extract error information directly from VerusError like agents do
        error_trace = error.trace[0] if error.trace else None

        if error_trace:
            error_location = (error_trace.lines[0], error_trace.lines[1])
            error_text = error_trace.get_text()
        else:
            # Fallback if no trace available
            error_location = (0, 0)
            error_text = error.get_text() if hasattr(error, "get_text") else str(error)

        # Extract surrounding context (same as agents do)
        lines = code.splitlines()
        start_line = max(0, error_location[0] - context_lines)
        end_line = min(len(lines), error_location[1] + context_lines)
        surrounding_context = "\n".join(lines[start_line:end_line])

        return Observation(
            code=code,
            error=error,
            error_location=error_location,
            error_text=error_text,
            surrounding_context=surrounding_context,
        )

    def create_observation_from_code(self, code: str, code_file: str = None) -> Observation:
        """Create observation from code by evaluating it with VEval to get real VerusError objects"""

        # Load code from file if specified
        if code_file is not None:
            try:
                file_path = Path(code_file)

                # Search in multiple locations
                search_paths = [
                    file_path,  # As specified
                    Path.cwd() / code_file,  # Relative to current directory
                    Path(__file__).parent.parent / code_file,  # Relative to project root
                ]

                # Also try common extensions if no extension provided
                if not file_path.suffix:
                    for ext in [".rs", ".verus", ".txt"]:
                        search_paths.extend(
                            [
                                Path(str(file_path) + ext),
                                Path.cwd() / (code_file + ext),
                                Path(__file__).parent.parent / (code_file + ext),
                            ]
                        )

                found_path = None
                for path in search_paths:
                    if path.exists():
                        found_path = path
                        break

                if found_path:
                    code = found_path.read_text(encoding="utf-8")
                    print(f"[INFO] Loaded code from: {found_path}")
                    print(f"[INFO] Code length: {len(code)} characters")
                else:
                    print(f"[ERROR] Could not find file: {code_file}")
                    print("[INFO] Searched in:")
                    for path in search_paths[:3]:  # Show first 3 search paths
                        print(f"  - {path}")
                    return None
            except Exception as e:
                print(f"[ERROR] Failed to read file {code_file}: {e}")
                return None

        if code is None:
            code = """
verus! {
fn test_function(x: i32, y: i32) -> i32
    requires x > 0 && y > 0
    ensures result >= 0
{
    let result = x + y;
    assert(result > x);  // This assertion might fail
    result
}
}
            """.strip()

        # Always use VEval to get real VerusError objects
        try:
            from veval import VEval

            print("[INFO] Evaluating code with VEval to find real errors...")
            veval = VEval(code, self.logger)
            veval.eval()
            score = veval.get_score()

            print(
                f"[INFO] VEval results: {score.verus_errors} Verus errors, {score.errors} total errors"
            )

            if score.verus_errors > 0 and hasattr(veval, "verus_errors") and veval.verus_errors:
                # Use the first real error found
                real_error = veval.verus_errors[0]
                print(f"[INFO] Using real VerusError: {real_error.error}")
                print(f"[INFO] Error text: {real_error.get_text()}")
                return self.create_observation_from_error(code, real_error)
            else:
                print("[ERROR] No VerusErrors found in the code!")
                print("[INFO] The code may be correct or have only compilation errors")
                print(f"[INFO] Score details: compilation_error={score.compilation_error}")
                return None

        except Exception as e:
            print(f"[ERROR] Failed to evaluate code with VEval: {e}")
            import traceback

            traceback.print_exc()
            return None

    def create_sample_observation(
        self,
        code: str = None,
        code_file: str = None,
        error_type: VerusErrorType = None,
        error_text: str = None,
        error_location: tuple[int, int] = None,
    ) -> Observation:
        """Create observation using real VEval - no more mock errors!"""

        # Always use the real VEval approach
        return self.create_observation_from_code(code, code_file)

    def test_action(
        self,
        action_type: ActionType,
        observation: Observation = None,
        params: dict[str, Any] = None,
        code_file: str = None,
        verbose: bool = False,
        save_output: bool = False,
    ) -> ActionResult:
        """Test a specific action with given inputs"""

        if observation is None:
            observation = self.create_sample_observation(code_file=code_file)

        if params is None:
            params = {"guidance": f"Test guidance for {action_type.value}"}

        # Get action class and instantiate
        action_class = action_registry.get_action_class(action_type)
        action_instance = action_class()

        print(f"\n{'='*60}")
        print(f"TESTING ACTION: {action_type.value.upper()}")
        print(f"{'='*60}")

        # Print action metadata
        print(f"\nAction Description: {action_class.get_description()}")
        print(f"Guidance Template: {action_class.get_guidance_template()}")
        print(f"When to Apply: {action_class.get_when_to_apply()}")
        print(f"Acceptance Criteria: {action_class.get_acceptance_criteria()}")

        # Print input observation
        print("\nINPUT OBSERVATION:")
        print(f"Error Type: {observation.error_type}")
        print(f"Error Location: {observation.error_location}")
        print(f"Error Text: {observation.error_text}")
        print(f"Code Length: {len(observation.code)} characters")
        print(f"Parameters: {params}")

        # Execute action
        try:
            if verbose:
                print(f"\n{'='*60}")
                print("EXECUTING ACTION WITH REAL AZURE OPENAI")
                print(f"{'='*60}")
                print(f"Action: {action_type.value}")
                print(f"Parameters: {params}")

                # Enable debug mode for more detailed output
                if (
                    hasattr(GlobalConfig.get_refinement(), "debug_mode")
                    if GlobalConfig.get_refinement()
                    else False
                ):
                    self.refinement.debug_mode = True

            # Let the action handle everything internally - prompts, LLM calls, etc.
            result = action_instance.execute(observation, params)

            if verbose:
                print(f"\n{'='*60}")
                print("ACTION EXECUTION COMPLETED")
                print(f"{'='*60}")
                # Disable debug mode
                if (
                    hasattr(GlobalConfig.get_refinement(), "debug_mode")
                    if GlobalConfig.get_refinement()
                    else False
                ):
                    self.refinement.debug_mode = False

            print("\nACTION RESULT:")
            print(f"Success: {result.success}")
            print(f"Action: {result.action_taken.value}")
            print(f"Explanation: {result.explanation}")
            print(f"Candidates: {len(result.candidates)}")

            if result.candidates:
                print("\nGENERATED CANDIDATES WITH ERROR EVALUATION:")

                max_candidates = (
                    len(result.candidates) if verbose else min(3, len(result.candidates))
                )

                for i, candidate in enumerate(result.candidates[:max_candidates], 1):
                    print(f"\n{'-'*20} Candidate {i} {'-'*20}")

                    # Evaluate candidate for errors
                    candidate_error_info = self._evaluate_candidate_errors(
                        candidate, observation.error
                    )

                    if verbose:
                        # Show full candidate in verbose mode
                        print(candidate)
                    else:
                        # Show truncated version
                        if len(candidate) > 500:
                            print(
                                candidate[:500] + f"\n... ({len(candidate) - 500} more characters)"
                            )
                        else:
                            print(candidate)

                    # Print error evaluation results
                    print(f"\n--- Error Evaluation for Candidate {i} ---")
                    print(f"Original Error Fixed: {candidate_error_info['original_error_fixed']}")
                    print(f"New Errors Introduced: {candidate_error_info['new_errors_count']}")
                    print(f"Total Errors: {candidate_error_info['total_errors']}")
                    print(f"Compilation Status: {candidate_error_info['compilation_status']}")

                    if candidate_error_info["error_details"]:
                        print("Error Details:")
                        for j, error_detail in enumerate(
                            candidate_error_info["error_details"][:3], 1
                        ):  # Show max 3 errors
                            print(f"  {j}. {error_detail}")
                        if len(candidate_error_info["error_details"]) > 3:
                            print(
                                f"  ... and {len(candidate_error_info['error_details']) - 3} more errors"
                            )

                    # Overall assessment
                    if (
                        candidate_error_info["original_error_fixed"]
                        and candidate_error_info["new_errors_count"] == 0
                    ):
                        print(
                            f"✅ CANDIDATE {i}: SUCCESS - Fixed original error with no new errors"
                        )
                    elif candidate_error_info["original_error_fixed"]:
                        print(
                            f"⚠️  CANDIDATE {i}: PARTIAL - Fixed original error but introduced {candidate_error_info['new_errors_count']} new errors"
                        )
                    elif candidate_error_info["new_errors_count"] == 0:
                        print(f"❌ CANDIDATE {i}: FAILED - Original error not fixed, no new errors")
                    else:
                        print(
                            f"❌ CANDIDATE {i}: FAILED - Original error not fixed, {candidate_error_info['new_errors_count']} new errors introduced"
                        )

                if len(result.candidates) > max_candidates:
                    print(f"\n... and {len(result.candidates) - max_candidates} more candidates")
                    print("Use --verbose to see all candidates")

            # Save detailed output to file if requested
            if save_output:
                self._save_detailed_output(action_type, observation, params, result, verbose)

            return result

        except Exception as e:
            print(f"\nERROR DURING EXECUTION: {e}")
            import traceback

            traceback.print_exc()
            return None

    def _evaluate_candidate_errors(
        self, candidate_code: str, original_error: VerusError
    ) -> dict[str, Any]:
        """Evaluate a candidate for errors and compare with original error"""
        try:
            from veval import VEval

            # Evaluate the candidate code
            veval = VEval(candidate_code, self.logger)
            veval.eval()
            score = veval.get_score()

            error_info = {
                "original_error_fixed": False,
                "new_errors_count": 0,
                "total_errors": score.verus_errors,
                "compilation_status": "Success" if score.compilation_error == 0 else "Failed",
                "error_details": [],
            }

            # Check if original error is fixed
            original_error_found = False
            if hasattr(veval, "verus_errors") and veval.verus_errors:
                for error in veval.verus_errors:
                    # Check if this error matches the original error
                    if self._errors_match(error, original_error):
                        original_error_found = True
                        break
                    else:
                        # This is a new/different error
                        error_info["error_details"].append(f"{error.error}: {error.get_text()}")

                error_info["new_errors_count"] = len(veval.verus_errors) - (
                    1 if original_error_found else 0
                )

            error_info["original_error_fixed"] = not original_error_found

            # Add compilation errors to details if any
            if score.compilation_error > 0:
                error_info["error_details"].append(f"Compilation errors: {score.compilation_error}")

            return error_info

        except Exception as e:
            self.logger.warning(f"Failed to evaluate candidate errors: {e}")
            return {
                "original_error_fixed": False,
                "new_errors_count": 0,
                "total_errors": 0,
                "compilation_status": "Evaluation Failed",
                "error_details": [f"Evaluation error: {str(e)}"],
            }

    def _errors_match(self, error1: VerusError, error2: VerusError) -> bool:
        """Check if two VerusError objects represent the same error using the built-in similar method"""
        try:
            # Use the existing VerusError.similar method which compares error_text and trace_text
            return error1.similar(error2)
        except Exception as e:
            self.logger.warning(f"Error comparing VerusError objects: {e}")
            return False

    def _save_detailed_output(
        self,
        action_type: ActionType,
        observation: Observation,
        params: dict[str, Any],
        result: ActionResult,
        verbose: bool,
    ):
        """Save detailed test output to files"""
        import datetime

        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = Path("debug_output")
        output_dir.mkdir(exist_ok=True)

        base_filename = f"{action_type.value}_{timestamp}"

        # Evaluate all candidates for error information
        candidate_evaluations = []
        if result.candidates:
            for _i, candidate in enumerate(result.candidates, 1):
                error_info = self._evaluate_candidate_errors(candidate, observation.error)
                candidate_evaluations.append(error_info)

        # Save summary with error evaluation
        summary_file = output_dir / f"{base_filename}_summary.txt"
        with open(summary_file, "w") as f:
            f.write("ACTION DEBUG SUMMARY\n")
            f.write(f"{'='*50}\n")
            f.write(f"Action: {action_type.value}\n")
            f.write(f"Timestamp: {timestamp}\n")
            f.write(f"Success: {result.success}\n")
            f.write(f"Candidates: {len(result.candidates)}\n")
            f.write(f"Explanation: {result.explanation}\n\n")

            f.write("INPUT OBSERVATION:\n")
            f.write(f"Error Type: {observation.error_type}\n")
            f.write(f"Error Location: {observation.error_location}\n")
            f.write(f"Error Text: {observation.error_text}\n")
            f.write(f"Parameters: {params}\n\n")

            f.write("INPUT CODE:\n")
            f.write(f"{'-'*30}\n")
            f.write(observation.code)
            f.write(f"\n{'-'*30}\n\n")

            # Add candidate evaluation summary
            if candidate_evaluations:
                f.write("CANDIDATE EVALUATION SUMMARY:\n")
                f.write(f"{'-'*40}\n")
                successful_candidates = 0
                partial_candidates = 0
                failed_candidates = 0

                for i, eval_info in enumerate(candidate_evaluations, 1):
                    f.write(f"Candidate {i}:\n")
                    f.write(f"  Original Error Fixed: {eval_info['original_error_fixed']}\n")
                    f.write(f"  New Errors: {eval_info['new_errors_count']}\n")
                    f.write(f"  Total Errors: {eval_info['total_errors']}\n")
                    f.write(f"  Compilation: {eval_info['compilation_status']}\n")

                    if eval_info["original_error_fixed"] and eval_info["new_errors_count"] == 0:
                        f.write("  Status: ✅ SUCCESS\n")
                        successful_candidates += 1
                    elif eval_info["original_error_fixed"]:
                        f.write("  Status: ⚠️  PARTIAL\n")
                        partial_candidates += 1
                    else:
                        f.write("  Status: ❌ FAILED\n")
                        failed_candidates += 1

                    if eval_info["error_details"]:
                        f.write("  Error Details:\n")
                        for detail in eval_info["error_details"][:3]:
                            f.write(f"    - {detail}\n")
                        if len(eval_info["error_details"]) > 3:
                            f.write(f"    ... and {len(eval_info['error_details']) - 3} more\n")
                    f.write("\n")

                f.write("OVERALL RESULTS:\n")
                f.write(f"  Successful: {successful_candidates}/{len(candidate_evaluations)}\n")
                f.write(f"  Partial: {partial_candidates}/{len(candidate_evaluations)}\n")
                f.write(f"  Failed: {failed_candidates}/{len(candidate_evaluations)}\n")
                f.write("\n")

        # Save full candidates with error evaluation
        if result.candidates:
            for i, candidate in enumerate(result.candidates, 1):
                candidate_file = output_dir / f"{base_filename}_candidate_{i}.rs"
                eval_info = (
                    candidate_evaluations[i - 1] if i - 1 < len(candidate_evaluations) else {}
                )

                with open(candidate_file, "w") as f:
                    f.write(f"// Generated by {action_type.value}\n")
                    f.write(f"// Candidate {i} of {len(result.candidates)}\n")
                    f.write(f"// Timestamp: {timestamp}\n")
                    f.write("//\n")
                    f.write("// ERROR EVALUATION:\n")
                    f.write(
                        f"// Original Error Fixed: {eval_info.get('original_error_fixed', 'Unknown')}\n"
                    )
                    f.write(
                        f"// New Errors Introduced: {eval_info.get('new_errors_count', 'Unknown')}\n"
                    )
                    f.write(f"// Total Errors: {eval_info.get('total_errors', 'Unknown')}\n")
                    f.write(
                        f"// Compilation Status: {eval_info.get('compilation_status', 'Unknown')}\n"
                    )

                    if eval_info.get("error_details"):
                        f.write("// Error Details:\n")
                        for detail in eval_info["error_details"][:3]:
                            f.write(f"//   - {detail}\n")
                        if len(eval_info["error_details"]) > 3:
                            f.write(f"//   ... and {len(eval_info['error_details']) - 3} more\n")

                    # Overall status
                    if (
                        eval_info.get("original_error_fixed")
                        and eval_info.get("new_errors_count", 0) == 0
                    ):
                        f.write("// STATUS: ✅ SUCCESS - Fixed original error with no new errors\n")
                    elif eval_info.get("original_error_fixed"):
                        f.write(
                            "// STATUS: ⚠️  PARTIAL - Fixed original error but introduced new errors\n"
                        )
                    else:
                        f.write("// STATUS: ❌ FAILED - Original error not fixed\n")

                    f.write("//\n\n")
                    f.write(candidate)

        print("\n[INFO] Detailed output saved to:")
        print(f"  Summary: {summary_file}")
        if result.candidates:
            print(f"  Candidates: {len(result.candidates)} files in {output_dir}/")
            # Show quick summary of results
            if candidate_evaluations:
                successful = sum(
                    1
                    for eval_info in candidate_evaluations
                    if eval_info["original_error_fixed"] and eval_info["new_errors_count"] == 0
                )
                print(
                    f"  Success rate: {successful}/{len(candidate_evaluations)} candidates fixed the error completely"
                )

    def interactive_test(self):
        """Enhanced interactive testing mode"""
        print("=== ACTION DEBUG INTERACTIVE MODE ===")
        print("Available actions:")

        actions = list(ActionType)
        for i, action in enumerate(actions, 1):
            print(f"{i:2d}. {action.value}")

        while True:
            try:
                print("\n" + "=" * 60)
                choice = input(f"Select action (1-{len(actions)}) or 'q' to quit: ").strip()
                if choice.lower() == "q":
                    break

                action_idx = int(choice) - 1
                if 0 <= action_idx < len(actions):
                    action_type = actions[action_idx]

                    print(f"\n--- Testing {action_type.value.upper()} ---")

                    # Ask for custom code
                    print("\nCode source options:")
                    print("  1. Use default sample code")
                    print("  2. Load from file")
                    print("  3. Enter code manually")

                    code_choice = input("Choice (1-3): ").strip()
                    observation = None

                    if code_choice == "2":
                        # Load from file
                        file_path = input("Enter file path: ").strip()
                        if file_path:
                            try:
                                observation = self.create_sample_observation(code_file=file_path)
                            except Exception as e:
                                print(f"Error loading file: {e}")
                                print("Using default sample code instead.")

                    elif code_choice == "3":
                        # Manual input
                        print("Enter your code (end with '###' on a new line):")
                        code_lines = []
                        while True:
                            line = input()
                            if line.strip() == "###":
                                break
                            code_lines.append(line)

                        custom_code = "\n".join(code_lines)
                        if custom_code.strip():
                            observation = self.create_sample_observation(code=custom_code)

                    # Create observation using real VEval
                    if observation is None:
                        observation = self.create_sample_observation()

                    if observation is None:
                        print("Failed to create observation. Please check your code.")
                        continue

                    # Ask for custom guidance
                    guidance = input("Enter custom guidance (or press Enter for default): ").strip()
                    params = {"guidance": guidance} if guidance else None

                    # Ask for options
                    verbose = input("Verbose output? (y/n): ").strip().lower() == "y"
                    save_output = (
                        input("Save detailed output to files? (y/n): ").strip().lower() == "y"
                    )

                    print(f"\n{'='*60}")
                    print(f"EXECUTING {action_type.value.upper()}")
                    print(f"{'='*60}")

                    # Test the action
                    result = self.test_action(
                        action_type, observation, params, verbose=verbose, save_output=save_output
                    )

                    if result:
                        print(f"\n{'='*60}")
                        print("EXECUTION COMPLETED")
                        print(f"{'='*60}")

                        # Ask if user wants to continue
                        continue_choice = input("\nTest another action? (y/n): ").strip().lower()
                        if continue_choice != "y":
                            break
                    else:
                        print("Execution failed. Please check your configuration.")
                        break

                else:
                    print("Invalid choice!")

            except (ValueError, KeyboardInterrupt):
                print("\nExiting...")
                break

    def run_sample_tests(self):
        """Run a few sample tests with real VEval errors"""
        print("=== RUNNING SAMPLE TESTS WITH REAL AZURE OPENAI AND REAL VERUS ERRORS ===")

        # Test 1: Assertion failure
        print("\n" + "=" * 80)
        print("SAMPLE TEST 1: ASSERTION FAILURE")

        assertion_code = """
verus! {
fn test_function(x: i32, y: i32) -> i32
    requires x > 0 && y > 0
    ensures result >= 0
{
    let result = x + y;
    assert(result > x);  // This assertion will fail
    result
}
}
        """.strip()

        obs1 = self.create_sample_observation(code=assertion_code)
        if obs1:
            # Let VEval determine the action type based on the actual error
            action_type = self._determine_action_type_from_error(obs1.error)
            self.test_action(action_type, obs1)
        else:
            print("Could not create observation from assertion code")

        # Test 2: Postcondition failure
        print("\n" + "=" * 80)
        print("SAMPLE TEST 2: POSTCONDITION FAILURE")

        postcond_code = """
verus! {
fn add_positive(x: i32, y: i32) -> i32
    requires x > 0 && y > 0
    ensures result > x + y  // This postcondition is too strong
{
    x + y
}
}
        """.strip()

        obs2 = self.create_sample_observation(code=postcond_code)
        if obs2:
            action_type = self._determine_action_type_from_error(obs2.error)
            self.test_action(action_type, obs2)
        else:
            print("Could not create observation from postcondition code")

        # Test 3: Use test_example.rs file if available
        print("\n" + "=" * 80)
        print("SAMPLE TEST 3: FROM test_example.rs FILE")

        obs3 = self.create_sample_observation(code_file="test_example.rs")
        if obs3:
            action_type = self._determine_action_type_from_error(obs3.error)
            self.test_action(action_type, obs3)
        else:
            print("Could not load or create observation from test_example.rs")

    def _determine_action_type_from_error(self, error) -> ActionType:
        """Determine the most appropriate action type based on the actual error"""
        if hasattr(error, "error"):
            error_type = error.error

            # Map error types to action types
            if error_type == VerusErrorType.AssertFail:
                return ActionType.ADD_TRIGGER_ASSERT  # Good default for assertion failures
            elif error_type == VerusErrorType.PostCondFail:
                return ActionType.POSTCONDITION_REPAIR
            elif error_type == VerusErrorType.PreCondFail:
                return ActionType.PRECONDITION_REPAIR
            elif error_type == VerusErrorType.InvFailEnd:
                return ActionType.INVARIANT_END_REPAIR
            elif error_type == VerusErrorType.InvFailFront:
                return ActionType.INVARIANT_FRONT_REPAIR
            elif error_type == VerusErrorType.MismatchedType:
                return ActionType.TYPE_REPAIR
            elif error_type == VerusErrorType.ArithmeticFlow:
                return ActionType.ARITHMETIC_OVERFLOW_REPAIR
            else:
                return ActionType.FALLBACK_LLM_REPAIR

        # Default fallback
        return ActionType.ADD_TRIGGER_ASSERT

    def list_all_actions(self):
        """List all available actions with their metadata"""
        print("=== ALL AVAILABLE ACTIONS ===")

        for action_type in ActionType:
            try:
                metadata = action_registry.get_action_metadata(action_type)
                print(f"\n{action_type.value.upper()}")
                print(f"  Description: {metadata['description']}")
                print(f"  When to apply: {metadata['when_to_apply']}")
                print(f"  Guidance: {metadata['guidance_template']}")
                print(f"  Acceptance: {metadata['acceptance_criteria']}")
            except Exception as e:
                print(f"\n{action_type.value.upper()}: Error getting metadata - {e}")


def create_argument_parser():
    """Create and configure the argument parser"""
    import argparse

    parser = argparse.ArgumentParser(
        description="Debug script for testing individual actions with real Azure OpenAI APIs and Verus error evaluation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Interactive mode (default when no action specified)
    python debug.py
    python debug.py --config your_config.json

    # List all available actions
    python debug.py --list

    # Run sample tests
    python debug.py --samples --config your_config.json

    # Test specific action
    python debug.py --test add_trigger_assert --config your_config.json
    python debug.py --test type_repair --config your_config.json --file my_code.rs --verbose --save

    # All options
    python debug.py --test postcondition_repair --config your_config.json --file /path/to/verus_file.rs --verbose --save

Note: This script requires a valid Azure OpenAI configuration file to function.
      Required config fields: aoai_api_key, aoai_endpoint, aoai_api_version, verus_path
        """,
    )

    # Main action arguments (mutually exclusive)
    action_group = parser.add_mutually_exclusive_group()
    action_group.add_argument(
        "--test",
        metavar="ACTION",
        help="Test a specific action (e.g., add_trigger_assert, type_repair)",
    )
    action_group.add_argument(
        "--samples", action="store_true", help="Run sample tests with real Verus errors"
    )
    action_group.add_argument(
        "--list", action="store_true", help="List all available actions with descriptions"
    )

    # Configuration
    parser.add_argument(
        "--config",
        metavar="PATH",
        help="Path to configuration file (JSON or Python). Required for most operations.",
    )

    # Code input
    parser.add_argument(
        "--file", metavar="PATH", help="Load code from specified file (supports .rs, .verus, .txt)"
    )

    # Output options
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Show detailed execution info and complete candidate outputs",
    )
    parser.add_argument(
        "--save", action="store_true", help="Save detailed results to debug_output/ directory"
    )

    return parser


def main():
    """Main entry point using argparse"""
    parser = create_argument_parser()
    args = parser.parse_args()

    # Handle --list action (doesn't require config)
    if args.list:
        ActionDebugger.list_all_actions()
        return

    # For other actions, we need config (except interactive mode can help select one)
    config = None
    if args.config:
        config = ActionDebugger.load_config_from_file(args.config)
        if config is None:
            print(f"ERROR: Failed to load config from {args.config}")
            return

    # Handle different modes
    if args.samples:
        # Samples mode requires config
        if not config:
            print("ERROR: --samples requires --config CONFIG_FILE")
            print("Available config files:")
            config_files = ActionDebugger.find_config_files()
            if config_files:
                for i, cf in enumerate(config_files, 1):
                    print(f"  {i}. {cf}")
                print("\nUse: python debug.py --samples --config CONFIG_FILE")
            else:
                print("  No config*.json files found. Please create a configuration file.")
            return

        debugger = ActionDebugger(config)
        debugger.run_sample_tests()

    elif args.test:
        # Test mode requires config
        if not config:
            print("ERROR: --test requires --config CONFIG_FILE")
            print("Available config files:")
            config_files = ActionDebugger.find_config_files()
            if config_files:
                for i, cf in enumerate(config_files, 1):
                    print(f"  {i}. {cf}")
                print(f"\nUse: python debug.py --test {args.test} --config CONFIG_FILE")
            else:
                print("  No config*.json files found. Please create a configuration file.")
            return

        debugger = ActionDebugger(config)

        # Find matching action
        action_type = None
        for at in ActionType:
            if at.value == args.test.lower() or at.name.lower() == args.test.lower():
                action_type = at
                break

        if action_type:
            debugger.test_action(
                action_type, code_file=args.file, verbose=args.verbose, save_output=args.save
            )
        else:
            print(f"ERROR: Action not found: {args.test}")
            print("Available actions:")
            for at in ActionType:
                print(f"  {at.value}")

    else:
        # Interactive mode (default)
        print("=== ACTION DEBUG INTERACTIVE MODE ===")

        if config:
            # Config was provided via --config, use it directly
            print(f"Using config: {args.config}")
            debugger = ActionDebugger(config)
            debugger.interactive_test()
        else:
            # No config provided, help user select one
            config = ActionDebugger.select_config_interactively()
            if config is None:
                print("Cannot proceed without configuration.")
                return

            debugger = ActionDebugger(config)
            debugger.interactive_test()


if __name__ == "__main__":
    main()
