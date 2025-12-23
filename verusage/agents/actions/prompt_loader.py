"""
Prompt Loader Utility
Loads instruction prompts from markdown files in the prompts directory.
"""

from pathlib import Path


class PromptLoader:
    """Utility class to load prompts from markdown files"""

    def __init__(self, prompts_dir: str | None = None):
        """Initialize the prompt loader

        Args:
            prompts_dir: Path to the prompts directory. If None, uses the default prompts directory.
        """
        if prompts_dir is None:
            # Default to prompts directory at agents level
            current_dir = Path(__file__).parent.parent  # Go up to agents directory
            self.prompts_dir = current_dir / "prompts"
        else:
            self.prompts_dir = Path(prompts_dir)

        # Cache for loaded prompts
        self._prompt_cache: dict[str, str] = {}

    def load_prompt(self, prompt_name: str) -> str:
        """Load a prompt from a markdown file

        Args:
            prompt_name: Name of the prompt file (without .md extension)

        Returns:
            The prompt content as a string

        Raises:
            FileNotFoundError: If the prompt file doesn't exist
        """
        # Check cache first
        if prompt_name in self._prompt_cache:
            return self._prompt_cache[prompt_name]

        # Construct file path
        prompt_file = self.prompts_dir / f"{prompt_name}.md"

        if not prompt_file.exists():
            raise FileNotFoundError(f"Prompt file not found: {prompt_file}")

        # Load and cache the prompt
        with open(prompt_file, encoding="utf-8") as f:
            content = f.read().strip()

        self._prompt_cache[prompt_name] = content
        return content

    def format_prompt(self, prompt_name: str, **kwargs) -> str:
        """Load and format a prompt with variables

        Args:
            prompt_name: Name of the prompt file
            **kwargs: Variables to substitute in the prompt

        Returns:
            The formatted prompt content
        """
        prompt = self.load_prompt(prompt_name)
        return prompt.format(**kwargs)

    def clear_cache(self):
        """Clear the prompt cache"""
        self._prompt_cache.clear()

    def list_available_prompts(self) -> list:
        """List all available prompt files

        Returns:
            List of prompt names (without .md extension)
        """
        if not self.prompts_dir.exists():
            return []

        return [f.stem for f in self.prompts_dir.glob("*.md")]


# Global instance for easy access
_prompt_loader = PromptLoader()


def load_prompt(prompt_name: str) -> str:
    """Convenience function to load a prompt

    Args:
        prompt_name: Name of the prompt file (without .md extension)

    Returns:
        The prompt content as a string
    """
    return _prompt_loader.load_prompt(prompt_name)


def format_prompt(prompt_name: str, **kwargs) -> str:
    """Convenience function to load and format a prompt

    Args:
        prompt_name: Name of the prompt file
        **kwargs: Variables to substitute in the prompt

    Returns:
        The formatted prompt content
    """
    return _prompt_loader.format_prompt(prompt_name, **kwargs)
