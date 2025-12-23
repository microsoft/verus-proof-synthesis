"""
Global Configuration Module
Provides singleton access to configuration, logger, LLM, and shared resources.
This eliminates the need to pass refinement_engine throughout the codebase.
"""

from pathlib import Path
from typing import Any, Optional

from houdini import houdini
from infer import LLM


class GlobalConfig:
    """
    Singleton for global configuration and shared resources.

    All components (agents, actions, repairs) should access configuration
    and shared resources through this class instead of holding references
    to the refinement engine.

    Usage:
        # Initialize once at startup in main.py
        GlobalConfig.initialize(config, logger)

        # Access anywhere in the codebase
        config = GlobalConfig.get_config()
        logger = GlobalConfig.get_logger()
        llm = GlobalConfig.get_llm()
    """

    _instance: Optional["GlobalConfig"] = None
    _initialized: bool = False

    def __init__(self):
        """Private constructor - use GlobalConfig.initialize() instead"""
        self.config = None
        self.logger = None
        self.llm = None
        self.houdini_instance = None
        self.repair_modules = {}

        # Directory paths
        self.temp_dir: Path | None = None
        self.llm_prompt_dir: Path | None = None

        # Metadata store for repair attempts
        self.metadata_store = None

    @classmethod
    def initialize(cls, config, logger, temp_dir: Path | None = None) -> "GlobalConfig":
        """
        Initialize the global configuration singleton.
        Should be called once at application startup.

        Args:
            config: Configuration dictionary or AttrDict
            logger: Logger instance (e.g., loguru logger)
            temp_dir: Optional temporary directory for outputs (defaults to "temp-output-dir")

        Returns:
            The GlobalConfig instance
        """
        if cls._instance is None:
            cls._instance = cls()

        cls._instance.config = config
        cls._instance.logger = logger
        cls._instance.llm = LLM(config, logger)
        cls._instance.houdini_instance = houdini(config)

        # Set up directory structure under temp_dir
        cls._instance.temp_dir = Path(temp_dir) if temp_dir else Path("temp-output-dir")
        cls._instance.llm_prompt_dir = cls._instance.temp_dir / "llm-prompts"

        # Create directories
        cls._instance.temp_dir.mkdir(parents=True, exist_ok=True)
        cls._instance.llm_prompt_dir.mkdir(parents=True, exist_ok=True)

        # Initialize metadata store
        from agents.repair_metadata import MetadataStore

        cls._instance.metadata_store = MetadataStore()

        cls._initialized = True

        logger.info("Global configuration initialized")
        logger.info(f"  Temp directory: {cls._instance.temp_dir}")
        logger.info(f"    - LLM prompts: {cls._instance.llm_prompt_dir}")
        logger.info("  Metadata store initialized")
        return cls._instance

    @classmethod
    def get(cls) -> "GlobalConfig":
        """
        Get the global configuration instance.

        Returns:
            The GlobalConfig singleton instance

        Raises:
            RuntimeError: If GlobalConfig has not been initialized
        """
        if not cls._initialized or cls._instance is None:
            raise RuntimeError(
                "GlobalConfig not initialized. Call GlobalConfig.initialize(config, logger) first."
            )
        return cls._instance

    @classmethod
    def is_initialized(cls) -> bool:
        """Check if GlobalConfig has been initialized"""
        return cls._initialized and cls._instance is not None

    # Convenience accessors for common resources

    @classmethod
    def get_config(cls):
        """Get the configuration dictionary/AttrDict"""
        return cls.get().config

    @classmethod
    def get_logger(cls):
        """Get the logger instance"""
        return cls.get().logger

    @classmethod
    def get_llm(cls) -> LLM:
        """Get the LLM instance"""
        return cls.get().llm

    @classmethod
    def get_houdini(cls):
        """Get the Houdini instance"""
        return cls.get().houdini_instance

    # Directory accessors

    @classmethod
    def get_temp_dir(cls) -> Path:
        """Get the temporary output directory"""
        return cls.get().temp_dir

    @classmethod
    def set_temp_dir(cls, temp_dir: Path):
        """
        Set a new temporary directory (and create subdirectories).

        Args:
            temp_dir: Path to the new temporary directory
        """
        instance = cls.get()
        instance.temp_dir = Path(temp_dir)
        instance.llm_prompt_dir = instance.temp_dir / "llm-prompts"

        # Create directories
        instance.temp_dir.mkdir(parents=True, exist_ok=True)
        instance.llm_prompt_dir.mkdir(parents=True, exist_ok=True)

        instance.logger.info(f"Temp directory updated to: {instance.temp_dir}")

    @classmethod
    def get_llm_prompt_dir(cls) -> Path:
        """Get the LLM prompt logging directory (subdirectory of temp_dir)"""
        return cls.get().llm_prompt_dir

    # Metadata store accessors

    @classmethod
    def get_metadata_store(cls):
        """
        Get the global metadata store for repair attempts.

        The metadata store provides centralized tracking of all repair attempts,
        eliminating the need to pass metadata dicts back and forth.

        Returns:
            MetadataStore instance

        Example:
            store = GlobalConfig.get_metadata_store()
            store.add_attempt(metadata)
            recent = store.get_recent_attempts(n=5)
        """
        return cls.get().metadata_store

    @classmethod
    def reset_metadata_store(cls):
        """
        Reset the metadata store, clearing all tracked attempts.

        This should be called at the start of a new repair session.
        """
        from agents.repair_metadata import MetadataStore

        cls.get().metadata_store = MetadataStore()
        cls.get().logger.info("Metadata store reset")

    @classmethod
    def register_repair_module(cls, name: str, module: Any):
        """
        Register a repair module for global access.

        Args:
            name: Name of the repair module (e.g., 'assertion_repairs', 'precondition_repairs')
            module: The repair module instance
        """
        cls.get().repair_modules[name] = module
        cls.get().logger.info(f"Registered repair module: {name}")

    @classmethod
    def get_repair_module(cls, name: str) -> Any | None:
        """
        Get a registered repair module by name.

        Args:
            name: Name of the repair module

        Returns:
            The repair module instance, or None if not found
        """
        return cls.get().repair_modules.get(name)

    @classmethod
    def get_all_repair_modules(cls) -> dict[str, Any]:
        """Get all registered repair modules"""
        return cls.get().repair_modules

    @classmethod
    def reset(cls):
        """
        Reset the global configuration.
        Primarily useful for testing.
        """
        if cls._instance and cls._instance.metadata_store:
            cls._instance.metadata_store.clear()
        cls._instance = None
        cls._initialized = False


# Convenience functions for backward compatibility and ease of use
def get_config():
    """Shorthand for GlobalConfig.get_config()"""
    return GlobalConfig.get_config()


def get_logger():
    """Shorthand for GlobalConfig.get_logger()"""
    return GlobalConfig.get_logger()


def get_llm():
    """Shorthand for GlobalConfig.get_llm()"""
    return GlobalConfig.get_llm()


def get_houdini():
    """Shorthand for GlobalConfig.get_houdini()"""
    return GlobalConfig.get_houdini()


def get_temp_dir():
    """Shorthand for GlobalConfig.get_temp_dir()"""
    return GlobalConfig.get_temp_dir()


def get_llm_prompt_dir():
    """Shorthand for GlobalConfig.get_llm_prompt_dir()"""
    return GlobalConfig.get_llm_prompt_dir()


def get_metadata_store():
    """Shorthand for GlobalConfig.get_metadata_store()"""
    return GlobalConfig.get_metadata_store()
