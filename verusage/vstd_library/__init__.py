"""
vstd Library Integration Module

This module provides tools to parse, index, and search the Verus standard library (vstd).
It enables LLM-driven retrieval of relevant library content for verification tasks.

Components:
- parser: Extract structured information from vstd .rs files
- indexer: Build searchable index of vstd content
- search_engine: Multi-modal search for relevant vstd functions
- query_generator: LLM generates search queries from error context
- result_formatter: Format search results for LLM consumption
"""

from .indexer import VstdIndexer
from .parser import VstdFunction, VstdOpenSpec, VstdParser
from .query_generator import QueryGenerator
from .result_formatter import ResultFormatter
from .search_engine import SearchQuery, SearchResult, VstdSearchEngine

__all__ = [
    "VstdParser",
    "VstdFunction",
    "VstdOpenSpec",
    "VstdIndexer",
    "VstdSearchEngine",
    "SearchQuery",
    "SearchResult",
    "QueryGenerator",
    "ResultFormatter",
]

__version__ = "0.1.0"
