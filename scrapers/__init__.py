"""
Scrapers module for academic databases.
"""

from .base import BaseScraper
from .ieee import IEEEScraper
from .sciencedirect import ScienceDirectScraper
from .springer import SpringerScraper

__all__ = [
    'BaseScraper',
    'IEEEScraper',
    'ScienceDirectScraper',
    'SpringerScraper',
]
