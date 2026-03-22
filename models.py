"""
Data models for paper downloader.
"""

from dataclasses import dataclass, asdict
from typing import Optional


@dataclass
class Paper:
    """Represents an academic paper."""
    title: str
    authors: str
    year: int
    doi: Optional[str] = None
    journal: Optional[str] = None
    abstract: Optional[str] = None
    url: Optional[str] = None
    pdf_url: Optional[str] = None
    database: Optional[str] = None
    topic: Optional[str] = None
    bibtex_raw: Optional[str] = None
    bibtex_key: Optional[str] = None

    def to_dict(self) -> dict:
        """Convert to dictionary, excluding None values."""
        return {k: v for k, v in asdict(self).items() if v is not None}
