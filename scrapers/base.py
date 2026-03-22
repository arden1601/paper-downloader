"""
Base scraper class for academic databases.
"""

import asyncio
import random
import re
from abc import ABC, abstractmethod
from pathlib import Path
from typing import List, Optional

from playwright.async_api import Page

from config import to_ezproxy_url
from models import Paper


class BaseScraper(ABC):
    """Abstract base class for database scrapers."""

    def __init__(self, page: Page, config: dict):
        self.page = page
        self.config = config
        self.name = "base"

    async def random_delay(self):
        """Add random delay between requests."""
        delay_min = self.config['download']['delay_min']
        delay_max = self.config['download']['delay_max']
        await asyncio.sleep(random.uniform(delay_min, delay_max))

    async def wait_for_selector(self, selector: str, timeout: int = 10000) -> bool:
        """Wait for selector with error handling."""
        try:
            await self.page.wait_for_selector(selector, timeout=timeout)
            return True
        except:
            return False

    @abstractmethod
    async def search(self, query: str, max_results: int) -> List[Paper]:
        """Search for papers. Must be implemented by subclasses."""
        pass

    @abstractmethod
    async def get_bibtex(self, paper: Paper) -> Optional[str]:
        """Get BibTeX citation for paper."""
        pass

    async def download_pdf(self, paper: Paper, download_dir: Path) -> Optional[str]:
        """Download PDF for paper. Returns file path or None."""
        if not paper.pdf_url:
            return None

        try:
            # Create download directory
            download_dir.mkdir(parents=True, exist_ok=True)

            # Generate safe filename
            safe_title = re.sub(r'[^\w\s-]', '', paper.title)
            safe_title = re.sub(r'[-\s]+', '_', safe_title)[:80]
            filename = f"{safe_title}.pdf"
            filepath = download_dir / filename

            # Check if this is a ScienceDirect /pdfft URL
            is_pdfft_url = '/pdfft' in paper.pdf_url.lower()

            if is_pdfft_url:
                # ScienceDirect /pdfft endpoint - navigate to it, triggers PDF download
                async with self.page.expect_download(timeout=60000) as download_info:
                    await self.page.goto(paper.pdf_url, wait_until='load', timeout=60000)
                download = await download_info.value
            elif '.pdf' in paper.pdf_url.lower():
                # Direct PDF URL
                async with self.page.expect_download(timeout=60000) as download_info:
                    await self.page.goto(paper.pdf_url, wait_until='load', timeout=60000)
                download = await download_info.value
            else:
                # Try to click download button
                async with self.page.expect_download(timeout=60000) as download_info:
                    await self.page.click(f'a[href*="{paper.pdf_url}"]', timeout=10000)
                download = await download_info.value

            await download.save_as(filepath)
            return str(filepath)
        except Exception as e:
            print(f"  [WARN] PDF download failed: {e}")
            return None
