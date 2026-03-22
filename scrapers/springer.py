"""
SpringerLink scraper.
"""

import re
from typing import List, Optional
from urllib.parse import quote_plus

from playwright.async_api import Page

from config import to_ezproxy_url
from models import Paper
from .base import BaseScraper


class SpringerScraper(BaseScraper):
    """Scraper for SpringerLink."""

    def __init__(self, page: Page, config: dict):
        super().__init__(page, config)
        self.name = "springer"
        self.base_url = "https://link.springer.com"

    async def search(self, query: str, max_results: int) -> List[Paper]:
        """Search SpringerLink via ezproxy."""
        search_url = f"{self.base_url}/search?query={quote_plus(query)}"
        ezproxy_url = to_ezproxy_url(search_url)

        await self.page.goto(ezproxy_url, wait_until='load', timeout=30000)
        await self.random_delay()

        papers = []

        try:
            # Wait for results
            await self.page.wait_for_selector('.app-card-open, .search-result-item', timeout=15000)

            # Get result items
            items = await self.page.query_selector_all('.app-card-open, .search-result-item')

            for i, item in enumerate(items[:max_results]):
                try:
                    # Extract title
                    title_elem = await item.query_selector('h3 a, .title a')
                    title = await title_elem.inner_text() if title_elem else ""
                    title = title.strip()

                    if not title:
                        continue

                    # Extract authors
                    authors_elem = await item.query_selector('.app-card-open__author-list, .authors')
                    authors = await authors_elem.inner_text() if authors_elem else ""
                    authors = authors.strip().replace('\n', ', ')

                    # Extract year
                    year_text = await item.inner_text()
                    year_match = re.search(r'\b(20\d{2}|19\d{2})\b', year_text)
                    year = int(year_match.group(1)) if year_match else None

                    # Extract journal/source
                    journal_elem = await item.query_selector('.app-card-open__meta-item, .source')
                    journal = await journal_elem.inner_text() if journal_elem else None

                    # Get article URL and DOI (already proxied via ezproxy)
                    article_url = None
                    doi = None
                    link_elem = await item.query_selector('h3 a, .title a')
                    if link_elem:
                        article_url = await link_elem.get_attribute('href')
                        if article_url and not article_url.startswith('http'):
                            article_url = to_ezproxy_url(f"{self.base_url}{article_url}")
                        # Extract DOI from URL
                        if article_url and '/article/' in article_url:
                            doi_match = re.search(r'/article/([^/]+)', article_url)
                            if doi_match:
                                doi = f"10.1007/{doi_match.group(1)}"

                    # Try to find PDF link
                    pdf_url = None
                    pdf_btn = await item.query_selector('a[href*="pdf"], a[href*=".pdf"], .pdf-link')
                    if pdf_btn:
                        href = await pdf_btn.get_attribute('href')
                        if href:
                            if href.startswith('http'):
                                pdf_url = href
                            else:
                                pdf_url = to_ezproxy_url(f"{self.base_url}{href}")

                    paper = Paper(
                        title=title,
                        authors=authors,
                        year=year,
                        doi=doi,
                        journal=journal,
                        url=article_url,
                        pdf_url=pdf_url,
                        database=self.name
                    )
                    papers.append(paper)

                except Exception as e:
                    print(f"  [WARN] Error parsing Springer result {i+1}: {e}")
                    continue

        except Exception as e:
            print(f"  [ERROR] Springer search failed: {e}")

        return papers

    async def get_bibtex(self, paper: Paper) -> Optional[str]:
        """Get BibTeX from Springer."""
        return None
