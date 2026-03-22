"""
IEEE Xplore scraper.
"""

import re
from typing import List, Optional
from urllib.parse import quote_plus

from playwright.async_api import Page

from config import to_ezproxy_url
from models import Paper
from .base import BaseScraper


class IEEEScraper(BaseScraper):
    """Scraper for IEEE Xplore."""

    def __init__(self, page: Page, config: dict):
        super().__init__(page, config)
        self.name = "ieee"
        self.base_url = "https://ieeexplore.ieee.org"

    async def search(self, query: str, max_results: int) -> List[Paper]:
        """Search IEEE Xplore via ezproxy."""
        # Build ezproxy-proxied URL
        search_url = f"{self.base_url}/search/searchresult.jsp?newsearch=true&queryText={quote_plus(query)}"
        ezproxy_url = to_ezproxy_url(search_url)

        await self.page.goto(ezproxy_url, wait_until='load', timeout=30000)
        await self.random_delay()

        papers = []

        try:
            # Wait for results
            await self.page.wait_for_selector('.List-results-items, .result-item', timeout=15000)

            # Get result items
            items = await self.page.query_selector_all('.List-results-items, .result-item')

            for i, item in enumerate(items[:max_results]):
                try:
                    # Extract title
                    title_elem = await item.query_selector('h2 a, .result-item h3 a')
                    title = await title_elem.inner_text() if title_elem else ""
                    title = title.strip()

                    if not title:
                        continue

                    # Extract authors
                    authors_elem = await item.query_selector('.author, .author-name')
                    authors = await authors_elem.inner_text() if authors_elem else ""
                    authors = authors.strip().replace('\n', ', ')

                    # Extract year
                    year_text = await item.inner_text()
                    year_match = re.search(r'\b(20\d{2}|19\d{2})\b', year_text)
                    year = int(year_match.group(1)) if year_match else None

                    # Extract DOI
                    doi = None
                    doi_elem = await item.query_selector('[data-doi]')
                    if doi_elem:
                        doi = await doi_elem.get_attribute('data-doi')

                    # Get article URL (already proxied via ezproxy)
                    article_url = None
                    link_elem = await item.query_selector('h2 a, h3 a')
                    if link_elem:
                        article_url = await link_elem.get_attribute('href')
                        if article_url and not article_url.startswith('http'):
                            article_url = to_ezproxy_url(f"{self.base_url}{article_url}")

                    # Try to find PDF link
                    pdf_url = None
                    pdf_btn = await item.query_selector('a[href*="pdf"], a[href*=".pdf"], .pdf-download')
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
                        url=article_url,
                        pdf_url=pdf_url,
                        database=self.name
                    )
                    papers.append(paper)

                except Exception as e:
                    print(f"  [WARN] Error parsing IEEE result {i+1}: {e}")
                    continue

        except Exception as e:
            print(f"  [ERROR] IEEE search failed: {e}")

        return papers

    async def get_bibtex(self, paper: Paper) -> Optional[str]:
        """Get BibTeX from IEEE."""
        return None
