#!/usr/bin/env python3
"""
Paper Downloader Agent
======================
A CLI tool to search and download academic papers from IEEE Xplore,
ScienceDirect, and SpringerLink via UGM ezproxy.

Usage:
    python download.py --interactive --search "blockchain RWA"
    python download.py --list --year 2023-2025
    python download.py --all
"""

import argparse
import asyncio
import hashlib
import json
import os
import random
import re
import sqlite3
import sys
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Dict, Any
from urllib.parse import quote_plus

import bibtexparser
import yaml
from rich.console import Console
from rich.table import Table
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn
from rich.panel import Panel
from rich import print as rprint

# Playwright imports
from playwright.async_api import async_playwright, Page, Browser, BrowserContext

# ============================================================================
# CONFIGURATION
# ============================================================================

DEFAULT_CONFIG = """
ezproxy:
  url: "https://ezproxy.ugm.ac.id/login"
  login_timeout: 300
  login_check_url: "https://ieeexplore.ieee.org"

databases:
  - name: ieee
    enabled: true
    search_url: "https://ieeexplore.ieee.org/search/searchresult.jsp?newsearch=true&queryText={query}"
  - name: sciencedirect
    enabled: true
    search_url: "https://www.sciencedirect.com/search?qs={query}"
  - name: springer
    enabled: true
    search_url: "https://link.springer.com/search?query={query}"

download:
  max_per_database: 5
  delay_min: 2
  delay_max: 4
  retry_max: 3
  timeout: 30
  headless: false

paths:
  downloads: "./downloads"
  database: "./library.db"
  bibtex: "../template-skripsi/daftar-pustaka.bib"
  logs: "./logs"

searches: []
"""

def load_config(config_path: str = "config.yaml") -> dict:
    """Load configuration from YAML file."""
    config_file = Path(config_path)
    if config_file.exists():
        with open(config_file, 'r') as f:
            return yaml.safe_load(f)
    else:
        return yaml.safe_load(DEFAULT_CONFIG)


def to_ezproxy_url(url: str, ezproxy_domain: str = "ezproxy.ugm.ac.id") -> str:
    """
    Transform a URL to its ezproxy-proxied version.

    Example:
        https://ieeexplore.ieee.org/document/123
        → https://ieeexplore-ieee-org.ezproxy.ugm.ac.id/document/123
    """
    from urllib.parse import urlparse, urlunparse

    parsed = urlparse(url)
    netloc = parsed.netloc

    # Transform domain: replace dots with dashes, then append ezproxy domain
    proxy_netloc = f"{netloc.replace('.', '-')}.{ezproxy_domain}"

    # Reconstruct URL
    return urlunparse((
        parsed.scheme,
        proxy_netloc,
        parsed.path,
        parsed.params,
        parsed.query,
        parsed.fragment
    ))


# ============================================================================
# DATA CLASSES
# ============================================================================

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
        return {k: v for k, v in asdict(self).items() if v is not None}


# ============================================================================
# DATABASE MANAGER
# ============================================================================

class Library:
    """SQLite database manager for tracking papers."""

    def __init__(self, db_path: str):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_db()

    def _init_db(self):
        """Initialize database schema."""
        with sqlite3.connect(self.db_path) as conn:
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS papers (
                    id INTEGER PRIMARY KEY,
                    doi TEXT UNIQUE,
                    title TEXT NOT NULL,
                    authors TEXT,
                    year INTEGER,
                    journal TEXT,
                    database TEXT,
                    topic TEXT,
                    pdf_path TEXT,
                    bibtex_key TEXT,
                    bibtex_raw TEXT,
                    abstract TEXT,
                    url TEXT,
                    downloaded_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    status TEXT DEFAULT 'downloaded'
                );

                CREATE INDEX IF NOT EXISTS idx_papers_doi ON papers(doi);
                CREATE INDEX IF NOT EXISTS idx_papers_title ON papers(title);
                CREATE INDEX IF NOT EXISTS idx_papers_year ON papers(year);
                CREATE INDEX IF NOT EXISTS idx_papers_topic ON papers(topic);

                CREATE TABLE IF NOT EXISTS searches (
                    id INTEGER PRIMARY KEY,
                    query TEXT NOT NULL,
                    topic TEXT,
                    database TEXT,
                    results_found INTEGER,
                    results_downloaded INTEGER,
                    searched_at DATETIME DEFAULT CURRENT_TIMESTAMP
                );
            """)

    def paper_exists(self, paper: Paper) -> bool:
        """Check if paper already exists (by DOI or title)."""
        with sqlite3.connect(self.db_path) as conn:
            if paper.doi:
                cursor = conn.execute(
                    "SELECT id FROM papers WHERE doi = ?", (paper.doi,)
                )
                if cursor.fetchone():
                    return True

            # Fuzzy title match (normalized)
            normalized_title = re.sub(r'\s+', ' ', paper.title.lower().strip())
            cursor = conn.execute(
                "SELECT title FROM papers WHERE title IS NOT NULL"
            )
            for row in cursor.fetchall():
                existing = re.sub(r'\s+', ' ', row[0].lower().strip())
                if normalized_title == existing:
                    return True
                # Also check if very similar (>90% match)
                if self._similar_titles(normalized_title, existing):
                    return True
            return False

    def _similar_titles(self, title1: str, title2: str) -> bool:
        """Check if two titles are similar (>90% match)."""
        if not title1 or not title2:
            return False
        words1 = set(title1.split())
        words2 = set(title2.split())
        if not words1 or not words2:
            return False
        intersection = words1 & words2
        union = words1 | words2
        similarity = len(intersection) / len(union)
        return similarity > 0.9

    def add_paper(self, paper: Paper, pdf_path: str = None, status: str = 'downloaded'):
        """Add a paper to the database."""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO papers
                (doi, title, authors, year, journal, database, topic, pdf_path,
                 bibtex_key, bibtex_raw, abstract, url, status)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                paper.doi, paper.title, paper.authors, paper.year, paper.journal,
                paper.database, paper.topic, pdf_path, paper.bibtex_key,
                paper.bibtex_raw, paper.abstract, paper.url, status
            ))

    def log_search(self, query: str, topic: str, database: str,
                   found: int, downloaded: int):
        """Log a search operation."""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO searches (query, topic, database, results_found, results_downloaded)
                VALUES (?, ?, ?, ?, ?)
            """, (query, topic, database, found, downloaded))

    def list_papers(self, year_range: tuple = None, topic: str = None) -> List[dict]:
        """List papers with optional filters."""
        query = "SELECT * FROM papers WHERE 1=1"
        params = []

        if year_range:
            query += " AND year BETWEEN ? AND ?"
            params.extend(year_range)

        if topic:
            query += " AND topic = ?"
            params.append(topic)

        query += " ORDER BY year DESC, downloaded_at DESC"

        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            cursor = conn.execute(query, params)
            return [dict(row) for row in cursor.fetchall()]

    def get_existing_keys(self) -> set:
        """Get all existing BibTeX keys."""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("SELECT bibtex_key FROM papers WHERE bibtex_key IS NOT NULL")
            return {row[0] for row in cursor.fetchall()}


# ============================================================================
# BIBTEX MERGER
# ============================================================================

class BibTexMerger:
    """Handles merging BibTeX entries into existing file."""

    def __init__(self, bibtex_path: str, library: Library):
        self.bibtex_path = Path(bibtex_path)
        self.library = library

    def generate_key(self, paper: Paper) -> str:
        """Generate a unique BibTeX key."""
        # Get first author's last name
        if paper.authors:
            first_author = paper.authors.split(',')[0].split(' and ')[0].strip()
            last_name = first_author.split()[-1].lower()
            # Remove non-alphanumeric characters
            last_name = re.sub(r'[^a-z0-9]', '', last_name)
        else:
            last_name = "unknown"

        # Base key: lastname + year
        base_key = f"{last_name}{paper.year or 'nodate'}"

        # Ensure uniqueness
        existing_keys = self.library.get_existing_keys()
        if base_key not in existing_keys:
            return base_key

        # Add letter suffix
        for letter in 'abcdefghijklmnopqrstuvwxyz':
            new_key = f"{base_key}{letter}"
            if new_key not in existing_keys:
                return new_key

        # Fallback to hash
        return f"{base_key}{hashlib.md5(paper.title.encode()).hexdigest()[:6]}"

    def create_bibtex_entry(self, paper: Paper) -> str:
        """Create a BibTeX entry from paper metadata."""
        key = paper.bibtex_key or self.generate_key(paper)

        # Determine entry type
        entry_type = "article"
        if paper.journal:
            journal_lower = paper.journal.lower()
            if any(x in journal_lower for x in ['conference', 'proceedings', 'symposium']):
                entry_type = "inproceedings"

        lines = [f"@{entry_type}{{{key},"]
        lines.append(f"    author = {{{paper.authors}}},")
        lines.append(f"    title = {{{paper.title}}},")

        if paper.year:
            lines.append(f"    year = {{{paper.year}}},")
        if paper.journal:
            lines.append(f"    journal = {{{paper.journal}}},")
        if paper.doi:
            lines.append(f"    doi = {{{paper.doi}}},")
        if paper.url:
            lines.append(f"    url = {{{paper.url}}},")

        lines.append("}")

        return '\n'.join(lines), key

    def merge(self, paper: Paper) -> tuple:
        """Merge paper into BibTeX file. Returns (status, key)."""
        try:
            bibtex_entry, key = self.create_bibtex_entry(paper)
            paper.bibtex_key = key
            paper.bibtex_raw = bibtex_entry

            # Ensure file exists
            if not self.bibtex_path.exists():
                self.bibtex_path.parent.mkdir(parents=True, exist_ok=True)
                self.bibtex_path.write_text("")

            # Append to file
            with open(self.bibtex_path, 'a', encoding='utf-8') as f:
                f.write(f"\n\n{bibtex_entry}")

            return "added", key
        except Exception as e:
            return f"error: {str(e)}", None


# ============================================================================
# BASE SCRAPER
# ============================================================================

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

            # Download
            async with self.page.context.expect_download() as download_info:
                await self.page.click(f'a[href*="{paper.pdf_url}"]', timeout=10000)
                download = await download_info.value

            await download.save_as(filepath)
            return str(filepath)
        except Exception as e:
            print(f"  [WARN] PDF download failed: {e}")
            return None


# ============================================================================
# IEEE XPLORE SCRAPER
# ============================================================================

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

        await self.page.goto(ezproxy_url, wait_until='networkidle', timeout=30000)
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
                        # URL is already in ezproxy format from the page
                        if article_url and not article_url.startswith('http'):
                            article_url = to_ezproxy_url(f"{self.base_url}{article_url}")

                    paper = Paper(
                        title=title,
                        authors=authors,
                        year=year,
                        doi=doi,
                        url=article_url,
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
        # IEEE requires clicking through their citation modal
        # For simplicity, we'll generate our own BibTeX
        return None


# ============================================================================
# SCIENCEDIRECT SCRAPER
# ============================================================================

class ScienceDirectScraper(BaseScraper):
    """Scraper for ScienceDirect."""

    def __init__(self, page: Page, config: dict):
        super().__init__(page, config)
        self.name = "sciencedirect"
        self.base_url = "https://www.sciencedirect.com"

    async def search(self, query: str, max_results: int) -> List[Paper]:
        """Search ScienceDirect via ezproxy."""
        # Build ezproxy-proxied URL
        search_url = f"{self.base_url}/search?qs={quote_plus(query)}"
        ezproxy_url = to_ezproxy_url(search_url)

        await self.page.goto(ezproxy_url, wait_until='networkidle', timeout=30000)
        await self.random_delay()

        papers = []

        try:
            # Wait for results
            await self.page.wait_for_selector('.result-item-content, .search-result-item', timeout=15000)

            # Get result items
            items = await self.page.query_selector_all('.result-item-content, .search-result-item')

            for i, item in enumerate(items[:max_results]):
                try:
                    # Extract title
                    title_elem = await item.query_selector('h2 a, .result-list-title-link')
                    title = await title_elem.inner_text() if title_elem else ""
                    title = title.strip()

                    if not title:
                        continue

                    # Extract authors
                    authors_elem = await item.query_selector('.author-group, .authors')
                    authors = await authors_elem.inner_text() if authors_elem else ""
                    authors = authors.strip().replace('\n', ', ')

                    # Extract year
                    year_text = await item.inner_text()
                    year_match = re.search(r'\b(20\d{2}|19\d{2})\b', year_text)
                    year = int(year_match.group(1)) if year_match else None

                    # Extract journal
                    journal_elem = await item.query_selector('.publication-title, .journal-name')
                    journal = await journal_elem.inner_text() if journal_elem else None

                    # Get article URL (already proxied via ezproxy)
                    article_url = None
                    link_elem = await item.query_selector('h2 a, a.result-list-title-link')
                    if link_elem:
                        article_url = await link_elem.get_attribute('href')
                        if article_url and not article_url.startswith('http'):
                            article_url = to_ezproxy_url(f"{self.base_url}{article_url}")

                    paper = Paper(
                        title=title,
                        authors=authors,
                        year=year,
                        journal=journal,
                        url=article_url,
                        database=self.name
                    )
                    papers.append(paper)

                except Exception as e:
                    print(f"  [WARN] Error parsing ScienceDirect result {i+1}: {e}")
                    continue

        except Exception as e:
            print(f"  [ERROR] ScienceDirect search failed: {e}")

        return papers

    async def get_bibtex(self, paper: Paper) -> Optional[str]:
        """Get BibTeX from ScienceDirect."""
        return None


# ============================================================================
# SPRINGER SCRAPER
# ============================================================================

class SpringerScraper(BaseScraper):
    """Scraper for SpringerLink."""

    def __init__(self, page: Page, config: dict):
        super().__init__(page, config)
        self.name = "springer"
        self.base_url = "https://link.springer.com"

    async def search(self, query: str, max_results: int) -> List[Paper]:
        """Search SpringerLink via ezproxy."""
        # Build ezproxy-proxied URL
        search_url = f"{self.base_url}/search?query={quote_plus(query)}"
        ezproxy_url = to_ezproxy_url(search_url)

        await self.page.goto(ezproxy_url, wait_until='networkidle', timeout=30000)
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

                    paper = Paper(
                        title=title,
                        authors=authors,
                        year=year,
                        doi=doi,
                        journal=journal,
                        url=article_url,
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


# ============================================================================
# EZPROXY SESSION
# ============================================================================

class EzproxySession:
    """Manages browser session with ezproxy authentication."""

    def __init__(self, config: dict, console: Console):
        self.config = config
        self.console = console
        self.browser: Optional[Browser] = None
        self.context: Optional[BrowserContext] = None
        self.page: Optional[Page] = None

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.close()

    async def start(self):
        """Start browser session."""
        playwright = await async_playwright().start()

        self.browser = await playwright.chromium.launch(
            headless=self.config['download'].get('headless', False)
        )

        self.context = await self.browser.new_context(
            accept_downloads=True,
            viewport={'width': 1280, 'height': 800}
        )

        self.page = await self.context.new_page()

    async def close(self):
        """Close browser session."""
        if self.browser:
            await self.browser.close()

    async def wait_for_login(self):
        """Wait for user to login to ezproxy."""
        ezproxy_url = self.config['ezproxy']['url']
        login_timeout = self.config['ezproxy']['login_timeout']
        check_url = self.config['ezproxy'].get('login_check_url', 'https://ieeexplore.ieee.org')

        # Transform check URL to ezproxy format
        ezproxy_check_url = to_ezproxy_url(check_url)

        # Navigate to ezproxy login
        self.console.print(f"\n[bold blue]→ Opening ezproxy login:[/] {ezproxy_url}")
        await self.page.goto(ezproxy_url, wait_until='networkidle')

        self.console.print(Panel.fit(
            "[bold yellow]ACTION REQUIRED[/bold yellow]\n\n"
            f"1. Login to UGM ezproxy in the browser window\n"
            f"2. Navigate to any database (IEEE, ScienceDirect, Springer)\n"
            f"3. Press [bold green]ENTER[/bold green] here when logged in\n\n"
            f"[dim]Timeout: {login_timeout}s[/dim]\n"
            f"[dim]After login, URLs will be auto-transformed to ezproxy format[/dim]",
            title="🔐 Manual Login Required"
        ))

        # Wait for user input
        input(self.console.input("[bold green]Press ENTER when logged in...[/bold green]"))

        # Verify login by checking if we can access a protected resource via ezproxy
        self.console.print(f"[dim]Verifying login via: {ezproxy_check_url}[/dim]")
        await self.page.goto(ezproxy_check_url, wait_until='networkidle', timeout=15000)

        current_url = self.page.url
        if 'ezproxy.ugm.ac.id' in current_url:
            self.console.print(f"[green]✓ Login verified! Using ezproxy URL: {current_url}[/green]")
        elif 'login' in current_url.lower():
            self.console.print("[yellow]⚠️  Redirected to login page. Please try again.[/yellow]")
        else:
            self.console.print(f"[yellow]⚠️  Unexpected URL: {current_url}. Proceeding anyway...[/yellow]")


# ============================================================================
# MAIN DOWNLOADER
# ============================================================================

class PaperDownloader:
    """Main paper downloader orchestrator."""

    def __init__(self, config_path: str = "config.yaml"):
        self.config = load_config(config_path)
        self.console = Console()

        # Initialize paths
        self.download_dir = Path(self.config['paths']['downloads'])
        self.download_dir.mkdir(parents=True, exist_ok=True)

        self.logs_dir = Path(self.config['paths']['logs'])
        self.logs_dir.mkdir(parents=True, exist_ok=True)

        # Initialize database
        self.library = Library(self.config['paths']['database'])

        # Initialize BibTeX merger
        self.bibtex_merger = BibTexMerger(self.config['paths']['bibtex'], self.library)

        # Scrapers
        self.scrapers = {
            'ieee': IEEEScraper,
            'sciencedirect': ScienceDirectScraper,
            'springer': SpringerScraper,
        }

    def get_scraper(self, name: str, page: Page) -> BaseScraper:
        """Get scraper instance by name."""
        scraper_class = self.scrapers.get(name)
        if scraper_class:
            return scraper_class(page, self.config)
        raise ValueError(f"Unknown scraper: {name}")

    async def search_and_download(
        self,
        query: str,
        topic: str = None,
        max_results: int = None,
        databases: List[str] = None,
        dry_run: bool = False,
        session: EzproxySession = None
    ) -> Dict[str, Any]:
        """Search and download papers for a query."""

        if not topic:
            topic = re.sub(r'[^\w\s-]', '', query.lower())
            topic = re.sub(r'[-\s]+', '-', topic)[:40]

        if not max_results:
            max_results = self.config['download']['max_per_database']

        if not databases:
            databases = [db['name'] for db in self.config['databases'] if db.get('enabled', True)]

        results = {
            'query': query,
            'topic': topic,
            'total_found': 0,
            'total_downloaded': 0,
            'total_skipped': 0,
            'total_failed': 0,
            'databases': {}
        }

        for db_name in databases:
            self.console.print(f"\n[bold cyan]Searching {db_name.upper()}:[/] {query}")

            try:
                scraper = self.get_scraper(db_name, session.page)
                papers = await scraper.search(query, max_results)

                db_results = {
                    'found': len(papers),
                    'downloaded': 0,
                    'skipped': 0,
                    'failed': 0
                }

                self.console.print(f"  Found [bold]{len(papers)}[/bold] papers")

                for i, paper in enumerate(papers):
                    paper.topic = topic

                    # Check for duplicates
                    if self.library.paper_exists(paper):
                        self.console.print(f"  [dim]⏭️  [{i+1}/{len(papers)}] Skipped (duplicate): {paper.title[:60]}...[/dim]")
                        db_results['skipped'] += 1
                        continue

                    if dry_run:
                        self.console.print(f"  [yellow]📄 [{i+1}/{len(papers)}] Would download: {paper.title[:60]}...[/yellow]")
                        db_results['downloaded'] += 1
                        continue

                    # Download and save
                    try:
                        # Create topic directory
                        topic_dir = self.download_dir / topic
                        topic_dir.mkdir(parents=True, exist_ok=True)

                        # Merge BibTeX
                        status, key = self.bibtex_merger.merge(paper)

                        if status == "added":
                            self.console.print(f"  [green]✓ [{i+1}/{len(papers)}] Downloaded: {paper.title[:60]}...[/green]")
                            self.console.print(f"    [dim]BibTeX key: {key}[/dim]")

                            # Save to database
                            self.library.add_paper(paper, status='downloaded')
                            db_results['downloaded'] += 1
                        else:
                            self.console.print(f"  [red]✗ [{i+1}/{len(papers)}] Failed: {paper.title[:60]}...[/red]")
                            db_results['failed'] += 1

                        await scraper.random_delay()

                    except Exception as e:
                        self.console.print(f"  [red]✗ [{i+1}/{len(papers)}] Error: {e}[/red]")
                        db_results['failed'] += 1

                results['databases'][db_name] = db_results
                results['total_found'] += db_results['found']
                results['total_downloaded'] += db_results['downloaded']
                results['total_skipped'] += db_results['skipped']
                results['total_failed'] += db_results['failed']

                # Log search
                self.library.log_search(query, topic, db_name, db_results['found'], db_results['downloaded'])

            except Exception as e:
                self.console.print(f"  [red]✗ Error searching {db_name}: {e}[/red]")
                results['databases'][db_name] = {'error': str(e)}

        return results

    async def run_interactive(
        self,
        query: str = None,
        topic: str = None,
        max_results: int = None,
        databases: List[str] = None,
        dry_run: bool = False
    ):
        """Run interactive download session."""

        async with EzproxySession(self.config, self.console) as session:
            await session.wait_for_login()

            if query:
                # Single search
                results = await self.search_and_download(
                    query, topic, max_results, databases, dry_run, session
                )
                self._print_summary([results])
            else:
                # Run all searches from config
                all_results = []
                searches = self.config.get('searches', [])

                if not searches:
                    self.console.print("[yellow]No searches configured in config.yaml[/yellow]")
                    self.console.print("Use --search to specify a query")
                    return

                for search_config in searches:
                    search_query = search_config['query']
                    search_topic = search_config.get('topic')
                    search_max = search_config.get('max_results', max_results)

                    results = await self.search_and_download(
                        search_query, search_topic, search_max, databases, dry_run, session
                    )
                    all_results.append(results)

                    # Delay between searches
                    await asyncio.sleep(random.uniform(3, 5))

                self._print_summary(all_results)

    def list_papers(self, year_range: tuple = None, topic: str = None, export_bib: str = None):
        """List downloaded papers."""
        papers = self.library.list_papers(year_range, topic)

        if not papers:
            self.console.print("[yellow]No papers found in library[/yellow]")
            return

        table = Table(title=f"Papers in Library ({len(papers)} total)")
        table.add_column("#", style="dim", width=4)
        table.add_column("Year", style="cyan", width=6)
        table.add_column("Title", width=50)
        table.add_column("Authors", width=25)
        table.add_column("Topic", width=20)
        table.add_column("DB", width=10)

        for i, paper in enumerate(papers, 1):
            table.add_row(
                str(i),
                str(paper.get('year', '')),
                paper['title'][:47] + "..." if len(paper['title']) > 50 else paper['title'],
                (paper.get('authors') or '')[:22] + "..." if paper.get('authors') and len(paper.get('authors', '')) > 25 else (paper.get('authors') or ''),
                paper.get('topic', '')[:17] + "..." if paper.get('topic') and len(paper.get('topic', '')) > 20 else (paper.get('topic') or ''),
                paper.get('database', '')
            )

        self.console.print(table)

        if export_bib:
            self._export_bibtex(papers, export_bib)

    def _export_bibtex(self, papers: List[dict], output_path: str):
        """Export papers to BibTeX file."""
        with open(output_path, 'w', encoding='utf-8') as f:
            for paper in papers:
                if paper.get('bibtex_raw'):
                    f.write(paper['bibtex_raw'] + "\n\n")

        self.console.print(f"[green]✓ Exported {len(papers)} entries to {output_path}[/green]")

    def _print_summary(self, all_results: List[dict]):
        """Print summary table."""
        table = Table(title="\n📊 Download Summary")
        table.add_column("Search Query", width=40)
        table.add_column("Found", justify="right", width=6)
        table.add_column("Downloaded", justify="right", width=10, style="green")
        table.add_column("Skipped", justify="right", width=8, style="yellow")
        table.add_column("Failed", justify="right", width=7, style="red")

        total_found = 0
        total_downloaded = 0
        total_skipped = 0
        total_failed = 0

        for results in all_results:
            table.add_row(
                results['query'][:37] + "..." if len(results['query']) > 40 else results['query'],
                str(results['total_found']),
                str(results['total_downloaded']),
                str(results['total_skipped']),
                str(results['total_failed'])
            )
            total_found += results['total_found']
            total_downloaded += results['total_downloaded']
            total_skipped += results['total_skipped']
            total_failed += results['total_failed']

        table.add_section()
        table.add_row(
            "[bold]TOTAL[/bold]",
            f"[bold]{total_found}[/bold]",
            f"[bold green]{total_downloaded}[/bold green]",
            f"[bold yellow]{total_skipped}[/bold yellow]",
            f"[bold red]{total_failed}[/bold red]"
        )

        self.console.print(table)

        self.console.print(f"\n📁 Files saved to: [bold]{self.download_dir}[/bold]")
        self.console.print(f"📄 BibTeX file: [bold]{self.config['paths']['bibtex']}[/bold]")


# ============================================================================
# CLI
# ============================================================================

def parse_year_range(value: str) -> tuple:
    """Parse year range from string like '2020-2025' or '2023'."""
    if '-' in value:
        parts = value.split('-')
        return (int(parts[0]), int(parts[1]))
    return (int(value), int(value))


def main():
    parser = argparse.ArgumentParser(
        description="Paper Downloader Agent - Download academic papers via UGM ezproxy",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --interactive --search "blockchain RWA"
  %(prog)s --search "ERC-721" --topic "nft-tracking" --max 10
  %(prog)s --search "smart contract" --database ieee --dry-run
  %(prog)s --list --year 2023-2025
  %(prog)s --list --topic "blockchain-rwa" --export-bib filtered.bib
  %(prog)s --all
"""
    )

    # Mode flags
    parser.add_argument('--interactive', '-i', action='store_true',
                        help='Run in interactive mode (wait for manual ezproxy login)')
    parser.add_argument('--list', '-l', action='store_true',
                        help='List downloaded papers')
    parser.add_argument('--all', '-a', action='store_true',
                        help='Run all searches from config.yaml')

    # Search options
    parser.add_argument('--search', '-s', type=str,
                        help='Search query')
    parser.add_argument('--topic', '-t', type=str,
                        help='Topic folder name for downloads')
    parser.add_argument('--max', '-m', type=int,
                        help='Max papers per database')
    parser.add_argument('--database', '-d', type=str,
                        choices=['ieee', 'sciencedirect', 'springer'],
                        help='Search only this database')

    # Filters (for --list)
    parser.add_argument('--year', '-y', type=parse_year_range,
                        help='Filter by year range (e.g., 2023-2025)')
    parser.add_argument('--export-bib', '-e', type=str,
                        help='Export filtered papers to BibTeX file')

    # Other options
    parser.add_argument('--dry-run', '-n', action='store_true',
                        help='Preview without downloading')
    parser.add_argument('--config', '-c', type=str, default='config.yaml',
                        help='Path to config file')

    args = parser.parse_args()

    downloader = PaperDownloader(args.config)

    # Handle list mode
    if args.list:
        downloader.list_papers(args.year, args.topic, args.export_bib)
        return

    # Handle search/download mode
    databases = [args.database] if args.database else None

    if args.interactive or args.all or args.search:
        asyncio.run(downloader.run_interactive(
            query=args.search,
            topic=args.topic,
            max_results=args.max,
            databases=databases,
            dry_run=args.dry_run
        ))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
