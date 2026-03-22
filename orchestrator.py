"""
Paper Downloader Orchestrator - Main coordination logic.
"""

import asyncio
import csv
import random
import re
from pathlib import Path
from typing import List, Optional, Dict

from rich.console import Console
from rich.table import Table
from rich.panel import Panel

from config import load_config
from database import Library
from models import Paper
from bibtex import BibTexMerger
from exporter import CSVExporter, BrowserOpener
from interactive import InteractiveMenu
from session import EzproxySession
from scrapers import IEEEScraper, ScienceDirectScraper, SpringerScraper


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

        # Initialize exporters
        self.csv_exporter = CSVExporter(self.console)
        self.browser_opener = BrowserOpener(self.console)

        # Scrapers mapping
        self.scrapers = {
            'ieee': IEEEScraper,
            'sciencedirect': ScienceDirectScraper,
            'springer': SpringerScraper,
        }

    def get_scraper(self, name: str, page):
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
    ) -> dict:
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

                        # Try to download PDF
                        pdf_path = None
                        if paper.pdf_url:
                            pdf_path = await scraper.download_pdf(paper, topic_dir)
                            if pdf_path:
                                self.console.print(f"  [dim]    PDF saved: {Path(pdf_path).name}[/dim]")
                        else:
                            self.console.print(f"  [dim]    No direct PDF URL available[/dim]")

                        # Merge BibTeX
                        status, key = self.bibtex_merger.merge(paper)

                        if status == "added":
                            self.console.print(f"  [green]✓ [{i+1}/{len(papers)}] Saved: {paper.title[:60]}...[/green]")
                            self.console.print(f"    [dim]BibTeX key: {key}[/dim]")

                            # Save to database
                            self.library.add_paper(paper, pdf_path=pdf_path, status='downloaded')
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

    def run_menu(self):
        """Run interactive menu."""
        menu = InteractiveMenu(
            library=self.library,
            csv_exporter=self.csv_exporter,
            browser_opener=self.browser_opener,
            console=self.console
        )
        asyncio.run(menu.run())

    def list_papers(self, year_range: tuple = None, topic: str = None, export_csv: str = None):
        """List downloaded papers."""
        papers = self.library.list_papers(year_range, topic)

        if not papers:
            self.console.print("[yellow]No papers in library[/yellow]")
            return

        table = Table(title=f"Papers in Library ({len(papers)} total)")
        table.add_column("#", style="dim", width=4)
        table.add_column("Year", style="cyan", width=6)
        table.add_column("Title", width=50)
        table.add_column("Authors", width=25)
        table.add_column("Topic", width=20)
        table.add_column("DB", width=12)

        for i, paper in enumerate(papers, 1):
            title = paper.get('title', '')
            authors = (paper.get('authors') or '')[:22]
            topic = (paper.get('topic') or '')[:17]

            table.add_row(
                str(i),
                str(paper.get('year', '')),
                title[:47] + "..." if len(title) > 50 else title,
                authors,
                topic,
                paper.get('database', '')
            )

        self.console.print(table)

        if export_csv:
            self._export_csv(papers, export_csv)

    def _export_csv(self, papers: List[dict], filepath: str):
        """Export papers to CSV file."""
        self.csv_exporter.export(papers, filepath)

    def clear_database(self):
        """Clear all papers and searches from database."""
        result = self.library.clear_database()

        self.console.print(Panel.fit(
            f"[bold green]✓ Database cleared![/bold green]\n\n"
            f"  Papers deleted: [bold]{result['papers_deleted']}[/bold]\n"
            f"  Searches deleted: [bold]{result['searches_deleted']}[/bold]\n\n"
            f"[dim]The download directory is not affected.[/dim]",
            title="🗑️  Database Cleared"
        ))

    def show_stats(self):
        """Show database statistics."""
        stats = self.library.get_stats()

        self.console.print(Panel.fit(
            f"[bold]📊 Library Statistics[/bold]\n\n"
            f"  Total papers: [bold cyan]{stats['total_papers']}[/bold cyan]\n"
            f"  Total searches: [bold cyan]{stats['total_searches']}[/bold cyan]\n"
            f"  Topics: [bold]{', '.join(stats['topics']) if stats['topics'] else '[dim]None[/dim]'}[/bold]\n"
            f"  Databases: [bold]{', '.join(stats['databases']) if stats['databases'] else '[dim]None[/dim]'}[/bold]",
            title="📈 Library Statistics"
        ))

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
