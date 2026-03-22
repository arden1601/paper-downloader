"""
Export utilities for paper downloader.
"""

import csv
import webbrowser
from pathlib import Path
from typing import List, Optional

from rich.console import Console

from models import Paper


class CSVExporter:
    """Export papers to CSV format."""

    def __init__(self, console: Console = None):
        self.console = console or Console()

    def export(self, papers: List[dict], filepath: str, include_headers: bool = True) -> bool:
        """
        Export papers to CSV file.

        Args:
            papers: List of paper dictionaries
            filepath: Output CSV file path
            include_headers: Whether to include header row

        Returns:
            True if successful, False otherwise
        """
        try:
            filepath = Path(filepath)
            filepath.parent.mkdir(parents=True, exist_ok=True)

            with open(filepath, 'w', newline='', encoding='utf-8') as f:
                fieldnames = [
                    'title', 'authors', 'year', 'doi', 'journal',
                    'url', 'pdf_url', 'database', 'topic', 'status'
                ]
                writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')

                if include_headers:
                    writer.writeheader()

                for paper in papers:
                    writer.writerow(paper)

            self.console.print(f"[green]✓ Exported {len(papers)} papers to: {filepath}[/green]")
            return True

        except Exception as e:
            self.console.print(f"[red]✗ Export failed: {e}[/red]")
            return False


class BrowserOpener:
    """Open paper links in default browser."""

    def __init__(self, console: Console = None):
        self.console = console or Console()

    def open_article(self, paper: dict) -> bool:
        """Open article URL in browser."""
        url = paper.get('url')
        if url:
            webbrowser.open(url)
            self.console.print(f"[green]✓ Opened article: {paper.get('title', 'Unknown')[:50]}...[/green]")
            return True
        self.console.print("[yellow]⚠ No article URL available[/yellow]")
        return False

    def open_pdf(self, paper: dict) -> bool:
        """Open PDF URL in browser."""
        url = paper.get('pdf_url')
        if url:
            webbrowser.open(url)
            self.console.print(f"[green]✓ Opened PDF: {paper.get('title', 'Unknown')[:50]}...[/green]")
            return True
        self.console.print("[yellow]⚠ No PDF URL available[/yellow]")
        return False

    def open_doi(self, paper: dict) -> bool:
        """Open DOI link in browser."""
        doi = paper.get('doi')
        if doi:
            url = f"https://doi.org/{doi}"
            webbrowser.open(url)
            self.console.print(f"[green]✓ Opened DOI: {doi}[/green]")
            return True
        self.console.print("[yellow]⚠ No DOI available[/yellow]")
        return False

    def open_by_choice(self, paper: dict, choice: str) -> bool:
        """Open link by choice (article, pdf, doi)."""
        if choice == 'article':
            return self.open_article(paper)
        elif choice == 'pdf':
            return self.open_pdf(paper)
        elif choice == 'doi':
            return self.open_doi(paper)
        else:
            self.console.print(f"[red]Unknown choice: {choice}[/red]")
            return False
