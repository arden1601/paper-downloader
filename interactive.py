"""
Interactive CLI menu for paper downloader.
"""

import asyncio
from typing import List, Optional

import questionary
from questionary import Choice
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import print as rprint

from database import Library
from exporter import CSVExporter, BrowserOpener


class InteractiveMenu:
    """Interactive CLI menu with arrow-key navigation."""

    def __init__(
        self,
        library: Library,
        csv_exporter: CSVExporter,
        browser_opener: BrowserOpener,
        console: Console = None
    ):
        self.library = library
        self.csv_exporter = csv_exporter
        self.browser = browser_opener
        self.console = console or Console()
        self._papers_cache: List[dict] = []

    async def run(self):
        """Main menu loop."""
        while True:
            choice = await questionary.select(
                "What would you like to do?",
                choices=[
                    Choice("📚 List papers", value="list"),
                    Choice("📊 Show statistics", value="stats"),
                    Choice("📤 Export to CSV", value="export"),
                    Choice("🌐 Open paper in browser", value="open"),
                    Choice("🗑️  Clear database", value="clear"),
                    Choice("🚪 Exit", value="exit"),
                ]
            ).ask_async()

            if choice is None or choice == "exit":
                self.console.print("\n[bold blue]Goodbye! 👋[/bold blue]")
                break

            await self._handle_choice(choice)

    async def _handle_choice(self, choice: str):
        """Handle menu choice."""
        handlers = {
            "list": self._handle_list,
            "stats": self._handle_stats,
            "export": self._handle_export,
            "open": self._handle_open,
            "clear": self._handle_clear,
        }

        handler = handlers.get(choice)
        if handler:
            await handler()

    async def _handle_list(self):
        """List all papers."""
        papers = self.library.list_papers()
        self._papers_cache = papers

        if not papers:
            self.console.print("[yellow]No papers in library.[/yellow]")
            return

        table = Table(title=f"📚 Papers in Library ({len(papers)} total)")
        table.add_column("#", style="dim", width=4)
        table.add_column("Year", style="cyan", width=6)
        table.add_column("Title", width=50)
        table.add_column("Authors", width=25)
        table.add_column("Topic", width=20)
        table.add_column("DB", width=10)

        for i, paper in enumerate(papers, 1):
            title = paper.get('title', '')
            title_display = title[:47] + "..." if len(title) > 50 else title

            authors = paper.get('authors', '') or ''
            authors_display = authors[:22] + "..." if len(authors) > 25 else authors

            topic = paper.get('topic', '') or ''
            topic_display = topic[:17] + "..." if len(topic) > 20 else topic

            table.add_row(
                str(i),
                str(paper.get('year', '')),
                title_display,
                authors_display,
                topic_display,
                paper.get('database', '')
            )

        self.console.print(table)

    async def _handle_stats(self):
        """Show library statistics."""
        stats = self.library.get_stats()

        panel = Panel.fit(
            f"[bold]📊 Library Statistics[/bold]\n\n"
            f"  Total papers: [bold cyan]{stats['total_papers']}[/bold cyan]\n"
            f"  Total searches: [bold cyan]{stats['total_searches']}[/bold cyan]\n"
            f"  Topics: [bold]{', '.join(stats['topics']) or '[dim]None[/dim]'}[/bold]\n"
            f"  Databases: [bold]{', '.join(stats['databases']) or '[dim]None[/dim]'}[/bold]",
            title="📈 Statistics"
        )
        self.console.print(panel)

    async def _handle_export(self):
        """Export papers to CSV."""
        papers = self.library.list_papers()
        if not papers:
            self.console.print("[yellow]No papers to export.[/yellow]")
            return

        filepath = await questionary.text(
            "Enter output file path:",
            default="papers.csv"
        ).ask_async()

        if filepath:
            self.csv_exporter.export(papers, filepath)

    async def _handle_open(self):
        """Open paper links in browser."""
        papers = self.library.list_papers()
        if not papers:
            self.console.print("[yellow]No papers in library.[/yellow]")
            return

        # Show list first
        await self._handle_list()

        # Get paper index
        index_str = await questionary.text(
            "Enter paper number (or 'c' to cancel):",
        ).ask_async()

        if index_str.lower() == 'c' or not index_str:
            return

        try:
            index = int(index_str)
            paper = self.library.get_paper_by_index(index)
            if not paper:
                self.console.print("[red]Invalid paper number.[/red]")
                return

            # Ask what to open
            link_type = await questionary.select(
                "What would you like to open?",
                choices=[
                    Choice("📄 Article URL", value="article"),
                    Choice("📑 PDF URL", value="pdf"),
                    Choice("🔗 DOI link", value="doi"),
                    Choice("← Back", value="back"),
                ]
            ).ask_async()

            if link_type == "back":
                return

            self.browser.open_by_choice(paper, link_type)

        except ValueError:
            self.console.print("[red]Please enter a valid number.[/red]")

    async def _handle_clear(self):
        """Clear database with confirmation."""
        confirm = await questionary.confirm(
            "⚠️  This will delete all papers and search history. Continue?",
            default=False
        ).ask_async()

        if confirm:
            result = self.library.clear_database()
            self.console.print(Panel.fit(
                f"[bold green]✓ Database cleared![/bold green]\n\n"
                f"  Papers deleted: [bold]{result['papers_deleted']}[/bold]\n"
                f"  Searches deleted: [bold]{result['searches_deleted']}[/bold]",
                title="🗑️  Database Cleared"
            ))


async def run_interactive_menu(library: Library, console: Console = None):
    """Run the interactive menu."""
    console = console or Console()
    csv_exporter = CSVExporter(console)
    browser_opener = BrowserOpener(console)
    menu = InteractiveMenu(library, csv_exporter, browser_opener, console)
    await menu.run()
