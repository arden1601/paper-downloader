#!/usr/bin/env python3
"""
Paper Downloader Agent - CLI Entry Point

A CLI tool to search and download academic papers from IEEE Xplore,
ScienceDirect, and SpringerLink via UGM ezproxy.

Usage:
    python download.py --interactive --search "blockchain RWA"
    python download.py --list --year 2023-2025
    python download.py --menu
"""

import argparse
import asyncio

from orchestrator import PaperDownloader


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
  %(prog)s --list --topic "blockchain-rwa" --export-csv papers.csv
  %(prog)s --menu
  %(prog)s --stats
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
    parser.add_argument('--menu', '-m', action='store_true',
                        help='Launch interactive menu (arrow-key navigation)')
    parser.add_argument('--clear-db', action='store_true',
                        help='Clear database (delete all papers and searches)')
    parser.add_argument('--stats', action='store_true',
                        help='Show database statistics')

    # Search options
    parser.add_argument('--search', '-s', type=str,
                        help='Search query')
    parser.add_argument('--topic', '-t', type=str,
                        help='Topic folder name for downloads')
    parser.add_argument('--max', type=int, default=5,
                        help='Max papers per database')
    parser.add_argument('--database', '-d', type=str,
                        choices=['ieee', 'sciencedirect', 'springer'],
                        help='Search only this database')

    # Filters (for --list)
    parser.add_argument('--year', '-y', type=parse_year_range,
                        help='Filter by year range (e.g., 2023-2025)')
    parser.add_argument('--export-csv', '-e', type=str,
                        help='Export filtered papers to CSV file')

    # Other options
    parser.add_argument('--dry-run', '-n', action='store_true',
                        help='Preview without downloading')
    parser.add_argument('--no-download', action='store_true',
                        help='Save papers without downloading PDFs')
    parser.add_argument('--config', '-c', type=str, default='config.yaml',
                        help='Path to config file')

    args = parser.parse_args()

    # Initialize downloader
    downloader = PaperDownloader(args.config)

    # Handle menu mode
    if args.menu:
        downloader.run_menu()
        return

    # Handle list mode
    if args.list:
        downloader.list_papers(args.year, args.topic, args.export_csv)
        return

    # Handle clear database
    if args.clear_db:
        downloader.clear_database()
        return

    # Handle stats
    if args.stats:
        downloader.show_stats()
        return

    # Handle search/download mode
    databases = [args.database] if args.database else None

    if args.interactive or args.search:
        asyncio.run(downloader.run_interactive(
            query=args.search,
            topic=args.topic,
            max_results=args.max,
            databases=databases,
            dry_run=args.dry_run,
            no_download=args.no_download
        ))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
