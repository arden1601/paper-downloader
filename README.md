# Paper Downloader Agent

A CLI tool to search, collect, and manage academic papers from IEEE Xplore, ScienceDirect, and SpringerLink via UGM ezproxy. Built for thesis literature review.

## Setup

```bash
# Install dependencies
pip install -r requirements.txt

# Install Playwright browsers
playwright install chromium
```

## Usage

### Search & Save Papers

```bash
# Search with manual ezproxy login, save metadata only (no PDF download)
python download.py --interactive --search "blockchain RWA" --no-download

# Search with PDF download attempt
python download.py --interactive --search "blockchain RWA"

# Search specific database with limit
python download.py --interactive --search "smart contract" --database ieee --max 10

# Preview without saving
python download.py --search "NFT tracking" --dry-run
```

### Run All Searches from Config

```bash
python download.py --all
```

### Interactive Menu (Arrow-Key Navigation)

```bash
python download.py --menu
```

### List & Export

```bash
# List all saved papers
python download.py --list

# Filter by year
python download.py --list --year 2023-2025

# Filter by topic and export to CSV
python download.py --list --topic "blockchain-rwa" --export-csv papers.csv
```

### Database Management

```bash
# Show statistics
python download.py --stats

# Clear all data
python download.py --clear-db
```

## Key Flags

| Flag | Description |
|------|-------------|
| `-i, --interactive` | Open browser for manual ezproxy login |
| `-s, --search` | Search query |
| `-d, --database` | Target database (`ieee`, `sciencedirect`, `springer`) |
| `-t, --topic` | Topic folder name for organizing papers |
| `--max N` | Max papers per database (default: 5) |
| `--no-download` | Save metadata + PDF URLs without downloading PDFs |
| `-n, --dry-run` | Preview results without saving anything |
| `--export-csv FILE` | Export filtered papers to CSV |
| `-m, --menu` | Launch interactive CLI menu |

## Configuration

Edit `config.yaml` to customize:

- **Ezproxy settings** - login URL and timeout
- **Databases** - enable/disable specific databases
- **Download settings** - delays, retries, timeouts
- **Storage paths** - downloads folder, database, BibTeX output
- **Predefined searches** - run all with `--all`

## How It Works

1. Opens a Chromium browser via Playwright
2. Redirects to UGM ezproxy login page
3. You log in manually in the browser
4. Tool searches papers, saves metadata to SQLite
5. Generates BibTeX entries merged into your reference file
6. Optionally downloads PDFs (may be blocked by some publishers)

Use `--no-download` to skip PDF downloads and just collect paper info with direct links for manual download.

## Output

- **`library.db`** - SQLite database with all papers
- **`downloads/`** - Downloaded PDFs organized by topic
- **`daftar-pustaka.bib`** - Merged BibTeX reference file
- **CSV export** - Paper list with titles, URLs, and status
