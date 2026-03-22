# Paper Downloader Agent - Design Document

## Overview

A CLI tool to search and download academic papers from IEEE Xplore, ScienceDirect, and SpringerLink via UGM ezproxy, with automatic BibTeX merging for thesis writing.

## Architecture

```
paper-downloader/
├── download.py           # Main CLI (~300 lines)
├── requirements.txt      # playwright, bibtexparser, pyyaml, rich
├── config.yaml           # Search terms, database URLs, settings
├── downloads/            # PDFs organized by topic
│   ├── blockchain-rwa/
│   ├── nft-asset-tracking/
│   └── ...
├── library.db            # SQLite database
└── logs/
    └── session_YYYYMMDD_HHMMSS.log
```

## CLI Commands

```bash
# Interactive mode (opens browser, you login)
python download.py --interactive

# Search with specific term
python download.py --search "blockchain RWA" --topic "blockchain-rwa"

# Dry run (preview only)
python download.py --search "ERC-721" --dry-run

# List downloaded papers with filters
python download.py --list --year 2023-2025 --topic "blockchain-rwa"

# Export filtered BibTeX
python download.py --list --year 2020-2025 --export-bib filtered.bib

# Run all searches from config
python download.py --all

# Help
python download.py --help
```

### Arguments

| Argument | Description | Default |
|----------|-------------|---------|
| `--interactive` | Wait for manual ezproxy login | False |
| `--search "query"` | Search term | None |
| `--topic "name"` | Folder name for downloads | Auto from query |
| `--max N` | Max papers per database | 5 |
| `--database NAME` | ieee/springer/sciencedirect | all |
| `--dry-run` | Preview only, no download | False |
| `--list` | List downloaded papers | False |
| `--year FROM-TO` | Filter by year range | all |
| `--export-bib FILE` | Export filtered BibTeX | None |
| `--all` | Run all searches from config | False |
| `--config FILE` | Custom config file | config.yaml |
| `--help` | Show help message | - |

## Database Schema (SQLite)

```sql
CREATE TABLE papers (
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
    downloaded_at DATETIME,
    status TEXT DEFAULT 'downloaded'
);

CREATE TABLE searches (
    id INTEGER PRIMARY KEY,
    query TEXT NOT NULL,
    topic TEXT,
    database TEXT,
    results_found INTEGER,
    results_downloaded INTEGER,
    searched_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

## Scraper Selectors

### IEEE Xplore
- URL: `https://ieeexplore.ieee.org/search/searchresult.jsp?queryText={query}`
- Results: `.List-results-items`
- Title: `.result-item h2 a`
- Authors: `.author span`
- Year: `.publisher-info-container span`
- DOI: `data-doi` attribute
- PDF: `.stats-document-lh-action-downloadPdf`

### ScienceDirect
- URL: `https://www.sciencedirect.com/search?qs={query}`
- Results: `.result-item-content`
- Title: `.result-list-title-link`
- Authors: `.author-group`
- Year: `.srctitle-date-fields`

### SpringerLink
- URL: `https://link.springer.com/search?query={query}`
- Results: `.app-card-open`
- Title: `h3.app-card-open__heading a`
- Authors: `.app-card-open__author-list`
- Year: `.app-card-open__meta-item time`

## BibTeX Integration

- Target: `../template-skripsi/daftar-pustaka.bib`
- Key format: `AuthorYear` + letter if duplicate
- Deduplication: Check DOI first, then fuzzy title match
- Append new entries to existing file

## Error Handling

| Scenario | Action |
|----------|--------|
| PDF download fails | Log error, save metadata, continue |
| BibTeX fetch fails | Generate from metadata |
| Page timeout | Retry with backoff (max 3) |
| Rate limited | Wait 60s, retry |
| Session expired | Prompt re-login |

## Config File (config.yaml)

```yaml
ezproxy:
  url: "https://ezproxy.ugm.ac.id/login"
  login_timeout: 300

databases:
  - name: ieee
    enabled: true
  - name: sciencedirect
    enabled: true
  - name: springer
    enabled: true

download:
  max_per_database: 5
  delay_min: 2
  delay_max: 4
  retry_max: 3
  timeout: 30

paths:
  downloads: "./downloads"
  database: "./library.db"
  bibtex: "../template-skripsi/daftar-pustaka.bib"
  logs: "./logs"

searches:
  - query: "blockchain real world assets tokenization"
    topic: "blockchain-rwa"
  - query: "ERC-721 NFT asset tracking"
    topic: "nft-asset-tracking"
  - query: "smart contract access control RBAC"
    topic: "smart-contract-rbac"
  - query: "IPFS decentralized storage blockchain"
    topic: "ipfs-storage"
  - query: "supply chain traceability blockchain"
    topic: "supply-chain-traceability"
  - query: "calibration tracking blockchain"
    topic: "calibration-tracking"
```

## Decision Log

| # | Decision | Alternatives | Why |
|---|----------|--------------|-----|
| 1 | Manual login per session | Stored credentials | Safer, handles 2FA |
| 2 | CLI with arguments | GUI | Flexible, scriptable |
| 3 | Organize by topic folders | By database | Matches thesis structure |
| 4 | SQLite for tracking | JSON/CSV | Queryable, dedup support |
| 5 | Download all years | Pre-filter | Don't miss foundational papers |
| 6 | Single-file approach | Modular | Simpler, faster to build |
