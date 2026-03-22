"""
Database manager for tracking papers.
"""

import re
import sqlite3
from pathlib import Path
from typing import List, Optional, Set

from models import Paper


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
                    pdf_url TEXT,
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
                 bibtex_key, bibtex_raw, abstract, url, pdf_url, status)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                paper.doi, paper.title, paper.authors, paper.year, paper.journal,
                paper.database, paper.topic, pdf_path, paper.bibtex_key,
                paper.bibtex_raw, paper.abstract, paper.url, paper.pdf_url, status
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

    def clear_database(self) -> dict:
        """Clear all papers and search history from database. Returns counts deleted."""
        with sqlite3.connect(self.db_path) as conn:
            # Count before deletion
            papers_count = conn.execute("SELECT COUNT(*) FROM papers").fetchone()[0]
            searches_count = conn.execute("SELECT COUNT(*) FROM searches").fetchone()[0]

            # Delete all records
            conn.execute("DELETE FROM papers")
            conn.execute("DELETE FROM searches")

            return {
                'papers_deleted': papers_count,
                'searches_deleted': searches_count
            }

    def get_stats(self) -> dict:
        """Get database statistics."""
        with sqlite3.connect(self.db_path) as conn:
            papers_count = conn.execute("SELECT COUNT(*) FROM papers").fetchone()[0]
            searches_count = conn.execute("SELECT COUNT(*) FROM searches").fetchone()[0]
            topics = conn.execute("SELECT DISTINCT topic FROM papers WHERE topic IS NOT NULL").fetchall()
            databases = conn.execute("SELECT DISTINCT database FROM papers WHERE database IS NOT NULL").fetchall()

            return {
                'total_papers': papers_count,
                'total_searches': searches_count,
                'topics': [t[0] for t in topics],
                'databases': [d[0] for d in databases]
            }

    def get_existing_keys(self) -> Set:
        """Get all existing BibTeX keys."""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute("SELECT bibtex_key FROM papers WHERE bibtex_key IS NOT NULL")
            return {row[0] for row in cursor.fetchall()}

    def get_paper_by_index(self, index: int) -> Optional[dict]:
        """Get paper by 1-based index from list_papers order."""
        papers = self.list_papers()
        if 1 <= index <= len(papers):
            return papers[index - 1]
        return None
