"""
Configuration module for paper downloader.
"""

from pathlib import Path
from urllib.parse import urlparse, urlunparse

import yaml


# ============================================================================
# DEFAULT CONFIGURATION
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
