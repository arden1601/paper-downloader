"""
Ezproxy session management.
"""

import asyncio
from typing import Optional

from playwright.async_api import async_playwright, Page, Browser, BrowserContext
from rich.console import Console
from rich.panel import Panel

from config import to_ezproxy_url


class EzproxySession:
    """Manages browser session with ezproxy authentication."""

    def __init__(self, config: dict, console: Console):
        self.config = config
        self.console = console
        self.browser: Optional[Browser] = None
        self.context: Optional[BrowserContext] = None
        self.page: Optional[Page] = None
        self._playwright = None

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.close()

    async def start(self):
        """Start browser session."""
        self._playwright = await async_playwright().start()

        self.browser = await self._playwright.chromium.launch(
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
        if self._playwright:
            await self._playwright.stop()

    async def wait_for_login(self):
        """Wait for user to login to ezproxy."""
        ezproxy_url = self.config['ezproxy']['url']
        login_timeout = self.config['ezproxy']['login_timeout']
        check_url = self.config['ezproxy'].get('login_check_url', 'https://ieeexplore.ieee.org')

        # Transform check URL to ezproxy format
        ezproxy_check_url = to_ezproxy_url(check_url)

        # Navigate to ezproxy login
        self.console.print(f"\n[bold blue]→ Opening ezproxy login:[/] {ezproxy_url}")
        await self.page.goto(ezproxy_url, wait_until='load')

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
        try:
            # Use 'load' instead of 'networkidle' - more lenient
            await self.page.goto(ezproxy_check_url, wait_until='load', timeout=30000)
            # Wait a bit for any redirects
            await asyncio.sleep(2)
        except Exception as e:
            self.console.print(f"[yellow]⚠️  Navigation timeout, but continuing anyway: {e}[/yellow]")

        current_url = self.page.url
        if 'ezproxy.ugm.ac.id' in current_url:
            self.console.print(f"[green]✓ Login verified! Using ezproxy URL: {current_url}[/green]")
        elif 'login' in current_url.lower():
            self.console.print("[yellow]⚠️  Redirected to login page. Please try again.[/yellow]")
        else:
            self.console.print(f"[yellow]⚠️  Current URL: {current_url}. Proceeding anyway...[/yellow]")
