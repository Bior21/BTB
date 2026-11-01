"""Start Beat the Blast in a browser using pygbag, or on the desktop."""

import asyncio
import sys

from beat_the_blast import App, main


async def play_in_browser():
    """Create the game and run frames without blocking the browser."""
    app = App()
    await app.run_browser()


if __name__ == "__main__":
    if sys.platform == "emscripten":
        asyncio.run(play_in_browser())
    else:
        sys.exit(main())
