"""Start Beat the Blast in a browser or on the desktop."""

import asyncio
import sys

# pygbag only loads pygame in the browser when main.py imports it directly.
import pygame  # noqa: F401

from beat_the_blast import App


async def play_in_browser():
    """Run the game while letting the browser update between frames."""
    app = App()
    await app.run_browser()


if __name__ == "__main__":
    if sys.platform == "emscripten":
        asyncio.run(play_in_browser())
    else:
        from beat_the_blast import main
        sys.exit(main())
