"""Prepare browser files without the desktop-only testing modules."""

import ast
from pathlib import Path
import shutil


TEST_NAMES = {
    "FakeClock", "TinyMaze", "escape", "PlayerTests", "MazeTests",
    "DemoTests", "GameTests", "InterfaceTests", "run_tests", "main",
}


def browser_source(source):
    """Remove test imports, test definitions, and the desktop launcher."""
    tree = ast.parse(source)
    lines = source.splitlines(keepends=True)
    removed = set()
    for node in tree.body:
        test_import = isinstance(node, ast.Import) and any(
            item.name in ("doctest", "unittest") for item in node.names)
        mock_import = (
            isinstance(node, ast.ImportFrom)
            and node.module == "unittest.mock"
        )
        test_name = getattr(node, "name", "") in TEST_NAMES
        launcher = (
            isinstance(node, ast.If)
            and ast.unparse(node.test) == "__name__ == '__main__'"
        )
        if test_import or mock_import or test_name or launcher:
            start = min(
                [node.lineno]
                + [item.lineno for item in getattr(node, "decorator_list", [])]
            )
            removed.update(range(start, node.end_lineno + 1))
    return "".join(
        line for number, line in enumerate(lines, 1)
        if number not in removed
    )


def prepare():
    """Write the browser game and entry point into web-src."""
    root = Path(__file__).resolve().parent
    target = root / "web-src"
    target.mkdir(exist_ok=True)
    source = (root / "beat_the_blast.py").read_text()
    (target / "beat_the_blast.py").write_text(browser_source(source))
    shutil.copyfile(root / "main.py", target / "main.py")
    # The browser cannot use fonts installed on a computer, so ship the game's own.
    shutil.copytree(root / "fonts", target / "fonts", dirs_exist_ok=True)


if __name__ == "__main__":
    prepare()
