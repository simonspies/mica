#!/usr/bin/env python3
"""Generate per-directory OUTLINE.md files summarizing Lean sources.

Usage:
    file_overview.py <directory>

Recursively descends into <directory>. In every directory that contains at
least one `.lean` file, writes an `OUTLINE.md` listing those files (sorted
alphabetically) alongside their one-line summary. A file's summary is the
text after `-- SUMMARY:` on the first matching line; files without such a
line are listed as `(none)`.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys


SUMMARY_RE = re.compile(r"^\s*--\s*SUMMARY:\s*(.*?)\s*$")


def extract_summary(path: pathlib.Path) -> str | None:
    try:
        with path.open("r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = SUMMARY_RE.match(line)
                if m:
                    return m.group(1).strip() or None
    except OSError as exc:
        print(f"warning: could not read {path}: {exc}", file=sys.stderr)
    return None


def write_outline(directory: pathlib.Path, root: pathlib.Path) -> None:
    lean_files = sorted(
        p for p in directory.iterdir() if p.is_file() and p.suffix == ".lean"
    )
    if not lean_files:
        return

    if directory == root:
        label = root.name
    else:
        label = (pathlib.Path(root.name) / directory.relative_to(root)).as_posix()

    lines = [f"**{label}**", ""]
    for f in lean_files:
        summary = extract_summary(f)
        lines.append(f"- `{f.name}` — {summary if summary else '(none)'}")

    out = directory / "OUTLINE.md"
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {out}")


def walk_dirs(root: pathlib.Path) -> list[pathlib.Path]:
    """Return directories under root, pruning hidden subdirectories."""
    dirs = [root]
    stack = [root]
    while stack:
        directory = stack.pop()
        children = sorted(
            p for p in directory.iterdir() if p.is_dir() and not p.name.startswith(".")
        )
        dirs.extend(children)
        stack.extend(reversed(children))
    return dirs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("directory", type=pathlib.Path)
    args = parser.parse_args()

    root: pathlib.Path = args.directory.resolve()
    if not root.is_dir():
        print(f"error: {root} is not a directory", file=sys.stderr)
        return 1

    for d in walk_dirs(root):
        write_outline(d, root)
    return 0


if __name__ == "__main__":
    sys.exit(main())
