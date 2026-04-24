#!/usr/bin/env python3
"""Generate markdown outlines of Lean files using the Lean LSP.

Usage:
    lean_outline.py <path/to/file.lean>   # emit outline to stdout
    lean_outline.py --all                 # write <file>.lean.md next to every
                                          # tracked source file (Main.lean,
                                          # Mica.lean, Mica/**/*.lean)

Spawns `lake env lean --server`, blocks on `waitForDiagnostics` until the file
is elaborated, then walks the `semanticTokens/full` stream for declaration
keywords (`def`, `theorem`, `inductive`, ...). For each, hovers at the
identifier to get the elaborated signature and docstring; for `inductive` /
`structure` / `class`, also appends the source body (constructors or fields)
from a `foldingRange` slice. Anonymous instances and notation/syntax/macro
declarations are emitted as source slices since they have no identifier to
hover.

This bypasses `documentSymbol`, which omits decls inside `mutual` blocks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
import time
from typing import Any
from urllib.parse import quote


FRONTMATTER_RE = re.compile(r"\A---\n(.*?)\n---\n", re.DOTALL)


def source_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_cached_hash(path: pathlib.Path) -> str | None:
    """Parse src-sha256 out of the YAML frontmatter of an existing outline."""
    try:
        head = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    m = FRONTMATTER_RE.match(head)
    if not m:
        return None
    for line in m.group(1).splitlines():
        k, _, v = line.partition(":")
        if k.strip() == "src-sha256":
            return v.strip()
    return None


def with_frontmatter(body: str, sha: str) -> str:
    return f"---\nsrc-sha256: {sha}\n---\n{body}"


# Decls handled by hovering at the identifier. The signature comes from hover
# (with explicit implicits and elaborated types); the docstring comes from
# hover too.
HOVER_KEYWORDS = {"def", "theorem", "lemma", "abbrev", "opaque", "axiom"}

# Inductives, structures, classes: hover gives only the head signature, so we
# also append the source body (constructors / fields) as comments.
BODY_KEYWORDS = {"inductive", "structure", "class"}

# No useful identifier to hover; emit the source slice verbatim.
VERBATIM_KEYWORDS = {"notation", "syntax", "macro"}

# `instance` is special: named instances hover normally, anonymous ones
# (`instance : BEq Foo := ...`) fall back to a source slice trimmed at `:=`.
INSTANCE_KEYWORD = "instance"

DECL_KEYWORDS = HOVER_KEYWORDS | BODY_KEYWORDS | VERBATIM_KEYWORDS | {INSTANCE_KEYWORD}

# After a decl keyword, the identifier starts at the first non-whitespace
# character that isn't `:`, `(`, `{`, or `[` (which would mark an anonymous
# decl or a binder before the name).
IDENT_AFTER_KEYWORD = re.compile(r"\s*[^\s:({\[]")


# ---------- LSP transport ----------

def send(w: Any, msg: dict[str, Any]) -> None:
    body = json.dumps(msg, separators=(",", ":")).encode("utf-8")
    w.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii"))
    w.write(body)
    w.flush()


def recv(r: Any) -> dict[str, Any]:
    cl: int | None = None
    while True:
        line = r.readline()
        if not line:
            raise EOFError("LSP stream closed")
        text = line.decode("ascii").strip()
        if text == "":
            break
        if text.lower().startswith("content-length:"):
            cl = int(text.split(":", 1)[1].strip())
    if cl is None:
        raise RuntimeError("missing Content-Length")
    return json.loads(r.read(cl).decode("utf-8"))


def request(proc: Any, rid: int, method: str, params: dict[str, Any]) -> Any:
    """Send a request and block for its response. Skips notifications and
    server-initiated requests, which reuse the id space and would otherwise
    be mistaken for our response."""
    send(proc.stdin, {"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
    while True:
        msg = recv(proc.stdout)
        if msg.get("id") == rid and "method" not in msg:
            if "error" in msg:
                raise RuntimeError(f"{method}: {msg['error']}")
            return msg.get("result")


def notify(proc: Any, method: str, params: dict[str, Any]) -> None:
    send(proc.stdin, {"jsonrpc": "2.0", "method": method, "params": params})


# ---------- semantic tokens ----------

def decode_tokens(data: list[int], token_types: list[str]) -> list[tuple[int, int, int, str]]:
    """Decode the LSP relative-delta token stream into absolute
    (line, col, length, type_name) tuples."""
    out: list[tuple[int, int, int, str]] = []
    line = col = 0
    for i in range(0, len(data), 5):
        dl, dc, length, tt, _tm = data[i:i + 5]
        if dl:
            col = 0
        line += dl
        col += dc
        out.append((line, col, length, token_types[tt]))
    return out


def find_decls(
    text: str, tokens: list[tuple[int, int, int, str]]
) -> list[tuple[int, str, int | None]]:
    """For each declaration-keyword token, return (line, keyword,
    identifier_column). identifier_column is None when the decl is
    anonymous (e.g. `instance : BEq Foo`)."""
    lines = text.splitlines()
    out: list[tuple[int, str, int | None]] = []
    for line_idx, col, length, ttype in tokens:
        if ttype != "keyword" or line_idx >= len(lines):
            continue
        kw = lines[line_idx][col:col + length]
        if kw not in DECL_KEYWORDS:
            continue
        m = IDENT_AFTER_KEYWORD.match(lines[line_idx], col + length)
        ident_col = (m.end() - 1) if m else None
        out.append((line_idx, kw, ident_col))
    return out


# ---------- hover parsing ----------

def parse_hover(result: dict[str, Any] | None) -> tuple[str, str | None] | None:
    """Parse Lean's hover into (signature, docstring|None). Returns None when
    hover landed on something that isn't a declaration (returned plain text
    rather than a fenced signature)."""
    if not result:
        return None
    contents = result.get("contents") or {}
    value = contents.get("value") if isinstance(contents, dict) else None
    if not isinstance(value, str):
        return None
    sig_block, _, doc = value.partition("\n***\n")
    sig_block = sig_block.strip()
    doc = doc.strip() or None
    if not sig_block.startswith("```"):
        return None
    lines = sig_block.splitlines()
    if lines and lines[0].startswith("```"):
        lines = lines[1:]
    if lines and lines[-1].strip() == "```":
        lines = lines[:-1]
    sig = "\n".join(lines).strip()
    if not sig:
        return None
    return sig, doc


# ---------- rendering ----------

def comment_lines(src: str) -> str:
    return "\n".join(f"-- {l}" if l else "--" for l in src.splitlines())


def render(entries: list[tuple[str, str | None]]) -> str:
    blocks: list[str] = []
    for sig, doc in entries:
        block = (comment_lines(doc) + "\n" + sig) if doc else sig
        blocks.append(block)
    return "```lean\n" + "\n\n".join(blocks) + "\n```\n"


# ---------- driver ----------

def collect_entries(
    text: str,
    decls: list[tuple[int, str, int | None]],
    region_end: dict[int, int],
    hover: Any,
) -> list[tuple[str, str | None]]:
    source_lines = text.splitlines()

    def slice_region(line: int) -> str:
        end = region_end.get(line, line)
        return "\n".join(source_lines[line:end + 1]).rstrip()

    entries: list[tuple[str, str | None]] = []
    for line, kw, ident_col in decls:
        verbatim = kw in VERBATIM_KEYWORDS or (kw == INSTANCE_KEYWORD and ident_col is None)
        if verbatim:
            src = slice_region(line)
            if kw == INSTANCE_KEYWORD:
                idx = src.find(":=")
                if idx >= 0:
                    src = src[:idx].rstrip()
            if src:
                entries.append((src, None))
            continue

        if ident_col is None:
            continue
        parsed = hover(line, ident_col)
        if not parsed:
            continue
        sig, doc = parsed
        if kw in BODY_KEYWORDS:
            body = slice_region(line)
            if body:
                sig = sig + "\n" + comment_lines(body)
        entries.append((sig, doc))
    return entries


class LeanServer:
    """One `lake env lean --server` process reused across many files."""

    def __init__(self, root: pathlib.Path) -> None:
        root_uri = "file://" + quote(str(root.resolve()), safe="/:")
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        init = request(self.proc, 1, "initialize",
                       {"processId": None, "rootUri": root_uri, "capabilities": {}})
        self.token_types = init["capabilities"]["semanticTokensProvider"]["legend"]["tokenTypes"]
        notify(self.proc, "initialized", {})
        self.rid = 100

    def next_id(self) -> int:
        self.rid += 1
        return self.rid

    def outline(self, path: pathlib.Path) -> str:
        text = path.read_text(encoding="utf-8")
        uri = "file://" + quote(str(path.resolve()), safe="/:")

        notify(self.proc, "textDocument/didOpen", {
            "textDocument": {"uri": uri, "languageId": "lean", "version": 1, "text": text},
        })
        try:
            request(self.proc, self.next_id(), "textDocument/waitForDiagnostics",
                    {"uri": uri, "version": 1})
            sem = request(self.proc, self.next_id(), "textDocument/semanticTokens/full",
                          {"textDocument": {"uri": uri}}) or {}
            tokens = decode_tokens(sem.get("data", []), self.token_types)
            decls = find_decls(text, tokens)

            folds = request(self.proc, self.next_id(), "textDocument/foldingRange",
                            {"textDocument": {"uri": uri}}) or []
            region_end = {int(f["startLine"]): int(f["endLine"])
                          for f in folds if f.get("kind") == "region"}

            def hover(line: int, col: int) -> tuple[str, str | None] | None:
                result = request(self.proc, self.next_id(), "textDocument/hover", {
                    "textDocument": {"uri": uri},
                    "position": {"line": line, "character": col},
                })
                return parse_hover(result)

            entries = collect_entries(text, decls, region_end, hover)
        finally:
            notify(self.proc, "textDocument/didClose", {"textDocument": {"uri": uri}})

        try:
            title = str(path.resolve().relative_to(pathlib.Path.cwd().resolve()))
        except ValueError:
            title = path.name
        return f"# {title}\n\n{render(entries)}"

    def close(self) -> None:
        try:
            notify(self.proc, "exit", {})
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=2)
        except Exception:
            self.proc.kill()


def write_readonly(path: pathlib.Path, content: str) -> None:
    """Write content, clearing write bits afterwards. Clears read-only first
    so re-running the script doesn't trip on an existing locked file."""
    if path.exists():
        path.chmod(path.stat().st_mode | stat.S_IWUSR)
    path.write_text(content, encoding="utf-8")
    mode = path.stat().st_mode
    path.chmod(mode & ~(stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH))


def collect_all_sources(root: pathlib.Path) -> list[pathlib.Path]:
    """Leaves first, roots last: process Mica/**/*.lean, then Mica.lean, then
    Main.lean. The first few files pay to warm the import cache; putting the
    roots last means they can reuse it."""
    files: list[pathlib.Path] = []
    mica = root / "Mica"
    if mica.exists():
        files.extend(sorted(mica.rglob("*.lean")))
    for top in ("Mica.lean", "Main.lean"):
        p = root / top
        if p.exists():
            files.append(p)
    return files


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("path", nargs="?", help="single .lean file; outline goes to stdout")
    ap.add_argument("--all", action="store_true",
                    help="write <file>.lean.md next to Main.lean, Mica.lean, and Mica/**/*.lean")
    ap.add_argument("--from-scratch", action="store_true",
                    help=("regenerate every outline. Without this, --all skips files "
                          "whose source sha256 matches the src-sha256 in the existing "
                          "outline's YAML frontmatter. Note that only the file's own "
                          "bytes are hashed: a change in a dependency could modify the "
                          "output when generated from scratch, but would not change the "
                          "contents of the file."))
    args = ap.parse_args()
    if args.all == bool(args.path):
        ap.error("pass either a single path or --all")

    root = pathlib.Path.cwd()

    if args.all and not args.from_scratch:
        all_files = collect_all_sources(root)
        files: list[tuple[pathlib.Path, str]] = []
        skipped = 0
        for p in all_files:
            text = p.read_text(encoding="utf-8")
            sha = source_hash(text)
            target = p.with_suffix(p.suffix + ".md")
            if target.exists() and read_cached_hash(target) == sha:
                skipped += 1
                continue
            files.append((p, sha))
        print(f"skipping {skipped} unchanged, regenerating {len(files)}", file=sys.stderr)
    elif args.all:
        files = [(p, source_hash(p.read_text(encoding="utf-8")))
                 for p in collect_all_sources(root)]

    server = LeanServer(root)
    try:
        if args.all:
            total_start = time.monotonic()
            for i, (path, sha) in enumerate(files, 1):
                t0 = time.monotonic()
                try:
                    out = server.outline(path)
                except Exception as e:
                    dt = time.monotonic() - t0
                    print(f"[{i}/{len(files)}] {path}  FAILED in {dt:.1f}s: {e}",
                          file=sys.stderr)
                    continue
                target = path.with_suffix(path.suffix + ".md")
                write_readonly(target, with_frontmatter(out, sha))
                dt = time.monotonic() - t0
                print(f"[{i}/{len(files)}] {path}  {dt:.1f}s", file=sys.stderr)
            total = time.monotonic() - total_start
            print(f"done: {len(files)} files in {total:.1f}s", file=sys.stderr)
            return 0
        else:
            sys.stdout.write(server.outline(pathlib.Path(args.path)))
            return 0
    finally:
        server.close()


if __name__ == "__main__":
    raise SystemExit(main())
