#!/usr/bin/env python3
"""Profile a generated SMT-LIB script one command at a time.

The profiler replays exactly the input commands. It relies on
`(set-option :print-success true)` for per-command response boundaries.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from time import perf_counter

SAT_RESPONSES = {"sat", "unsat", "unknown"}
PREFIX_WIDTH = 18
SLOWEST_COUNT = 20


def split_toplevel(text: str) -> list[str]:
    commands: list[str] = []
    depth = 0
    start: int | None = None
    i = 0
    in_string = False

    while i < len(text):
        c = text[i]
        if in_string:
            if c == '"':
                if i + 1 < len(text) and text[i + 1] == '"':
                    i += 2
                    continue
                in_string = False
            i += 1
            continue
        if c == ";":
            j = text.find("\n", i)
            i = len(text) if j == -1 else j + 1
            continue
        if c == '"':
            in_string = True
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth < 0:
                raise ValueError(f"unmatched ')' at byte {i}")
            if depth == 0:
                commands.append(text[start : i + 1])
                start = None
        i += 1

    if depth != 0:
        raise ValueError("unterminated top-level s-expression")
    return commands


def head(command: str) -> str:
    body = command.lstrip()[1:].lstrip()
    return body.split(None, 1)[0].rstrip(")").lower()


def print_success(command: str) -> bool:
    return " ".join(command.lower().split()) == "(set-option :print-success true)"


def response_ok(command: str, response: str) -> bool:
    return response in SAT_RESPONSES if head(command) == "check-sat" else response == "success"


def short(command: str, limit: int = 90) -> str:
    text = " ".join(command.split())
    return text if len(text) <= limit else text[: limit - 3] + "..."


def print_profile_line(line: int, seconds: float, command: str) -> None:
    lines = command.splitlines() or [""]
    print(f"{line:5d} : {seconds:6.2f}s | {lines[0]}")
    for extra in lines[1:]:
        print(f"{' ' * PREFIX_WIDTH}{extra}")


def read_input(path: str | None) -> str:
    return sys.stdin.read() if path in {None, "-"} else Path(path).read_text()


def die(message: str) -> int:
    print(f"ERROR: {message}", file=sys.stderr)
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Profile a Z3 SMT-LIB script command-by-command.",
        epilog=(
            "Examples: lake exe mica --smt-commands-only Examples/foo.ml "
            "| python3 scripts/smt_profile.py; "
            "scripts/smt_profile.py run.smt2 > run.trace"
        ),
    )
    parser.add_argument("script", nargs="?", help="SMT-LIB file; reads stdin if omitted")
    parser.add_argument("--z3", default="z3")
    args = parser.parse_args()

    try:
        commands = split_toplevel(read_input(args.script))
    except OSError as err:
        return die(f"could not read {args.script or 'stdin'}: {err}")
    except ValueError as err:
        return die(f"invalid SMT-LIB input: {err}")
    if not commands:
        return die("no SMT-LIB commands found")

    try:
        z3 = subprocess.Popen(
            [args.z3, "-in"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except OSError as err:
        return die(f"could not start {args.z3}: {err}")
    if z3.stdin is None or z3.stdout is None:
        return die("failed to open pipes to z3")

    total = check_total = 0.0
    check_count = 0
    timings: list[tuple[int, float]] = []
    observable = False

    try:
        for line, command in enumerate(commands, start=1):
            is_check = head(command) == "check-sat"
            if not (observable or is_check or print_success(command)):
                return die(
                    "command has no observable response before "
                    f"`(set-option :print-success true)`: {line:5d} : {short(command)}"
                )

            start = perf_counter()
            z3.stdin.write(command + "\n")
            z3.stdin.flush()
            response = z3.stdout.readline()
            seconds = perf_counter() - start

            if response == "":
                stderr = z3.stderr.read() if z3.stderr is not None else ""
                if stderr:
                    print(stderr, file=sys.stderr, end="")
                return die("z3 exited early")
            response = response.strip()
            if not response_ok(command, response):
                return die(f"unexpected response to {line:5d} : {short(command)}: {response}")

            total += seconds
            timings.append((line, seconds))
            if is_check:
                check_total += seconds
                check_count += 1
            if print_success(command):
                observable = True
            print_profile_line(line, seconds, command)
    finally:
        if z3.poll() is None:
            z3.stdin.write("(exit)\n")
            z3.stdin.flush()
            z3.wait()

    print()
    print(f"total     : {total:.2f}s over {len(commands)} commands")
    print(f"check-sat : {check_total:.2f}s over {check_count} calls")
    print(f"other     : {total - check_total:.2f}s")
    slowest = sorted(timings, key=lambda item: item[1], reverse=True)[:SLOWEST_COUNT]
    entries = ", ".join(f"{line} ({seconds:.2f}s)" for line, seconds in slowest)
    print(f"slowest   : {entries}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
