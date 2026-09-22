#!/usr/bin/env python3
"""List candidate HOL declarations to port before a chosen goal theorem.

This is a navigation aid, not a dependency analysis or a proof of missing work:
an untagged declaration may have an untagged Lean analogue, and an existing tag
does not establish semantic equivalence. Review both sources before claiming a
candidate or adding a tag.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / ".hol-index" / "hol-index.tsv"
SOURCE_SHA = ROOT / ".hol-index" / "source.sha"


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    path: str
    start: int
    end: int


def read_index(path: Path) -> list[Declaration]:
    declarations = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        kind, name, location, _theory = line.split("\t")
        source, span = location.rsplit(":", 1)
        start, end = span.split("-", 1)
        declarations.append(Declaration(kind, name, source, int(start), int(end)))
    return declarations


def read_mapping(output: str) -> set[tuple[str, str]]:
    return {
        (hol_path.removeprefix("cakeml/"), hol_name)
        for line in output.splitlines()
        for _lean_site, _lean_name, hol_path, hol_name in [line.split("\t")]
    }


def candidates(
    declarations: list[Declaration],
    tagged: set[tuple[str, str]],
    source: str,
    goal: str | None,
    kinds: set[str],
) -> tuple[list[Declaration], int]:
    in_file = [entry for entry in declarations if entry.path == source]
    if not in_file:
        raise ValueError(f"no indexed declarations in cakeml/{source}")
    cutoff = None
    if goal is not None:
        matches = [entry for entry in in_file if entry.name == goal]
        if len(matches) != 1:
            raise ValueError(f"expected one declaration named {goal!r} in cakeml/{source}; found {len(matches)}")
        cutoff = matches[0].start
    in_scope = [entry for entry in in_file if cutoff is None or entry.start < cutoff]
    tagged_count = sum((entry.path, entry.name) in tagged for entry in in_scope)
    remaining = [
        entry for entry in in_scope
        if entry.kind in kinds and (entry.path, entry.name) not in tagged
    ]
    return sorted(remaining, key=lambda entry: (entry.start, entry.name)), tagged_count


def current_index() -> None:
    revision = subprocess.check_output(
        ["git", "-C", str(ROOT / "cakeml"), "rev-parse", "HEAD"], text=True
    ).strip()
    if INDEX.is_file() and SOURCE_SHA.is_file() and SOURCE_SHA.read_text().strip() == revision:
        return
    subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "index-hol.py")],
        cwd=ROOT, check=True, stdout=subprocess.DEVNULL,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", required=True, help="HOL script path under cakeml/")
    parser.add_argument("--goal", help="list declarations earlier than this HOL declaration")
    parser.add_argument("--kind", action="append", choices=["Definition", "Theorem", "Triviality", "Datatype"],
                        help="kind to list (repeatable; default: Definition)")
    parser.add_argument("--limit", type=int, default=20, help="maximum candidates to print (default: 20)")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    source = args.file.removeprefix("cakeml/")
    if not source.startswith("pancake/") or not source.endswith(".sml") or ".." in Path(source).parts:
        parser.error("--file must name a script under cakeml/pancake/")
    try:
        current_index()
        mapping = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "check-hol-refs.py"), "--mapping"],
            cwd=ROOT, check=True, capture_output=True, text=True,
        ).stdout
        found, tagged_count = candidates(
            read_index(INDEX), read_mapping(mapping), source, args.goal,
            set(args.kind or ["Definition"]),
        )
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        parser.exit(1, f"error: {error}\n")
    scope = f" before {args.goal}" if args.goal else ""
    print(f"cakeml/{source}{scope}: {tagged_count} tagged; {len(found)} untagged candidates")
    print("Candidates only: inspect HOL dependencies, Lean analogues, and issue claims before porting.")
    for entry in found[: args.limit]:
        print(f"{entry.kind}\t{entry.name}\tcakeml/{entry.path}:{entry.start}\t{entry.end - entry.start + 1} lines")
    if len(found) > args.limit:
        print(f"... {len(found) - args.limit} more; use --limit or --goal to narrow the list")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
