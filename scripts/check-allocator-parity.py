#!/usr/bin/env python3
"""Check the original-Cake allocator witnesses for exact RISC-V bytes.

These fixtures exercise distinct allocator/frame shapes: dead-raise
allocation, colour permutation, returned-value allocation, 64-bit
register pressure, and a stack-allocation boundary.  Keep the list explicit
so a change in the checked original-Cake witnesses is reviewable.
"""

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
PARITY = REPO_ROOT / "scripts" / "parity-bytes.py"
FIXTURES = (
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00634_dead_raise.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "allocator_colour_permutation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00068_allocator_return.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "mul64x64_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1049_stack_alloc.pnk",
)


def main() -> int:
    missing = [path for path in FIXTURES if not path.is_file()]
    if missing:
        for path in missing:
            print(f"missing allocator fixture: {path}", file=sys.stderr)
        return 2
    return subprocess.run(
        [sys.executable, str(PARITY), *(str(path) for path in FIXTURES)],
        cwd=REPO_ROOT,
    ).returncode


if __name__ == "__main__":
    sys.exit(main())
