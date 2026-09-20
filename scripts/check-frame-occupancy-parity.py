#!/usr/bin/env python3
"""Check every minimized Cake frame-occupancy fixture for exact bytes.

The fixtures are the original Pancake/CakeML witnesses used by bead
``flapjack-pxn.8.5.14.1.3``.  Keep this campaign separate from the broader
small corpus because its sources and checked Cake assembly vectors are
specifically about frame occupancy and allocator temporary slots.
"""

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_DIR = REPO_ROOT / "scripts" / "parity-difffuzz-findings" / "frame-occupancy"
PARITY = REPO_ROOT / "scripts" / "parity-bytes.py"


def main() -> int:
    fixtures = sorted(FIXTURE_DIR.glob("*.pnk"))
    if not fixtures:
        print(f"no frame fixtures found in {FIXTURE_DIR}", file=sys.stderr)
        return 2
    result = subprocess.run(
        [sys.executable, str(PARITY), *(str(path) for path in fixtures)],
        cwd=REPO_ROOT,
    )
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
