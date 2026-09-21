#!/usr/bin/env python3
"""Check every minimized Cake frame-occupancy fixture for exact bytes.

The fixtures are the original Pancake/CakeML witnesses used by bead
``flapjack-pxn.8.5.14.1.3``.  Keep this campaign separate from the broader
small corpus because its sources and checked Cake assembly vectors are
specifically about frame occupancy and allocator temporary slots.  The
``.cake.S`` files beside the sources are checked-in Cake outputs, so this
check does not require the ignored/local Cake executable in CI.
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
    failures = 0
    for path in fixtures:
        reference = path.with_suffix(".cake.S")
        if not reference.is_file():
            print(f"missing Cake oracle: {reference}", file=sys.stderr)
            failures += 1
            continue
        result = subprocess.run(
            [sys.executable, str(PARITY), "--reference", str(reference), str(path)],
            cwd=REPO_ROOT,
        )
        failures += result.returncode != 0
    print(f"frame fixtures={len(fixtures)} failures={failures}")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
