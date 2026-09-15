#!/usr/bin/env python3
"""Run exact Pancake/Flapjack checks for every checked-in golden artifact.

Each ``scripts/parity-goldens/<name>.cake.S`` file must have a matching
``Flapjack/Test/OriginalPancake/<name>.pnk`` source file.  Adding a new exact
end-to-end parity fixture therefore automatically adds it to CI.
"""

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
GOLDENS = ROOT / "scripts" / "parity-goldens"
SOURCES = ROOT / "Flapjack" / "Test" / "OriginalPancake"
PARITY = ROOT / "scripts" / "parity-bytes.py"


def main() -> int:
    goldens = sorted(GOLDENS.glob("*.cake.S"))
    if not goldens:
        print(f"no parity goldens found in {GOLDENS}", file=sys.stderr)
        return 1

    failures = 0
    for golden in goldens:
        name = golden.name.removesuffix(".cake.S")
        source = SOURCES / f"{name}.pnk"
        if not source.is_file():
            print(f"{golden}: missing matching source {source}", file=sys.stderr)
            failures += 1
            continue
        print(f"checking exact parity: {source.name}")
        result = subprocess.run(
            [
                sys.executable,
                str(PARITY),
                "--reference",
                str(golden),
                str(source),
            ],
            cwd=ROOT,
        )
        failures += result.returncode != 0

    print(f"parity goldens={len(goldens)} failures={failures}")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
