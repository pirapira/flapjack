#!/usr/bin/env python3
"""Check the pinned stateless Pancake guest against Flapjack.

The source is pinned by the workflow to a commit of the upstream guest
repository.  The expected stdout digest is the output of the authoritative
CakeML Pancake RISC-V compiler for that exact source.  This keeps the large
guest source and Cake executable out of CI while still checking the complete
Pancake-compatible artifact byte-for-byte.
"""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys


EXPECTED_SOURCE_SHA256 = (
    "daf135834eb1628faf498a768833b04e4c1e67168f6920e5065482fd358a55b4"
)
EXPECTED_CAKE_STDOUT_SHA256 = (
    "180794acc97366a671c98819019fbe09bea12ac8a506b4b441e29049986e94d7"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Check guest.pp.pnk output against pinned CakeML output."
    )
    parser.add_argument("source", type=Path)
    parser.add_argument(
        "--flapjack",
        default=os.environ.get("FLAPJACK", ".lake/build/bin/flapjack-compile"),
        type=Path,
    )
    args = parser.parse_args(argv)

    source_bytes = args.source.read_bytes()
    source_digest = sha256(source_bytes)
    if source_digest != EXPECTED_SOURCE_SHA256:
        print(
            f"guest source hash mismatch: expected {EXPECTED_SOURCE_SHA256}, "
            f"got {source_digest}",
            file=sys.stderr,
        )
        return 1

    result = subprocess.run(
        [str(args.flapjack), "--assembly", str(args.source)],
        capture_output=True,
    )
    actual = sha256(result.stdout)
    if result.returncode != 0 or actual != EXPECTED_CAKE_STDOUT_SHA256:
        print(
            f"guest.pp.pnk parity mismatch: returncode={result.returncode} "
            f"expected={EXPECTED_CAKE_STDOUT_SHA256} got={actual}",
            file=sys.stderr,
        )
        if result.stderr:
            sys.stderr.buffer.write(result.stderr)
        return 1

    print(
        "guest.pp.pnk exact Pancake parity "
        f"source={source_digest} stdout={actual}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
