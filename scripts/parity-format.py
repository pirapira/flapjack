#!/usr/bin/env python3
"""Audit the RISC-V assembly envelope emitted by CakeML and Flapjack.

This is deliberately separate from ``parity-bytes.py``: generated/user code
bytes may differ while the artifact serialization must remain identical.  The
audit compares the complete non-payload frame byte-for-byte, then validates
the payload and symbol-line grammar on both outputs.

The upstream reference is ``cake --pancake --target=riscv``.  Flapjack is
invoked with ``--assembly`` because that is the public Pancake-compatible
format alias.
"""

import argparse
import os
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = os.path.join(REPO_ROOT, ".lake", "build", "bin", "flapjack-compile")
BYTE_LINE = re.compile(r"^\t\.byte (0x[0-9A-F]{2}(?:,0x[0-9A-F]{2}){0,15})$")
SYMBOL_LINE = re.compile(r"^    makesym\(\w+, \d+, \d+\)$")


def run_compiler(command, path):
    process = subprocess.run(command, stdin=open(path, "rb"), capture_output=True)
    if process.returncode != 0:
        return None, process.stderr.decode("utf-8", "replace")
    return process.stdout.decode("utf-8", "replace"), ""


def inspect_frame(text, label):
    """Return the static frame and validate payload/symbol serialization."""
    lines = text.splitlines()
    if "cake_main:" not in lines:
        raise ValueError(f"{label}: missing cake_main marker")

    static = []
    byte_lines = 0
    for line_number, line in enumerate(lines, 1):
        if ".byte" in line:
            match = BYTE_LINE.fullmatch(line)
            if match is None:
                raise ValueError(f"{label}: malformed .byte line {line_number}: {line!r}")
            byte_lines += 1
            continue
        if line.lstrip().startswith("makesym("):
            if SYMBOL_LINE.fullmatch(line) is None:
                raise ValueError(
                    f"{label}: malformed makesym line {line_number}: {line!r}"
                )
            continue
        static.append(line)

    if byte_lines == 0:
        raise ValueError(f"{label}: no .byte payload lines")
    return static


def compare(path, cake, flapjack):
    cake_text, cake_error = run_compiler(
        [cake, "--pancake", "--target=riscv"], path
    )
    if cake_text is None:
        print(f"{os.path.basename(path)}: cake rejects (no comparison)")
        return 0

    flap_text, flap_error = run_compiler([flapjack, "--assembly"], path)
    if flap_text is None:
        print(f"{os.path.basename(path)}: flapjack rejects (GAP)")
        if flap_error:
            print(f"  {flap_error.strip()}")
        return 1

    try:
        cake_static = inspect_frame(cake_text, "cake")
        flap_static = inspect_frame(flap_text, "flapjack")
    except ValueError as error:
        print(f"{os.path.basename(path)}: FORMAT GAP: {error}")
        return 1

    if cake_static != flap_static:
        print(f"{os.path.basename(path)}: FORMAT GAP: static frame differs")
        for index, (cake_line, flap_line) in enumerate(
            zip(cake_static, flap_static), 1
        ):
            if cake_line != flap_line:
                print(f"  first difference at static line {index}")
                print(f"  cake:     {cake_line!r}")
                print(f"  flapjack: {flap_line!r}")
                break
        else:
            print(
                f"  line counts differ: cake={len(cake_static)} "
                f"flapjack={len(flap_static)}"
            )
        return 1

    print(f"{os.path.basename(path)}: FORMAT MATCH")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("programs", nargs="+", help="Pancake source files")
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument(
        "--flapjack", default=os.environ.get("FLAPJACK", DEFAULT_FLAPJACK)
    )
    args = parser.parse_args(argv)
    gaps = sum(compare(path, args.cake, args.flapjack) for path in args.programs)
    print(f"programs={len(args.programs)} format_gaps={gaps}")
    return 1 if gaps else 0


if __name__ == "__main__":
    sys.exit(main())
