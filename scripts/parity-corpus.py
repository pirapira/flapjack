#!/usr/bin/env python3
"""Reproducible Pancake/RISC-V acceptance-corpus differential runner.

This extracts every Pancake program embedded in the CakeML submodule's
Pancake sources (backtick blocks that declare at least one ``fun``), then
compares how the original CakeML Pancake compiler and Flapjack's checked
source entry point react to each program:

* ``cake --pancake --target=riscv`` reads the program on standard input.
* ``flapjack-compile`` reads the program from a file.

Programs without a ``main`` are retried with a synthetic ``main`` appended so
the comparison exercises the whole source-to-RISC-V path rather than only the
entry-point lookup.

A *gap* is a program the original Pancake accepts but Flapjack rejects; those
are the high-priority porting bugs.  An *opposite* case is a program the
original rejects but Flapjack accepts; those are reported separately because
they can reflect intentional permissive Flapjack behaviour.

Usage::

    scripts/parity-corpus.py
    scripts/parity-corpus.py --out /var/tmp/pancake-corpus

The CakeML ``cake`` binary is taken from ``$CAKE`` and otherwise defaults to
``~/pancake-lean/cakeml/developers/bin/cake``.  ``flapjack-compile`` defaults
to this repository's ``.lake/build/bin/flapjack-compile``.  The extracted
programs and a ``results.txt`` summary are written under ``--out`` (a fresh
temporary directory by default).
"""

import argparse
import glob
import hashlib
import os
import re
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = os.path.join(REPO_ROOT, ".lake", "build", "bin", "flapjack-compile")
DEFAULT_SUBMODULE = os.path.join(REPO_ROOT, "cakeml", "pancake")

SYNTHETIC_MAIN = "\nfun 1 main() { return 0; }\n"
BACKTICK_BLOCK = re.compile(r"`([^`]*)`")


def extract_programs(root):
    """Return the deduplicated Pancake programs found in ``root``/*.sml."""
    programs = {}
    for path in glob.glob(os.path.join(root, "**", "*.sml"), recursive=True):
        with open(path, encoding="utf-8", errors="replace") as handle:
            source = handle.read()
        for block in BACKTICK_BLOCK.findall(source):
            if "fun " not in block:
                continue
            program = block.strip("\n") + "\n"
            digest = hashlib.sha1(program.encode("utf-8")).hexdigest()[:10]
            programs.setdefault(digest, program)
    return dict(sorted(programs.items()))


def write_corpus(programs, out_dir):
    """Write each program twice: as extracted, and with a synthetic main."""
    raw_dir = os.path.join(out_dir, "raw")
    main_dir = os.path.join(out_dir, "withmain")
    os.makedirs(raw_dir, exist_ok=True)
    os.makedirs(main_dir, exist_ok=True)
    written = []
    for digest, program in programs.items():
        raw_path = os.path.join(raw_dir, digest + ".pan")
        with open(raw_path, "w", encoding="utf-8") as handle:
            handle.write(program)
        with_main = program if "main" in program else program + SYNTHETIC_MAIN
        main_path = os.path.join(main_dir, digest + ".pan")
        with open(main_path, "w", encoding="utf-8") as handle:
            handle.write(with_main)
        written.append((digest, main_path))
    return written


def accepts_cake(cake, path):
    with open(path, encoding="utf-8") as handle:
        result = subprocess.run(
            [cake, "--pancake", "--target=riscv"],
            stdin=handle,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    return result.returncode == 0


def accepts_flapjack(flapjack, path):
    result = subprocess.run(
        [flapjack, os.path.abspath(path)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument(
        "--flapjack", default=os.environ.get("FLAPJACK", DEFAULT_FLAPJACK)
    )
    parser.add_argument("--submodule", default=DEFAULT_SUBMODULE)
    parser.add_argument("--out", help="corpus output directory")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    for name, path in (("cake", args.cake), ("flapjack", args.flapjack)):
        if not os.path.isfile(path):
            print("missing %s binary: %s" % (name, path), file=sys.stderr)
            return 2
    if not os.path.isdir(args.submodule):
        print("missing Pancake submodule directory: %s" % args.submodule, file=sys.stderr)
        return 2

    out_dir = args.out or tempfile.mkdtemp(
        prefix="flapjack-parity-corpus-",
        dir="/var/tmp" if os.path.isdir("/var/tmp") else None,
    )
    programs = extract_programs(args.submodule)
    written = write_corpus(programs, out_dir)

    both_ok = both_bad = gaps = opposite = 0
    gap_names, opposite_names = [], []
    lines = []
    for digest, path in written:
        cake_ok = accepts_cake(args.cake, path)
        flapjack_ok = accepts_flapjack(args.flapjack, path)
        if cake_ok and flapjack_ok:
            both_ok += 1
        elif not cake_ok and not flapjack_ok:
            both_bad += 1
        elif cake_ok:
            gaps += 1
            gap_names.append(digest)
        else:
            opposite += 1
            opposite_names.append(digest)
        lines.append(
            "%s cake=%d flapjack=%d" % (digest, 0 if cake_ok else 1, 0 if flapjack_ok else 1)
        )

    results = os.path.join(out_dir, "results.txt")
    with open(results, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")
    summary = "programs=%d both_ok=%d both_bad=%d gaps=%d opposite=%d out=%s" % (
        len(written),
        both_ok,
        both_bad,
        gaps,
        opposite,
        out_dir,
    )
    if not args.quiet:
        print(summary)
        for digest in gap_names:
            print("  GAP", digest)
        for digest in opposite_names:
            print("  OPP", digest)
    return 1 if gaps else 0


if __name__ == "__main__":
    sys.exit(main())
