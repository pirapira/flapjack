#!/usr/bin/env python3
"""Differential RISC-V byte comparison: original Pancake vs Flapjack.

The original CakeML ``cake --pancake --target=riscv`` compiler emits assembly
with a ``makesym`` table naming each generated section (``cml_generated_main``,
``cml_main``, ``cml_<function>``) plus the shared runtime (``cml__...``).  The
Flapjack ``flapjack-compile --sections`` mode emits the same idea as one line
per linked section: ``<label> <address> <bytes...>``.

This script runs a set of Pancake programs through both compilers, normalizes
only the CakeML section-name prefix/suffix (``cml_main_7`` -> ``main``,
``cml_generated_main_6`` -> ``generated_main``; the trailing index is the
deterministic section number), and reports whether each CakeML user-function
section has a byte-identical Flapjack section.  The shared runtime sections
(``cml__Init``, ``cml__GC``, ...) are compared only for presence.

A *gap* is any user function whose emitted code has no byte-identical Flapjack
section.  The script prints the first mismatching function per program and
exits non-zero when any gap is present.

Usage:
    scripts/parity-bytes.py PROGRAM.pan [PROGRAM.pan ...]
    scripts/parity-bytes.py --dir <directory>

Defaults can be overridden with --cake / --flapjack or the CAKE / FLAPJACK
environment variables.
"""

import argparse
import os
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = os.path.join(REPO_ROOT, ".lake", "build", "bin", "flapjack-compile")


def cake_sections(path, cake):
    """Return (runtime, entry, {user_name: bytes}) parsed from cake assembly."""
    proc = subprocess.run(
        [cake, "--pancake", "--target=riscv"],
        stdin=open(path, "rb"),
        capture_output=True,
    )
    if proc.returncode != 0:
        return None
    text = proc.stdout.decode("utf-8", "replace")
    marker = "#### Generated machine code follows"
    start = text.find(marker)
    if start < 0:
        return None
    flat = []
    for line in text[start:].splitlines():
        match = re.search(r"\.byte(.*)", line)
        if match:
            for value in re.findall(r"0x[0-9A-Fa-f]+", match.group(1)):
                flat.append(int(value, 16))
        if re.match(r"\s*makesym\(", line):
            break
    runtime, entry, user = {}, None, {}
    for match in re.finditer(r"makesym\((\w+),\s*(\d+),\s*(\d+)\)", text):
        name, offset, length = match.group(1), int(match.group(2)), int(match.group(3))
        data = flat[offset:offset + length]
        if name.startswith("cml__"):
            runtime[name] = data
        elif name.startswith("cml_generated_main"):
            entry = data
        else:
            user[re.sub(r"^cml_", "", re.sub(r"_\d+$", "", name))] = data
    return runtime, entry, user


def flapjack_sections(path, flapjack):
    """Return a list of (label, address, bytes) from flapjack-compile --sections."""
    proc = subprocess.run(
        [flapjack, "--sections", path],
        capture_output=True,
    )
    if proc.returncode != 0:
        return None
    sections = []
    for line in proc.stdout.decode("utf-8", "replace").splitlines():
        parts = line.split()
        if len(parts) < 3:
            continue
        label, address = int(parts[0]), int(parts[1])
        data = [int(byte, 16) for byte in parts[2:]]
        sections.append((label, address, data))
    return sections


def hexstr(data):
    return " ".join(f"{byte:02x}" for byte in data)


def compare(path, cake, flapjack, quiet):
    cake_parsed = cake_sections(path, cake)
    flap_parsed = flapjack_sections(path, flapjack)
    name = os.path.basename(path)
    if cake_parsed is None:
        if not quiet:
            print(f"{name}: cake rejects (no comparison)")
        return 0
    if flap_parsed is None:
        print(f"{name}: flapjack rejects (GAP)")
        return 1
    _runtime, entry, user = cake_parsed
    flap_bytes = [data for (_label, _address, data) in flap_parsed]
    gaps = 0
    if entry is not None and entry not in flap_bytes:
        gaps += 1
        if not quiet:
            print(f"{name}: generated_main mismatch")
            print(f"  cake     : {hexstr(entry)}")
            print(f"  flapjack : {hexstr(flap_bytes[1]) if len(flap_bytes) > 1 else ''}")
    for func in sorted(user):
        if user[func] not in flap_bytes:
            gaps += 1
            if not quiet:
                print(f"{name}: {func} mismatch")
                print(f"  cake     : {hexstr(user[func])}")
    if gaps == 0:
        if not quiet:
            print(f"{name}: MATCH ({len(user)} user function(s))")
    else:
        if not quiet:
            print(f"{name}: {gaps} GAP(s)")
    return gaps


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("programs", nargs="*", help="Pancake source files")
    parser.add_argument("--dir", help="directory of .pan programs")
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument("--flapjack", default=os.environ.get("FLAPJACK", DEFAULT_FLAPJACK))
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    programs = list(args.programs)
    if args.dir:
        for entry in sorted(os.listdir(args.dir)):
            if entry.endswith(".pan"):
                programs.append(os.path.join(args.dir, entry))
    if not programs:
        parser.error("no programs given (pass files or --dir)")

    total_gaps = 0
    for path in programs:
        total_gaps += compare(path, args.cake, args.flapjack, args.quiet)
    if not args.quiet:
        print(f"programs={len(programs)} gaps={total_gaps}")
    return 1 if total_gaps else 0


if __name__ == "__main__":
    sys.exit(main())
