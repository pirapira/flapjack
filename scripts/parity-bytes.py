#!/usr/bin/env python3
"""Direct RISC-V byte comparison: original Pancake vs Flapjack.

Both compilers now emit the *same* textual artifact format, so this script
parses each with one shared parser and compares the results without any
conversion layer:

* the original ``cake --pancake --target=riscv`` compiler emits assembly with
  a ``cake_main:`` marker, the linked code image as ``.byte`` lines, and a
  ``makesym(name, base, len)`` symbol table;
* the Flapjack ``flapjack-compile --assembly`` mode emits the same frame for
  the code image the port actually produces.

The shared parser reconstructs every ``makesym`` section and normalizes only
the deterministic symbol prefix/suffix (``cml_generated_main_7`` ->
``generated_main``, ``cml_main_7`` -> ``main``).  Programs the original
compiler rejects are skipped.  For every accepted program the script reports
each runtime/user section whose bytes or base differs between the two
compilers, plus the generated entry and any symbol/layout difference.

A *gap* is a byte mismatch in the generated entry or a user function.  The
script prints the first mismatch per section and exits non-zero when any gap
is present.

Usage:
    scripts/parity-bytes.py PROGRAM.pan [PROGRAM.pan ...]
    scripts/parity-bytes.py --dir <directory>

Defaults can be overridden with --cake / --flapjack or the CAKE / FLAPJACK
environment variables.
"""

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = os.path.join(REPO_ROOT, ".lake", "build", "bin", "flapjack-compile")


def parse_byte_line(content):
    values = []
    for token in content.split(","):
        token = token.strip()
        if not token:
            continue
        values.append(int(token, 16))
    return values


def parse_assembly(text):
    """Parse one artifact frame into ``{name: (base, bytes)}``.

    Both Cake assembly and ``flapjack-compile --assembly`` share this frame, so
    a single parser is used for both inputs.
    """
    marker = text.find("cake_main:")
    if marker < 0:
        marker = text.find("#### Generated machine code follows")
    if marker < 0:
        return None
    flat = []
    for line in text[marker:].splitlines():
        match = re.search(r"\.byte(.*)", line)
        if match:
            flat.extend(parse_byte_line(match.group(1)))
    sections = {}
    for match in re.finditer(r"makesym\((\w+),\s*(\d+),\s*(\d+)\)", text):
        name, base, length = match.group(1), int(match.group(2)), int(match.group(3))
        sections[name] = (base, flat[base:base + length])
    if not sections:
        return None
    return sections


def is_runtime(name):
    return name.startswith("cml__") or name.startswith("cml_flapjack_runtime")


def is_entry(name):
    return name.startswith("cml_generated_main")


def normalize(name):
    return re.sub(r"_\d+$", "", re.sub(r"^cml_", "", name))


def classify(sections):
    runtime, entry, user = {}, None, {}
    for name, (base, data) in sections.items():
        if is_runtime(name):
            runtime[name] = (base, data)
        elif is_entry(name):
            entry = (name, base, data)
        else:
            user[normalize(name)] = (name, base, data)
    return runtime, entry, user


def cake_assembly(path, cake):
    proc = subprocess.run(
        [cake, "--pancake", "--target=riscv"],
        stdin=open(path, "rb"),
        capture_output=True,
    )
    if proc.returncode != 0:
        return None
    return parse_assembly(proc.stdout.decode("utf-8", "replace"))


def flapjack_assembly(path, flapjack):
    proc = subprocess.run(
        [flapjack, "--assembly", path],
        capture_output=True,
    )
    if proc.returncode != 0:
        return None
    return parse_assembly(proc.stdout.decode("utf-8", "replace"))


def hexstr(data):
    return " ".join(f"{byte:02x}" for byte in data)


def compare_section(name, cake_section, flap_section, owner, quiet):
    """Compare one named section, including its offset and byte payload."""
    cake_base, cake_data = cake_section
    flap_base, flap_data = flap_section
    if cake_base == flap_base and cake_data == flap_data:
        return 0

    if not quiet:
        if cake_base != flap_base:
            print(f"{owner} {name} layout mismatch")
            print(f"  cake base: {cake_base}")
            print(f"  flapjack base: {flap_base}")
        if cake_data != flap_data:
            print(f"{owner} {name} mismatch")
            print(f"  cake     : {hexstr(cake_data)}")
            print(f"  flapjack : {hexstr(flap_data)}")
    return 1


def compare_section_maps(name, cake_sections, flap_sections, owner, quiet):
    """Compare exact-name sections and report missing/extra symbols."""
    gaps = 0
    for section in sorted(cake_sections):
        if section not in flap_sections:
            gaps += 1
            if not quiet:
                print(f"{owner} {section} missing in flapjack")
            continue
        gaps += compare_section(
            name, cake_sections[section], flap_sections[section], owner, quiet
        )
    for section in sorted(set(flap_sections) - set(cake_sections)):
        gaps += 1
        if not quiet:
            print(f"{owner} {section} unexpected in flapjack")
    return gaps


def compare(path, cake, flapjack, quiet, reference=None):
    name = os.path.basename(path)
    if reference is None:
        cake_sections = cake_assembly(path, cake)
    else:
        cake_sections = parse_assembly(reference.read_text(encoding="utf-8"))
        if cake_sections is None:
            print(f"{reference}: malformed reference artifact")
            return 1
    if cake_sections is None:
        if not quiet:
            print(f"{name}: cake rejects (no comparison)")
        return 0
    flap_sections = flapjack_assembly(path, flapjack)
    if flap_sections is None:
        print(f"{name}: flapjack rejects (GAP)")
        return 1

    cake_runtime, cake_entry, cake_user = classify(cake_sections)
    flap_runtime, flap_entry, flap_user = classify(flap_sections)
    gaps = 0

    gaps += compare_section_maps(
        name, cake_runtime, flap_runtime, "runtime", quiet
    )

    if cake_entry is not None:
        if flap_entry is None:
            gaps += 1
            if not quiet:
                print(f"{name}: generated_main missing in flapjack")
        else:
            gaps += compare_section(
                name,
                (cake_entry[1], cake_entry[2]),
                (flap_entry[1], flap_entry[2]),
                "generated_main",
                quiet,
            )
    elif flap_entry is not None:
        gaps += 1
        if not quiet:
            print(f"{name}: generated_main unexpected in flapjack")

    for func in sorted(cake_user):
        if func not in flap_user:
            gaps += 1
            if not quiet:
                print(f"{name}: {func} missing in flapjack")
            continue
        gaps += compare_section(
            name,
            (cake_user[func][1], cake_user[func][2]),
            (flap_user[func][1], flap_user[func][2]),
            "user",
            quiet,
        )

    for func in sorted(set(flap_user) - set(cake_user)):
        gaps += 1
        if not quiet:
            print(f"{name}: {func} unexpected in flapjack")

    if gaps == 0:
        if not quiet:
            print(f"{name}: MATCH ({len(cake_user)} user function(s))")
    return gaps


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("programs", nargs="*", help="Pancake source files")
    parser.add_argument("--dir", help="directory of .pan programs")
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument("--flapjack", default=os.environ.get("FLAPJACK", DEFAULT_FLAPJACK))
    parser.add_argument(
        "--reference",
        type=Path,
        help="use a checked-in original Cake artifact instead of invoking cake",
    )
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    programs = list(args.programs)
    if args.dir:
        for entry in sorted(os.listdir(args.dir)):
            if entry.endswith(".pan"):
                programs.append(os.path.join(args.dir, entry))
    if not programs:
        parser.error("no programs given (pass files or --dir)")

    if args.reference is not None and len(programs) != 1:
        parser.error("--reference requires exactly one program")

    total_gaps = 0
    for path in programs:
        total_gaps += compare(path, args.cake, args.flapjack, args.quiet, args.reference)
    if not args.quiet:
        print(f"programs={len(programs)} gaps={total_gaps}")
    return 1 if total_gaps else 0


if __name__ == "__main__":
    sys.exit(main())
