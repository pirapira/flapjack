#!/usr/bin/env python3
"""Call-site scaling benchmark for the Word back end.

Generates single-function Pancake programs whose size is controlled by one
parameter and times `flapjack-compile` on each.  The call-site shape is the
one that exposed the cubic cost of the association-list heuristic state: the
Word IR nests every call continuation inside the previous call, so a function
with k call sites is a chain of depth k over a counter map with O(k) keys.

The `--check` binary, when given, is run on the same inputs and its output is
compared byte for byte, so a speed-up can be shown not to have moved a single
byte of the emitted image.

Usage:
  scripts/perf-call-scaling.py [--shape calls|vars|assign] [--sizes 50,100,200,400]
                               [--binary .lake/build/bin/flapjack-compile]
                               [--check /path/to/baseline/flapjack-compile]
"""

import argparse
import pathlib
import subprocess
import sys
import tempfile
import time


def program(shape: str, size: int) -> str:
    if shape == "calls":
        body = "\n".join("  t = f(t);" for _ in range(size))
        return (
            "fun 1 f(1 x) {\n  return x + 1;\n}\n\n"
            f"fun 1 main() {{\n  var t = 1;\n{body}\n"
            "  @halt(@base, 0, @base, 0);\n  return 0;\n}\n"
        )
    if shape == "vars":
        decls = "\n".join(f"  var v{i} = {i + 1};" for i in range(size))
        uses = " + ".join(f"v{i}" for i in range(size))
        return (
            f"fun 1 main() {{\n{decls}\n  var t = {uses};\n"
            "  @halt(@base, 0, @base, 0);\n  return t;\n}\n"
        )
    if shape == "assign":
        body = "\n".join(f"  t = t + {i + 1};" for i in range(size))
        return (
            f"fun 1 main() {{\n  var t = 1;\n{body}\n"
            "  @halt(@base, 0, @base, 0);\n  return 0;\n}\n"
        )
    raise SystemExit(f"unknown shape: {shape}")


def run(binary: str, source: pathlib.Path) -> tuple[float, bytes, int]:
    start = time.monotonic()
    completed = subprocess.run(
        [binary, str(source)], capture_output=True, check=False
    )
    return time.monotonic() - start, completed.stdout, completed.returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--shape", default="calls",
                        choices=["calls", "vars", "assign"])
    parser.add_argument("--sizes", default="50,100,200,400")
    parser.add_argument("--binary", default=".lake/build/bin/flapjack-compile")
    parser.add_argument("--check", default=None,
                        help="second binary whose output must match byte for byte")
    arguments = parser.parse_args()

    sizes = [int(size) for size in arguments.sizes.split(",")]
    previous = None
    mismatches = 0
    with tempfile.TemporaryDirectory() as directory:
        for size in sizes:
            source = pathlib.Path(directory) / f"{arguments.shape}_{size}.pnk"
            source.write_text(program(arguments.shape, size))
            elapsed, output, code = run(arguments.binary, source)
            ratio = "" if previous is None else f"  x{elapsed / previous:.2f}"
            note = "" if code == 0 else f"  (exit {code})"
            line = (f"{arguments.shape} size={size:<6} {elapsed:7.2f} s"
                    f"  out={len(output):<8}{ratio}{note}")
            if arguments.check:
                _, reference, referenceCode = run(arguments.check, source)
                if reference == output and referenceCode == code:
                    line += "  identical"
                else:
                    line += "  DIFFERS"
                    mismatches += 1
            print(line, flush=True)
            previous = elapsed
    if mismatches:
        print(f"output mismatches: {mismatches}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
