#!/usr/bin/env python3
"""Capture reproducible intermediate evidence for one Pancake parity gap.

The final artifact comparison is shared with ``parity-difffuzz.py``.  When
HOL4 and CakeML are available, the script also evaluates the original
``pan_simp -> pan_structs -> pan_globals -> pan_to_crep -> crep_to_loop ->
loop_to_word`` stages.  Flapjack's matching pipeline is dumped by the
``flapjack-debug`` executable.  ``--minimize`` performs signature-preserving
line delta debugging, so a smaller source is only accepted when it keeps the
same observed disagreement.

Example:

    python3 scripts/parity-debug.py Flapjack/Test/OriginalPancake/shadowing.pnk \
        --out /tmp/shadowing-debug --minimize
"""

import argparse
import difflib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DIFFUZZ = ROOT / "scripts" / "parity-difffuzz.py"
HOL_PROBE = ROOT / "scripts" / "hol-probes" / "pancake-stage-probeScript.sml"
DEFAULT_CAKE = Path(os.environ.get("CAKE", str(ROOT / "cakeml/developers/bin/cake")))
DEFAULT_FLAPJACK = Path(os.environ.get(
    "FLAPJACK", str(ROOT / ".lake/build/bin/flapjack-compile")))
DEFAULT_DEBUG = Path(os.environ.get(
    "FLAPJACK_DEBUG", str(ROOT / ".lake/build/bin/flapjack-debug")))
DEFAULT_HOL = Path(os.environ.get("HOL", "/home/zksecurity/HOL/bin/hol"))


def load_diffuzz():
    spec = importlib.util.spec_from_file_location("flapjack_parity_diffuzz", DIFFUZZ)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(command, *, input_bytes=None, env=None, cwd=None, timeout=60):
    try:
        result = subprocess.run(command, input=input_bytes, capture_output=True,
                                env=env, cwd=cwd, timeout=timeout)
        return {"command": [str(x) for x in command],
                "returncode": result.returncode,
                "stdout": result.stdout, "stderr": result.stderr}
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"command": [str(x) for x in command], "returncode": 124,
                "stdout": b"", "stderr": str(error).encode()}


def write_bytes(path, data):
    path.write_bytes(data)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path, required=True,
                        help="directory receiving the complete evidence bundle")
    parser.add_argument("--cake", type=Path, default=DEFAULT_CAKE)
    parser.add_argument("--flapjack", type=Path, default=DEFAULT_FLAPJACK)
    parser.add_argument("--flapjack-debug", type=Path, default=DEFAULT_DEBUG)
    parser.add_argument("--hol", type=Path, default=DEFAULT_HOL)
    parser.add_argument("--nice", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--minimize", action="store_true",
                        help="also write case.min.pnk preserving mismatch signatures")
    parser.add_argument("--no-stages", action="store_true",
                        help="skip the HOL and Lean intermediate-stage commands")
    args = parser.parse_args(argv)

    source = args.source.resolve()
    if not source.is_file():
        parser.error("source file not found: %s" % source)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source_bytes = source.read_bytes()
    write_bytes(out / "case.pnk", source_bytes)

    diffuzz = load_diffuzz()
    runner = diffuzz.Runner(args.cake, args.flapjack, args.nice, args.timeout)
    result = runner.run(source, source_bytes)
    comparison = diffuzz.compare_case(result)
    record = {"source": str(source), "comparison": comparison,
              "commands": {key: value["command"] for key, value in result.items()},
              "returncodes": {key: value["returncode"] for key, value in result.items()}}
    write_bytes(out / "cake.S", result["cake"]["stdout"])
    write_bytes(out / "cake.err", result["cake"]["stderr"])
    write_bytes(out / "flapjack.S", result["flapjack"]["stdout"])
    write_bytes(out / "flapjack.err", result["flapjack"]["stderr"])
    (out / "comparison.json").write_text(json.dumps(record, indent=2) + "\n")
    cake_lines = result["cake"]["stdout"].decode("utf-8", "replace").splitlines(True)
    flap_lines = result["flapjack"]["stdout"].decode("utf-8", "replace").splitlines(True)
    (out / "final.diff").write_text("".join(difflib.unified_diff(
        cake_lines, flap_lines, fromfile="cake.S", tofile="flapjack.S")))

    if args.minimize:
        workdir = out / ".minimize-work"
        workdir.mkdir(exist_ok=True)
        minimized, steps = diffuzz.minimize_source(
            runner, source_bytes, comparison, workdir)
        write_bytes(out / "case.min.pnk", minimized)
        record["minimized"] = {"steps": steps, "bytes": len(minimized)}
        (out / "comparison.json").write_text(json.dumps(record, indent=2) + "\n")

    if not args.no_stages:
        debug = run([args.flapjack_debug, str(source)], timeout=args.timeout)
        write_bytes(out / "flapjack-stages.txt", debug["stdout"])
        write_bytes(out / "flapjack-stages.err", debug["stderr"])
        hol_env = os.environ.copy()
        hol_env["PANCAKE_SOURCE"] = str(source)
        hol = run([args.hol, "run", str(HOL_PROBE)], env=hol_env,
                  cwd=ROOT / "cakeml" / "pancake",
                  timeout=args.timeout)
        write_bytes(out / "cake-stages.txt", hol["stdout"])
        write_bytes(out / "cake-stages.err", hol["stderr"])
        record["stage_commands"] = {"flapjack": debug["command"], "cake": hol["command"]}
        record["stage_returncodes"] = {"flapjack": debug["returncode"], "cake": hol["returncode"]}
        cake_stage_lines = hol["stdout"].decode("utf-8", "replace").splitlines(True)
        flap_stage_lines = debug["stdout"].decode("utf-8", "replace").splitlines(True)
        (out / "stages.diff").write_text("".join(difflib.unified_diff(
            cake_stage_lines, flap_stage_lines,
            fromfile="cake-stages.txt", tofile="flapjack-stages.txt")))
        (out / "comparison.json").write_text(json.dumps(record, indent=2) + "\n")

    print("out=%s class=%s signatures=%s" % (
        out, comparison["class"], ",".join(diffuzz.signatures_of(comparison)) or "none"))
    return 1 if comparison["mismatches"] else 0


if __name__ == "__main__":
    sys.exit(main())
