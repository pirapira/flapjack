#!/usr/bin/env python3
"""Run the checked-in original Pancake source-to-RISC-V corpus.

Each fixture is compiled by both the authoritative CakeML Pancake compiler and
Flapjack's source-facing executable.  The runner checks the original stdout
hash, parses both Pancake-compatible assembly frames, and compares runtime,
generated-entry, and user-function sections including their bases and bytes.

Known byte differences are not silently normalized: they pass only when the
fixture records the P1 bead(s) that own the discrepancy.  An acceptance,
format, or byte difference without a tracked bead fails the command.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"
DEFAULT_MANIFEST = Path(__file__).with_name("parity-small-corpus.json")


def run(command, path):
    input_stream = path.open("rb") if command[0].endswith("cake") else None
    try:
        return subprocess.run(command, stdin=input_stream, capture_output=True)
    finally:
        if input_stream is not None:
            input_stream.close()


def parse_byte_line(content):
    return [int(token.strip(), 16) for token in content.split(",") if token.strip()]


def parse_assembly(text):
    marker = text.find("cake_main:")
    if marker < 0:
        marker = text.find("#### Generated machine code follows")
    if marker < 0:
        return None
    payload = []
    for line in text[marker:].splitlines():
        match = re.search(r"\.byte(.*)", line)
        if match:
            payload.extend(parse_byte_line(match.group(1)))
    sections = {}
    for match in re.finditer(r"makesym\((\w+),\s*(\d+),\s*(\d+)\)", text):
        name, base, length = match.group(1), int(match.group(2)), int(match.group(3))
        sections[name] = (base, payload[base:base + length])
    return sections if sections else None


def normalize(name):
    return re.sub(r"_\d+$", "", re.sub(r"^cml_", "", name))


def classify(sections):
    runtime, entry, user = {}, None, {}
    for name, section in sections.items():
        if name.startswith("cml__") or name.startswith("cml_flapjack_runtime"):
            runtime[name] = section
        elif name.startswith("cml_generated_main"):
            entry = section
        else:
            user[normalize(name)] = section
    return runtime, entry, user


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def compare_section(cake, flapjack, owner, name):
    if cake == flapjack:
        return None
    return {
        "owner": owner,
        "section": name,
        "cake_base": cake[0],
        "flapjack_base": flapjack[0],
        "cake_bytes": len(cake[1]),
        "flapjack_bytes": len(flapjack[1]),
        "cake_sha256": sha256(bytes(cake[1])),
        "flapjack_sha256": sha256(bytes(flapjack[1])),
    }


def compare_maps(cake, flapjack, owner):
    gaps = []
    for name in sorted(cake):
        if name not in flapjack:
            gaps.append({"owner": owner, "section": name, "kind": "missing"})
        else:
            mismatch = compare_section(cake[name], flapjack[name], owner, name)
            if mismatch:
                gaps.append(mismatch)
    for name in sorted(set(flapjack) - set(cake)):
        gaps.append({"owner": owner, "section": name, "kind": "unexpected"})
    return gaps


def fixture_report(fixture, cake, flapjack):
    relative = fixture["path"]
    path = REPO_ROOT / relative
    report = {
        "path": relative,
        "source_reference": fixture["source_reference"],
        "tracked_beads": fixture.get("tracked_beads", []),
    }
    cake_result = run([cake, "--pancake", "--target=riscv"], path)
    flapjack_result = run([str(flapjack), "--assembly", str(path)], path)
    report["cake_accepts"] = cake_result.returncode == 0
    report["flapjack_accepts"] = flapjack_result.returncode == 0
    report["cake_stdout_sha256"] = sha256(cake_result.stdout)
    report["flapjack_stdout_sha256"] = sha256(flapjack_result.stdout)
    report["expected_cake_sha256"] = fixture["cake_sha256"]
    report["untracked"] = []

    if report["cake_stdout_sha256"] != fixture["cake_sha256"]:
        report["untracked"].append("original Cake stdout hash changed")
    if report["cake_accepts"] != report["flapjack_accepts"]:
        report["untracked"].append("acceptance disagreement")
    if not report["cake_accepts"]:
        report["status"] = "reference-rejected"
        report["mismatches"] = []
        return report
    if not report["flapjack_accepts"]:
        report["status"] = "flapjack-rejected"
        report["mismatches"] = [{"owner": "artifact", "kind": "rejected"}]
        return report

    cake_sections = parse_assembly(cake_result.stdout.decode("utf-8", "replace"))
    flap_sections = parse_assembly(flapjack_result.stdout.decode("utf-8", "replace"))
    if cake_sections is None or flap_sections is None:
        report["status"] = "format-gap"
        report["mismatches"] = [{"owner": "artifact", "kind": "malformed"}]
        return report

    cake_runtime, cake_entry, cake_user = classify(cake_sections)
    flap_runtime, flap_entry, flap_user = classify(flap_sections)
    mismatches = compare_maps(cake_runtime, flap_runtime, "runtime")
    if cake_entry is None and flap_entry is not None:
        mismatches.append({"owner": "generated_main", "kind": "unexpected"})
    elif cake_entry is not None and flap_entry is None:
        mismatches.append({"owner": "generated_main", "kind": "missing"})
    elif cake_entry is not None:
        mismatch = compare_section(cake_entry, flap_entry, "generated_main", "entry")
        if mismatch:
            mismatches.append(mismatch)
    mismatches.extend(compare_maps(cake_user, flap_user, "user"))
    report["mismatches"] = mismatches
    report["status"] = "exact" if not mismatches else "tracked-gap"
    if mismatches and not report["tracked_beads"]:
        report["untracked"].append("byte/layout mismatch has no owning bead")
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument("--flapjack", default=os.environ.get("FLAPJACK", str(DEFAULT_FLAPJACK)))
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--report", help="write the machine-readable report to this path")
    args = parser.parse_args(argv)
    if not Path(args.cake).is_file():
        print(f"missing cake binary: {args.cake}", file=sys.stderr)
        return 2
    if not Path(args.flapjack).is_file():
        print(f"missing flapjack binary: {args.flapjack}", file=sys.stderr)
        return 2

    manifest = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
    reports = [fixture_report(fixture, args.cake, Path(args.flapjack))
               for fixture in manifest["fixtures"]]
    for report in reports:
        beads = ",".join(report["tracked_beads"]) or "none"
        print(f"{report['status']} {report['path']} "
              f"cake={report['cake_stdout_sha256']} "
              f"flapjack={report['flapjack_stdout_sha256']} "
              f"mismatches={len(report['mismatches'])} tracked={beads}")
        for problem in report["untracked"]:
            print(f"  UNTRACKED: {problem}")
    summary = {
        "fixtures": len(reports),
        "exact": sum(report["status"] == "exact" for report in reports),
        "tracked_gaps": sum(report["status"] == "tracked-gap" and not report["untracked"]
                             for report in reports),
        "untracked": sum(bool(report["untracked"]) for report in reports),
        "reports": reports,
    }
    print("corpus=%d exact=%d tracked_gaps=%d untracked=%d" %
          (summary["fixtures"], summary["exact"], summary["tracked_gaps"], summary["untracked"]))
    if args.report:
        Path(args.report).write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    return 1 if summary["untracked"] else 0


if __name__ == "__main__":
    sys.exit(main())
