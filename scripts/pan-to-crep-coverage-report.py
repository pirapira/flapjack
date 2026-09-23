#!/usr/bin/env python3
"""Validate and render the direct-HOL Pan-to-Crep fixture coverage matrix."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs" / "PAN-TO-CREP-PARITY-COVERAGE.md"

# Each row binds original Pancake's reproducible HOL EVAL artifact to Lean
# checks for the same boundary. Labels are asserted in both the SML probe and
# captured output; Lean markers name the corresponding executable checks.
FIXTURES = [
    {
        "area": "Expression compiler finite maps",
        "boundary": "compile_exp",
        "probe": "compile_exp_probe",
        "hol_labels": ["leaves", "struct_field", "loads_ops", "cmp_shift", "finite_map_shadow"],
        "lean": "Flapjack/Test/CompileExpParity.lean",
        "lean_markers": ["compileExpHOL", "finiteMapLookupOK", "parityGuard"],
        "covers": "original expression cases plus duplicate-key FUPDATE lookup through the finite-map context",
    },
    {
        "area": "Program compiler",
        "boundary": "compile_prog",
        "probe": "compile_prog_probe",
        "hol_labels": ["empty", "inline_call", "global_dest", "handled_missing_dest"],
        "lean": "Flapjack/Test/CompileProgParity.lean",
        "lean_markers": ["compile_prog_inline_call_parity", "shMemStoreAddressTempParity"],
        "covers": "empty input; inline calls; valid Global return destination; handled call with missing destination and a two-word payload",
    },
    {
        "area": "Function and declaration lowering",
        "boundary": "compile_to_crep",
        "probe": "compile_to_crep_probe",
        "hol_labels": ["empty", "raise_const", "raise_pair", "raise_pair_later", "handled_pair"],
        "lean": "Flapjack/Test/CompileToCrepeParity.lean",
        "lean_markers": ["compile_to_crep_raise_const_parity", "pairRaiseOracle", "laterPairOracle", "handledPairOracle", "globalDestinationOracle", "handledMissingDestinationOracle"],
        "covers": "empty input; one-word and two-word exception raises, including a two-word payload lowered after earlier declarations so its later Temp slots stay word-strided; handled two-word exception; flattened parameters",
    },
    {
        "area": "Expression handler setup",
        "boundary": "exp_hdl",
        "probe": "exp_hdl_probe",
        "hol_labels": ["missing", "known", "dup_update", "dup_list"],
        "lean": "Flapjack/Test/ExpHdlParity.lean",
        "lean_markers": ["expHdlFiniteMap", "parityGuard", "dupUpdateOK", "dupListOK", "execDupOK"],
        "covers": "missing and known handler variables; duplicate finite-map updates in both FUPDATE and FUPDATE_LIST form, where the last binding wins; the executed adapter on a duplicate-bearing association-list context",
    },
    {
        "area": "Return handler",
        "boundary": "ret_hdl",
        "probe": "ret_hdl_probe",
        "hol_labels": ["one", "comb_empty", "comb_one", "comb_two", "named"],
        "lean": "Flapjack/Test/RetHdlParity.lean",
        "lean_markers": ["parityGuard"],
        "covers": "One, empty/single/two-word Comb, and Named shapes",
    },
    {
        "area": "Return variable",
        "boundary": "ret_var",
        "probe": "ret_var_probe",
        "hol_labels": ["one_empty", "one_nonempty", "comb_one", "comb_many", "named"],
        "lean": "Flapjack/Test/RetVarParity.lean",
        "lean_markers": ["parityGuard"],
        "covers": "empty and populated One, single and multiword Comb, and Named shapes",
    },
    {
        "area": "Return destination wrapping",
        "boundary": "wrap_rt",
        "probe": "wrap_rt_probe",
        "hol_labels": ["none", "empty_one", "one_word", "comb_empty", "named"],
        "lean": "Flapjack/Test/WrapRtParity.lean",
        "lean_markers": ["parityGuard"],
        "covers": "absent, empty/single One, empty Comb, and Named destinations",
    },
    {
        "area": "Assigned-call edge cases",
        "boundary": "compile",
        "probe": "compile_def_probe",
        "hol_labels": ["missing_global", "empty_one_global", "extra_names_global",
                       "missing_names_global", "missing_local", "empty_one_local",
                       "extra_names_local", "missing_names_local", "valid_local",
                       "empty_struct_return", "finite_map_shadow_return", "pair_load", "pair_store"],
        "lean": "Flapjack/Test/CompileDefParity.lean",
        "lean_markers": ["parityGuard", "missingGlobalCall", "emptyOneGlobalCall",
                         "extraNamesGlobalCall", "missingNamesGlobalCall",
                         "missingLocalCall", "emptyOneLocalCall", "extraNamesLocalCall",
                         "missingNamesLocalCall", "validLocalCall", "nativeProgramParityGuard",
                         "finiteMapLoadStoreParityGuard", "finiteMapParityGuard"],
        "related_lean": "Flapjack/Test/StandaloneCallParity.lean",
        "related_markers": ["assigned call to an unknown local destination", "assigned call to a local whose shape"],
        "covers": "finite-map duplicate updates; empty-shape Return; fixed-stride structured Load/Store; missing/empty/malformed Global and Local destination lists; valid Local pair destination",
    },
]


def require_contains(path: Path, labels: list[str], context: str) -> None:
    content = path.read_text()
    missing = [label for label in labels if label not in content]
    if missing:
        raise ValueError(f"{context}: missing markers in {path.relative_to(ROOT)}: {', '.join(missing)}")


def render() -> str:
    lines = [
        "# Pan-to-Crep parity fixture coverage",
        "",
        "This matrix is generated from the direct CakeML/HOL EVAL probes and the",
        "Lean checks that consume the corresponding intermediate results. The",
        "captured `.out` files are committed, so CI checks do not rebuild HOL.",
        "Run `python3 scripts/pan-to-crep-coverage-report.py --check` to validate",
        "the inventory and this report.",
        "",
        "| Pancake boundary | Direct HOL EVAL artifact | Lean check | Covered cases |",
        "| --- | --- | --- | --- |",
    ]

    for fixture in FIXTURES:
        probe = fixture["probe"]
        script_path = ROOT / "scripts" / "hol-probes" / f"{probe}Script.sml"
        output_path = ROOT / "scripts" / "hol-probes" / f"{probe}.out"
        lean_path = ROOT / fixture["lean"]
        require_contains(script_path, fixture["hol_labels"], f"{fixture['boundary']} probe")
        require_contains(output_path, fixture["hol_labels"], f"{fixture['boundary']} result")
        require_contains(lean_path, fixture["lean_markers"], f"{fixture['boundary']} Lean test")
        if "related_lean" in fixture:
            related_path = ROOT / fixture["related_lean"]
            require_contains(related_path, fixture["related_markers"], f"{fixture['boundary']} related Lean test")

        probe_link = f"[`{probe}.out`](../scripts/hol-probes/{probe}.out)"
        lean_link = f"[`{lean_path.name}`](../{fixture['lean']})"
        lines.append(
            f"| `{fixture['boundary']}` | {probe_link} | {lean_link} | {fixture['covers']} |"
        )

    lines += [
        "",
        "## Scope",
        "",
        "The matrix covers intermediate Pan-to-Crep behavior; it does not claim",
        "complete Pancake language coverage. End-to-end RISC-V exact-output",
        "coverage remains checked separately by `scripts/parity-small-corpus.py`",
        "and the pinned goldens in CI. The multiword raise and handled-call rows",
        "exercise word-indexed global slots with `bytesInWord = 8` in Lean.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail unless the checked-in report is current")
    args = parser.parse_args()

    try:
        report = render()
    except (OSError, ValueError) as error:
        print(f"Pan-to-Crep coverage inventory failed: {error}", file=sys.stderr)
        return 1

    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != report:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; regenerate it with this script", file=sys.stderr)
            return 1
        print(f"Pan-to-Crep coverage report current ({len(FIXTURES)} boundaries)")
    else:
        OUTPUT.write_text(report)
        print(f"wrote {OUTPUT.relative_to(ROOT)} ({len(FIXTURES)} boundaries)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
