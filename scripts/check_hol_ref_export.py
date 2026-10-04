#!/usr/bin/env python3
"""Check reviewed theorem-map rows against the elaborated `@[hol]` attributes.

`scripts/HolRefExport.lean` lists every tagged declaration with the qualifiers
recorded by its elaborated `@[hol]` attribute and, unless the declaration itself
carries `(reals_as_rational_cuts)`, whether its constant closure reaches a
declaration that does. For every `reviewed_*` row of `docs/HOL-THEOREM-MAP.json`
this script requires

* exactly one tagged declaration with the row's HOL reference and Lean leaf name,
* the manifest qualifiers to equal the elaborated qualifiers, and
* the manifest `inherits_reals_as_rational_cuts` marker to equal the closure.

This is a consistency gate between the manifest and the Lean attributes. It does
not pin declaration statements or bodies, and it does not prove HOL-to-Lean
equivalence or replace source-level review.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
EXPORTER = ROOT / "scripts" / "HolRefExport.lean"

ALLOWED_QUALIFIERS = {
    "list_as_array", "names_as_string", "names_as_string_boundary",
    "fmap_as_finite_support", "fmap_as_finite_support_result",
    "fmap_as_finite_support_function",
    "fmap_as_finite_support_heterogeneous_function",
    "fmap_as_finite_support_result_observations",
    "fmap_as_finite_support_parameters",
    "fmap_as_finite_support_existentials",
    "fmap_as_finite_support_relation", "fmap_as_finite_support_equalities",
    "fmap_as_finite_support_equality",
    "words_as_type_indexed_bitvec",
    "word_dimension_as_width", "word_dimensions_as_widths",
    "reals_as_rational_cuts",
}
BOOLEAN_QUALIFIERS = {
    "fmap_as_finite_support_result", "fmap_as_finite_support_equalities",
    "fmap_as_finite_support_equality", "words_as_type_indexed_bitvec",
    "reals_as_rational_cuts",
}


def validate_export_record(record: Any, line_number: int) -> dict[str, Any]:
    """Reject malformed exporter output."""
    if not isinstance(record, dict):
        raise ValueError(f"Lean export line {line_number} is not an object")
    required = {"lean_name", "hol_path", "hol_name"}
    allowed = required | {"qualifiers", "inherits_reals_as_rational_cuts"}
    if not required.issubset(record) or not set(record) <= allowed:
        raise ValueError(f"Lean export line {line_number} has invalid fields")
    non_string = [key for key in required if not isinstance(record[key], str)]
    if non_string:
        raise ValueError(f"Lean export line {line_number} has non-string fields {non_string}")
    if not isinstance(record.get("inherits_reals_as_rational_cuts", False), bool):
        raise ValueError(
            f"Lean export line {line_number} has a non-boolean inherits_reals_as_rational_cuts"
        )
    qualifiers = record.get("qualifiers", {})
    if not isinstance(qualifiers, dict) or not set(qualifiers) <= ALLOWED_QUALIFIERS:
        raise ValueError(f"Lean export line {line_number} has invalid qualifiers")
    if any(
        (
            not isinstance(value, bool)
            if key in BOOLEAN_QUALIFIERS
            else not isinstance(value, str)
            if key == "word_dimension_as_width"
            else not isinstance(value, list) or not all(isinstance(field, str) for field in value)
        )
        for key, value in qualifiers.items()
    ):
        raise ValueError(f"Lean export line {line_number} has malformed qualifier fields")
    return record


def exported_refs() -> list[dict[str, Any]]:
    # Use Lake's native `lean` command so the exporter resolves imports from
    # the current workspace build graph. A saved setup file can keep pointing
    # at a shared-cache OLean from an older source revision after `lake build`
    # has rebuilt the local module.
    result = subprocess.run(
        ["lake", "--quiet", "lean", str(EXPORTER)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(
            f"Lean @[hol] export failed (exit {result.returncode}):\n"
            f"{result.stdout}{result.stderr}"
        )
    records = []
    for line_number, line in enumerate(result.stdout.splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"Lean export line {line_number} is not JSON: {line[:160]}") from error
        records.append(validate_export_record(record, line_number))
    if not records:
        raise ValueError("Lean @[hol] export returned no declarations")
    return records


def manifest_qualifiers(record: dict[str, Any]) -> dict[str, Any]:
    """The qualifiers a manifest row records, in the exporter's encoding."""
    qualifiers: dict[str, Any] = {
        "list_as_array": list(record.get("list_as_array", ())),
        "names_as_string": list(record.get("names_as_string", ())),
        "names_as_string_boundary": list(record.get("names_as_string_boundary", ())),
        "fmap_as_finite_support": list(record.get("fmap_as_finite_support", ())),
    }
    for key in (
        "fmap_as_finite_support_relation",
        "fmap_as_finite_support_function",
        "fmap_as_finite_support_heterogeneous_function",
        "fmap_as_finite_support_result_observations",
        "fmap_as_finite_support_parameters",
        "fmap_as_finite_support_existentials",
        "word_dimensions_as_widths",
    ):
        if record.get(key, ()):
            qualifiers[key] = list(record[key])
    for key in BOOLEAN_QUALIFIERS:
        if record.get(key, False):
            qualifiers[key] = True
    if record.get("word_dimension_as_width") is not None:
        qualifiers["word_dimension_as_width"] = record["word_dimension_as_width"]
    return qualifiers


def check_records(
    manifest: list[dict[str, Any]], exports: list[dict[str, Any]]
) -> int:
    """Check every reviewed row against its elaborated declaration.

    Rows are matched by HOL reference and Lean leaf name: one HOL theorem may
    have several Lean cases, while Lean leaf names may recur in separate
    namespaces. Ambiguity fails rather than choosing an arbitrary declaration.
    Returns the number of reviewed rows checked.
    """
    by_key: dict[tuple[str, str, str], list[dict[str, Any]]] = {}
    for item in exports:
        key = (item["hol_path"], item["hol_name"], item["lean_name"].rsplit(".", 1)[-1])
        by_key.setdefault(key, []).append(item)
    checked = 0
    for record in manifest:
        if not str(record.get("statement_status", "")).startswith("reviewed_"):
            continue
        # Source scanners retain Lean's escaped identifier delimiters, while
        # Name.toString exports the underlying leaf (e.g. dfn'FMIN_S).
        leaf = record["lean_name"]
        if leaf.startswith("«") and leaf.endswith("»"):
            leaf = leaf[1:-1]
        key = (record["hol_path"], record["hol_name"], leaf)
        candidates = by_key.get(key, [])
        if len(candidates) != 1:
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: "
                f"expected one tagged declaration for {key}, found {len(candidates)}"
            )
        item = candidates[0]
        qualifiers = manifest_qualifiers(record)
        exported_qualifiers = item.get("qualifiers", {})
        if any(exported_qualifiers.get(name, []) != value
               for name, value in qualifiers.items()):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: manifest qualifiers "
                "differ from elaborated @[hol] exporter"
            )
        if (exported_qualifiers.get("reals_as_rational_cuts", False)
                and not qualifiers.get("reals_as_rational_cuts", False)):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: elaborated @[hol] carries "
                "reals_as_rational_cuts but the manifest record does not"
            )
        exported_inherits = bool(item.get("inherits_reals_as_rational_cuts", False))
        manifest_inherits = bool(record.get("inherits_reals_as_rational_cuts", False))
        if exported_inherits != manifest_inherits:
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: manifest "
                f"inherits_reals_as_rational_cuts={manifest_inherits} but the elaborated "
                f"declaration closure gives {exported_inherits}"
            )
        checked += 1
    return checked


def main() -> int:
    try:
        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        checked = check_records(manifest, exported_refs())
        print(f"{checked} reviewed theorem-map rows match their elaborated @[hol] attributes")
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"HOL reference export check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
