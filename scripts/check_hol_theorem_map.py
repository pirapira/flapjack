#!/usr/bin/env python3
"""Check the reviewed inventory for HOL-tagged declarations and Proofs theorems.

The inventory records citation metadata and the current statement-review state.
This gate checks coverage and consistency; it is not a cross-prover equivalence
checker. In particular, ``pending_statement_review`` is an explicit open review
state, not a claim that the Lean statement is equivalent to HOL.
"""

from __future__ import annotations

import argparse
import json
import re
import runpy
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = ROOT / "Flapjack" / "Pancake" / "Proofs"
DEFAULT_MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
REFS = runpy.run_path(str(ROOT / "scripts" / "check-hol-refs.py"))
HOL_ATTRIBUTE_SITES = REFS["hol_attribute_sites"]
FIND_LEAN_DECL = REFS["find_lean_decl"]

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma)\s+([^\s:({\[]+)"
)
DATA_DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|opaque|structure|inductive|class)\s+([^\s:({\[]+)"
)
# HOL definition candidates whose Lean declarations were withdrawn from
# @[hol] because their carrier or statement shape differs. Keep this explicit
# inventory small and source-reviewed; a mismatch row is not generated merely
# because an arbitrary Lean def happens to mention a HOL name.
WITHDRAWN_HOL_DECLARATIONS = {
    ("Flapjack/Pancake/Semantics/PanSem.lean", "panEmptyLocals"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "empty_locals_def",
        "Codex (source comparison with panSemScript.sml:436-438: HOL updates the "
        "finite mlstring-keyed locals map to FEMPTY; panEmptyLocals uses the "
        "production String-keyed unrestricted lookup-function state. "
        "emptyLocalsHOLExact in PanSem/StateExact.lean improves the name and "
        "value carriers but its untouched map fields still admit infinite support. "
        "Direct HOL rows empty_locals/empty_locals_globals/empty_locals_clock are "
        "in pan_empty_locals_probe.out and sampled by PanSemEmptyLocalsHOLParity. "
        "No exact finite-map bridge; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.2."
    ),
}
VALID_STATUSES = {
    "reviewed_exact",
    "reviewed_list_as_array",
    "reviewed_names_as_string",
    "reviewed_list_as_array_names_as_string",
    "pending_statement_review",
    "documented_mismatch",
    "no_hol_reference_pending_classification",
}
FIELDS = {
    "hol_path",
    "hol_name",
    "lean_path",
    "lean_name",
    "statement_status",
    "reviewer",
}


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments, preserving line boundaries."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    line_comment = False
    while index < len(text):
        if line_comment:
            if text[index] == "\n":
                line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                result.extend((" ", " "))
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append(text[index])
            if escaped:
                escaped = False
            elif text[index] == "\\":
                escaped = True
            elif text[index] == '"':
                in_string = False
            index += 1
            continue

        if text.startswith("/-", index):
            block_depth = 1
            result.extend((" ", " "))
            index += 2
        elif text.startswith("--", index):
            line_comment = True
            result.extend((" ", " "))
            index += 2
        else:
            char = text[index]
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


def proof_theorem_declarations(root: Path = ROOT) -> set[tuple[str, str]]:
    """Return file/name pairs for theorem and lemma declarations under Proofs.

    ``#check`` commands and theorem names in comments are deliberately ignored.
    """
    declarations: set[tuple[str, str]] = set()
    proofs = root / "Flapjack" / "Pancake" / "Proofs"
    for path in sorted(proofs.rglob("*.lean")):
        source = strip_comments(path.read_text(encoding="utf-8"))
        rel = path.relative_to(root).as_posix()
        for line in source.splitlines():
            match = THEOREM_RE.match(line)
            if match:
                declarations.add((rel, match.group(1)))
    return declarations


def data_declarations(root: Path = ROOT) -> set[tuple[str, str]]:
    """Return data/definition declaration names outside the Proofs inventory."""
    declarations: set[tuple[str, str]] = set()
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        source = strip_comments(path.read_text(encoding="utf-8"))
        rel = path.relative_to(root).as_posix()
        for line in source.splitlines():
            match = DATA_DECLARATION_RE.match(line)
            if match:
                declarations.add((rel, match.group(1)))
    return declarations


def tagged_declarations(
    root: Path = ROOT,
) -> dict[tuple[str, str], tuple[str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...]]]:
    """Return Lean file/name to HOL file/name for every active ``@[hol]``."""
    tagged: dict[
        tuple[str, str],
        tuple[str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...]],
    ] = {}
    for path in REFS["lean_files"]():
        rel = path.relative_to(root).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        for (line, hol_path, hol_name, _hol_line, list_fields,
             names_fields, boundary_fields) in HOL_ATTRIBUTE_SITES(lines):
            lean_name = FIND_LEAN_DECL(lines, line - 1)
            key = (rel, lean_name)
            # Source-line disambiguation is checked against the HOL script by
            # check-hol-refs.py. The inventory keys the declaration by its
            # stable HOL file/name pair, not by an editable source line.
            value = (hol_path, hol_name, list_fields, names_fields, boundary_fields)
            if key in tagged and tagged[key] != value:
                raise ValueError(f"conflicting @[hol] references for {rel}:{lean_name}")
            tagged[key] = value
    return tagged


def build_inventory(root: Path = ROOT) -> list[dict[str, Any]]:
    """Build a review inventory template without claiming statement review."""
    tagged = tagged_declarations(root)
    inventory: dict[tuple[str, str], dict[str, Any]] = {}
    for (lean_path, lean_name), (
        hol_path, hol_name, list_fields, names_fields, boundary_fields
    ) in tagged.items():
        entry = {
            "hol_path": hol_path,
            "hol_name": hol_name,
            "lean_path": lean_path,
            "lean_name": lean_name,
            "statement_status": "pending_statement_review",
            "reviewer": "Codex (reference inventory)",
        }
        if list_fields:
            entry["list_as_array"] = list(list_fields)
        if names_fields:
            entry["names_as_string"] = list(names_fields)
        if boundary_fields:
            entry["names_as_string_boundary"] = list(boundary_fields)
        inventory[(lean_path, lean_name)] = entry

    for lean_path, lean_name in proof_theorem_declarations(root):
        inventory.setdefault(
            (lean_path, lean_name),
            {
                "hol_path": None,
                "hol_name": None,
                "lean_path": lean_path,
                "lean_name": lean_name,
                "statement_status": "no_hol_reference_pending_classification",
                "reviewer": "Codex (proof inventory)",
            },
        )

    # These source/theorem pairs were checked against their HOL declaration
    # statements in the active review task, not merely copied from attributes.
    reviewed_exact = {
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_less_than"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_not_in"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_all_distinct"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "moreThenNotMaxList"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "max_list_genlist_add_suc_val"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "firstCompileProgAllDistinct"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "map_pick_up_first"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "tuple_4_o"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "ALOOKUP_MAP3"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "ALOOKUP_MAP4"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "mod_eq_of_lt_eq"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "option_ne_none_iff_exists"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "prod_mk_pair_eq_id"),
        ("Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean", "genlistVmaxDistinctListsCompiledExpsW"),
    }
    for key in reviewed_exact:
        # A source comparison cannot claim an exact HOL port after its tag is
        # withdrawn. Keep the untagged proof in the classification queue.
        if key in inventory and inventory[key]["hol_name"] is not None:
            inventory[key]["statement_status"] = "reviewed_exact"
            inventory[key]["reviewer"] = "Codex (source comparison)"

    for key, (hol_path, hol_name, reviewer) in WITHDRAWN_HOL_DECLARATIONS.items():
        inventory[key] = {
            "hol_path": hol_path,
            "hol_name": hol_name,
            "lean_path": key[0],
            "lean_name": key[1],
            "statement_status": "documented_mismatch",
            "reviewer": reviewer,
        }

    return [inventory[key] for key in sorted(inventory)]


def validate_inventory(
    records: list[dict[str, Any]],
    proof_declarations: set[tuple[str, str]],
    tagged: dict[
        tuple[str, str],
        tuple[str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...]],
    ],
    data_declarations_: set[tuple[str, str]] | None = None,
) -> list[str]:
    errors: list[str] = []
    by_key: dict[tuple[str, str], dict[str, Any]] = {}
    for index, record in enumerate(records, start=1):
        missing_fields = FIELDS - record.keys()
        if missing_fields:
            errors.append(f"record {index}: missing fields {sorted(missing_fields)}")
            continue
        key = (record["lean_path"], record["lean_name"])
        if key in by_key:
            errors.append(f"duplicate manifest entry: {key[0]}:{key[1]}")
            continue
        by_key[key] = record
        status = record["statement_status"]
        if status not in VALID_STATUSES:
            errors.append(f"{key[0]}:{key[1]}: invalid statement_status {status!r}")
        reviewer = record["reviewer"]
        if not isinstance(reviewer, str) or not reviewer.strip():
            errors.append(f"{key[0]}:{key[1]}: reviewer metadata is required")

        hol_path, hol_name = record["hol_path"], record["hol_name"]
        tag = tagged.get(key)
        if tag is not None and len(tag) < 5:
            tag = tag + ((),) * (5 - len(tag))
        list_fields = tag[2] if tag is not None else ()
        names_fields = tag[3] if tag is not None else ()
        boundary_fields = tag[4] if tag is not None else ()
        manifest_list_fields = tuple(record.get("list_as_array", ()))
        manifest_names_fields = tuple(record.get("names_as_string", ()))
        manifest_boundary_fields = tuple(record.get("names_as_string_boundary", ()))
        if manifest_list_fields != list_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest list_as_array fields do not match its @[hol] tag"
            )
        if manifest_names_fields != names_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest names_as_string fields do not match its @[hol] tag"
            )
        if manifest_boundary_fields != boundary_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest names_as_string_boundary fields do not match its @[hol] tag"
            )
        if not set(boundary_fields) <= set(names_fields):
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string_boundary must be a subset of names_as_string"
            )
        if list_fields and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: qualified @[hol] tag cannot have reviewed_exact status; "
                "use reviewed_list_as_array after source comparison"
            )
        if not list_fields and status == "reviewed_list_as_array":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_list_as_array needs a qualified @[hol] tag"
            )
        if names_fields and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string @[hol] tag cannot have reviewed_exact status; "
                "use reviewed_names_as_string after source comparison"
            )
        if names_fields and status not in {
            "reviewed_names_as_string",
            "reviewed_list_as_array_names_as_string",
        }:
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string @[hol] tag needs a reviewed "
                "source classification"
            )
        if not names_fields and status == "reviewed_names_as_string":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_names_as_string needs a names_as_string @[hol] tag"
            )
        if list_fields and names_fields:
            if status == "reviewed_list_as_array" or status == "reviewed_names_as_string":
                errors.append(
                    f"{key[0]}:{key[1]}: combined qualifiers require "
                    "reviewed_list_as_array_names_as_string"
                )
        elif status == "reviewed_list_as_array_names_as_string":
            errors.append(
                f"{key[0]}:{key[1]}: combined review status requires both qualifiers"
            )
        if status in {
            "reviewed_names_as_string",
            "reviewed_list_as_array_names_as_string",
        }:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or any(
                field not in reviewer_text for field in names_fields
            ):
                errors.append(
                    f"{key[0]}:{key[1]}: {status} needs a source-review note that "
                    "names every names_as_string field"
                )
            for identifier in names_fields:
                classification = (
                    "byte-observable" if identifier in boundary_fields
                    else "equality/map-key-only"
                )
                if f"{identifier}: {classification}" not in reviewer_text:
                    errors.append(
                        f"{key[0]}:{key[1]}: source-review note must classify "
                        f"{identifier} as {classification}"
                    )
        if (hol_path is None) != (hol_name is None):
            errors.append(f"{key[0]}:{key[1]}: HOL path and name must both be set or null")
        elif status == "documented_mismatch":
            if hol_path is None:
                errors.append(f"{key[0]}:{key[1]}: documented mismatch needs its HOL candidate")
            elif not isinstance(hol_path, str) or not isinstance(hol_name, str):
                errors.append(f"{key[0]}:{key[1]}: HOL path/name must be strings")
            if key in tagged:
                errors.append(f"{key[0]}:{key[1]}: documented mismatch must not carry an @[hol] tag")
            if key not in proof_declarations and key not in WITHDRAWN_HOL_DECLARATIONS:
                errors.append(f"{key[0]}:{key[1]}: untagged HOL mismatch is not source-reviewed")
            if key in WITHDRAWN_HOL_DECLARATIONS and hol_path is not None:
                expected_path, expected_name, _reviewer = WITHDRAWN_HOL_DECLARATIONS[key]
                if (hol_path, hol_name) != (expected_path, expected_name):
                    errors.append(f"{key[0]}:{key[1]}: withdrawn declaration HOL candidate differs from source review")
        elif hol_path is not None:
            if not isinstance(hol_path, str) or not isinstance(hol_name, str):
                errors.append(f"{key[0]}:{key[1]}: HOL path/name must be strings")
            elif tag is None or tag[:2] != (hol_path, hol_name):
                errors.append(
                    f"{key[0]}:{key[1]}: manifest HOL reference does not match its @[hol] tag"
                )
            if status == "no_hol_reference_pending_classification":
                errors.append(f"{key[0]}:{key[1]}: tagged entry cannot have no-HOL status")
        elif status != "no_hol_reference_pending_classification":
            errors.append(f"{key[0]}:{key[1]}: null HOL reference needs no-HOL status")

    for key, reference in tagged.items():
        record = by_key.get(key)
        if record is None:
            errors.append(f"tagged declaration missing from manifest: {key[0]}:{key[1]}")
        elif (record["hol_path"], record["hol_name"]) != reference:
            # The detailed mismatch was already reported above.
            pass

    for key in proof_declarations:
        if key not in by_key:
            errors.append(f"Proofs theorem missing from manifest: {key[0]}:{key[1]}")

    for key in by_key:
        if key not in tagged and key not in proof_declarations and not (
            key in WITHDRAWN_HOL_DECLARATIONS
            and (data_declarations_ is None or key in data_declarations_)
        ):
            errors.append(f"manifest entry is not a current declaration: {key[0]}:{key[1]}")
    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--bootstrap",
        action="store_true",
        help="write an initial inventory template and exit (will not overwrite)",
    )
    args = parser.parse_args(argv)

    if args.bootstrap:
        if args.manifest.exists():
            print(f"error: refusing to overwrite {args.manifest}", file=sys.stderr)
            return 1
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(
            json.dumps(build_inventory(), indent=2) + "\n", encoding="utf-8"
        )
        print(f"wrote {args.manifest.relative_to(ROOT)}")
        return 0

    try:
        records = json.loads(args.manifest.read_text(encoding="utf-8"))
        if not isinstance(records, list):
            raise ValueError("manifest root must be a JSON array")
        errors = validate_inventory(
            records,
            proof_theorem_declarations(),
            tagged_declarations(),
            data_declarations(),
        )
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1
    print(
        f"HOL theorem inventory checked: {len(records)} declarations; "
        f"all {len(proof_theorem_declarations())} Proofs theorems/lemmas are mapped"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
