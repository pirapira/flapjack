#!/usr/bin/env python3
"""Pin reviewed HOL ports to their elaborated Lean declaration types.

This detects statement drift after human review. It does not prove that a Lean
statement is equivalent to its HOL source, and it does not hash the HOL
declaration or untagged transitive dependencies. Regenerate the lock only after
reviewing the changed statement against HOL, then inspect the lock diff.

For tagged definitions and `opaque` declarations the lock additionally covers
the elaborated Lean body, because such a body can change without changing its
type. Proof terms of tagged theorems are not hashed; they may be refactored
without changing the reviewed statement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
LOCK = ROOT / "docs" / "HOL-TYPE-HASHES.json"
EXPORTER = ROOT / "scripts" / "HolTypeHashes.lean"


def validate_export_record(record: Any, line_number: int) -> dict[str, str]:
    """Reject malformed exporter output. `value_expr` is optional and only
    emitted for definitions and `opaque` declarations."""
    if not isinstance(record, dict):
        raise ValueError(f"Lean export line {line_number} is not an object")
    required = {"lean_name", "hol_path", "hol_name", "type_expr"}
    allowed = required | {"value_expr"}
    if not required.issubset(record) or not set(record) <= allowed:
        raise ValueError(f"Lean export line {line_number} has invalid fields")
    if not all(isinstance(record[key], str) for key in record):
        raise ValueError(f"Lean export line {line_number} has non-string fields")
    return record


def exported_types() -> list[dict[str, str]]:
    result = subprocess.run(
        ["lake", "env", "lean", str(EXPORTER)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(
            f"Lean type export failed (exit {result.returncode}):\n"
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
        raise ValueError("Lean type export returned no declarations")
    return records


def reviewed_payload(item: dict[str, str]) -> str:
    """Serialize the reviewed part of a declaration: type and, when tagged,
    the definition body. A definition whose body appears or disappears (for
    example a change between `def` and `theorem`) changes the hash. Theorem
    records keep their original type-only hash so the lock diff isolates the
    newly covered definition bodies."""
    if "value_expr" in item:
        return f"{item['type_expr']}\x00{item['value_expr']}"
    return item["type_expr"]


def lock_records(
    manifest: list[dict[str, Any]], exports: list[dict[str, str]]
) -> list[dict[str, str]]:
    """Select reviewed declarations by HOL reference and Lean leaf name.

    Both keys are checked because one HOL theorem may have several Lean cases,
    while Lean leaf names may recur in separate namespaces. Ambiguity fails
    rather than choosing an arbitrary type.
    """
    result = []
    for record in manifest:
        if record.get("statement_status") != "reviewed_exact":
            continue
        key = (record["hol_path"], record["hol_name"], record["lean_name"])
        candidates = [
            item for item in exports
            if (item["hol_path"], item["hol_name"], item["lean_name"].rsplit(".", 1)[-1])
            == key
        ]
        if len(candidates) != 1:
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: "
                f"expected one elaborated type for {key}, found {len(candidates)}"
            )
        item = candidates[0]
        result.append(
            {
                "lean_path": record["lean_path"],
                "lean_name": record["lean_name"],
                "lean_full_name": item["lean_name"],
                "hol_path": record["hol_path"],
                "hol_name": record["hol_name"],
                "sha256": hashlib.sha256(
                    reviewed_payload(item).encode("utf-8")
                ).hexdigest(),
            }
        )
    return sorted(result, key=lambda item: (item["lean_path"], item["lean_name"]))


def expected_lock(
    manifest: list[dict[str, Any]], exports: list[dict[str, str]], toolchain: str
) -> dict[str, Any]:
    return {"lean_toolchain": toolchain.strip(), "records": lock_records(manifest, exports)}


def check_lock(committed: dict[str, Any], current: dict[str, Any]) -> None:
    names = [item["lean_full_name"] for item in committed.get("records", [])]
    duplicates = sorted(name for name, count in Counter(names).items() if count > 1)
    if duplicates:
        raise ValueError(
            "reviewed Lean type lock has duplicate declaration(s): "
            + ", ".join(duplicates)
        )
    if committed == current:
        return
    old = {item["lean_full_name"]: item for item in committed.get("records", [])}
    new = {item["lean_full_name"]: item for item in current["records"]}
    changed = sorted(name for name in old.keys() | new.keys() if old.get(name) != new.get(name))
    detail = ", ".join(changed[:12]) + (" ..." if len(changed) > 12 else "")
    if committed.get("lean_toolchain") != current["lean_toolchain"]:
        detail = f"Lean toolchain changed; {detail}"
    if not changed and not detail:
        detail = "record order or lock metadata differs"
    raise ValueError(
        f"reviewed Lean type lock differs for {len(changed)} declaration(s): "
        f"{detail}; review the HOL/Lean statement before --update"
    )


def render_lock(lock: dict[str, Any]) -> str:
    """Keep each reviewed statement on one diff-friendly JSON line."""
    lines = [
        "{",
        f'  "lean_toolchain": {json.dumps(lock["lean_toolchain"])},',
        '  "records": [',
    ]
    for index, record in enumerate(lock["records"]):
        comma = "," if index + 1 < len(lock["records"]) else ""
        lines.append("    " + json.dumps(record, ensure_ascii=False) + comma)
    lines.extend(["  ]", "}"])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update", action="store_true",
        help="rewrite the reviewed-type lock after human statement review",
    )
    args = parser.parse_args()
    try:
        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        current = expected_lock(
            manifest,
            exported_types(),
            (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
        )
        if args.update:
            LOCK.write_text(render_lock(current), encoding="utf-8")
            print(f"wrote {len(current['records'])} reviewed Lean type hashes to {LOCK}")
            return 0
        committed = json.loads(LOCK.read_text(encoding="utf-8"))
        check_lock(committed, current)
        print(f"{len(current['records'])} reviewed elaborated Lean types unchanged")
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"HOL type hash check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
