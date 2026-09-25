"""Regression tests for the elaborated-type review lock."""

import hashlib
import importlib.util
import json
import unittest
from pathlib import Path
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "check_hol_type_hashes.py"
SPEC = importlib.util.spec_from_file_location("check_hol_type_hashes", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class HolTypeHashesTest(unittest.TestCase):
    def setUp(self):
        self.manifest = [{
            "lean_path": "Flapjack/Pancake/Proofs/Example.lean",
            "lean_name": "exampleCorrect",
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_correct",
            "statement_status": "reviewed_exact",
        }]
        self.export = [{
            "lean_name": "Flapjack.exampleCorrect",
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_correct",
            "type_expr": "Lean.Expr.const `True []",
        }]

    def test_elaborated_type_change_changes_review_lock(self):
        old = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        changed = [{**self.export[0], "type_expr": "Lean.Expr.const `False []"}]
        new = MODULE.expected_lock(self.manifest, changed, "leanprover/lean4:v4")
        self.assertNotEqual(old, new)
        with self.assertRaisesRegex(ValueError, "reviewed Lean type lock differs"):
            MODULE.check_lock(old, new)
        self.assertEqual(
            old["records"][0]["sha256"],
            hashlib.sha256(MODULE.reviewed_payload(self.export[0]).encode()).hexdigest(),
        )

    def test_reviewer_status_controls_lock_membership(self):
        pending = [{**self.manifest[0], "statement_status": "pending_statement_review"}]
        self.assertEqual(MODULE.lock_records(pending, self.export), [])

    def test_definition_body_change_changes_review_lock(self):
        definition_export = [{
            **self.export[0],
            "value_expr": "Lean.Expr.const `True []",
        }]
        old = MODULE.expected_lock(self.manifest, definition_export, "leanprover/lean4:v4")
        changed = [{**definition_export[0], "value_expr": "Lean.Expr.const `False []"}]
        new = MODULE.expected_lock(self.manifest, changed, "leanprover/lean4:v4")
        self.assertNotEqual(old, new)
        with self.assertRaisesRegex(ValueError, "reviewed Lean type lock differs"):
            MODULE.check_lock(old, new)

    def test_body_presence_changes_review_lock(self):
        with_body = MODULE.expected_lock(
            self.manifest, [{**self.export[0], "value_expr": "Lean.Expr.const `True []"}],
            "leanprover/lean4:v4",
        )
        without_body = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        self.assertNotEqual(with_body, without_body)

    def test_reviewed_names_as_string_qualifiers_are_locked(self):
        manifest = [{
            **self.manifest[0],
            "statement_status": "reviewed_names_as_string",
            "names_as_string": ["key", "generated"],
            "names_as_string_boundary": ["generated"],
        }]
        export = [{
            **self.export[0],
            "qualifiers": {
                "list_as_array": [],
                "names_as_string": ["key", "generated"],
                "names_as_string_boundary": ["generated"],
            },
        }]
        lock = MODULE.expected_lock(manifest, export, "leanprover/lean4:v4")
        self.assertEqual(lock["records"][0]["qualifiers"], {
            "list_as_array": [],
            "names_as_string": ["key", "generated"],
            "names_as_string_boundary": ["generated"],
            "fmap_as_finite_support": [],
        })
        changed = [{
            **export[0],
            "qualifiers": {
                **export[0]["qualifiers"],
                "names_as_string_boundary": [],
            },
        }]
        with self.assertRaisesRegex(ValueError, "manifest qualifiers differ"):
            MODULE.lock_records(manifest, changed)

    def test_qualifier_changes_reviewed_hash(self):
        plain = {**self.export[0], "qualifiers": {}}
        qualified = {**self.export[0], "qualifiers": {"names_as_string": ["key"]}}
        self.assertNotEqual(
            MODULE.reviewed_payload(plain), MODULE.reviewed_payload(qualified)
        )

    def test_reviewed_payload_covers_only_type_and_body(self):
        item = {**self.export[0], "value_expr": "Lean.Expr.const `True []"}
        self.assertEqual(
            MODULE.reviewed_payload(item),
            "Lean.Expr.const `True []\x00Lean.Expr.const `True []",
        )
        self.assertEqual(
            MODULE.reviewed_payload(self.export[0]),
            "Lean.Expr.const `True []",
        )

    def test_theorem_type_only_hash_is_stable(self):
        # A declaration without a body must hash exactly its type, so the
        # original theorem hashes are unchanged by the body-hash extension.
        lock = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        self.assertEqual(
            lock["records"][0]["sha256"],
            hashlib.sha256(self.export[0]["type_expr"].encode()).hexdigest(),
        )

    def test_reviewed_fmap_as_finite_support_qualifiers_are_locked(self):
        manifest = [{
            **self.manifest[0],
            "statement_status": "reviewed_fmap_as_finite_support",
            "fmap_as_finite_support": ["locals", "globals"],
        }]
        export = [{
            **self.export[0],
            "qualifiers": {
                "list_as_array": [],
                "names_as_string": [],
                "names_as_string_boundary": [],
                "fmap_as_finite_support": ["locals", "globals"],
            },
        }]
        lock = MODULE.expected_lock(manifest, export, "leanprover/lean4:v4")
        self.assertEqual(lock["records"][0]["qualifiers"]["fmap_as_finite_support"],
                         ["locals", "globals"])
        changed = [{
            **export[0],
            "qualifiers": {
                **export[0]["qualifiers"],
                "fmap_as_finite_support": ["locals"],
            },
        }]
        with self.assertRaisesRegex(ValueError, "manifest qualifiers differ"):
            MODULE.lock_records(manifest, changed)

    def test_fmap_qualifier_validates_and_rejects_unknown(self):
        MODULE.validate_export_record(
            {
                "lean_name": "n", "hol_path": "p", "hol_name": "h",
                "type_expr": "t",
                "qualifiers": {"fmap_as_finite_support": ["locals"]},
            },
            1,
        )
        with self.assertRaisesRegex(ValueError, "invalid qualifiers"):
            MODULE.validate_export_record(
                {
                    "lean_name": "n", "hol_path": "p", "hol_name": "h",
                    "type_expr": "t",
                    "qualifiers": {"finite_map": ["locals"]},
                },
                1,
            )

    def test_unknown_export_field_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "invalid fields"):
            MODULE.validate_export_record(
                {"lean_name": "n", "hol_path": "p", "hol_name": "h",
                 "type_expr": "t", "extra": "x"},
                1,
            )

    def test_missing_required_field_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "invalid fields"):
            MODULE.validate_export_record(
                {"lean_name": "n", "hol_path": "p", "type_expr": "t"}, 1
            )

    def test_valid_export_record_with_body(self):
        record = {"lean_name": "n", "hol_path": "p", "hol_name": "h",
                  "type_expr": "t", "value_expr": "v"}
        self.assertEqual(MODULE.validate_export_record(record, 1), record)

    def test_valid_export_record_with_qualifiers(self):
        record = {
            "lean_name": "n", "hol_path": "p", "hol_name": "h", "type_expr": "t",
            "qualifiers": {
                "list_as_array": [], "names_as_string": ["key"],
                "names_as_string_boundary": [],
            },
        }
        self.assertEqual(MODULE.validate_export_record(record, 1), record)

    def test_malformed_export_qualifier_fails_closed(self):
        record = {
            "lean_name": "n", "hol_path": "p", "hol_name": "h", "type_expr": "t",
            "qualifiers": {"names_as_string": "key"},
        }
        with self.assertRaisesRegex(ValueError, "malformed qualifier"):
            MODULE.validate_export_record(record, 1)

    def test_ambiguous_reference_fails_closed(self):
        duplicate = [{**self.export[0], "lean_name": "Other.exampleCorrect"}]
        with self.assertRaisesRegex(ValueError, "found 2"):
            MODULE.lock_records(self.manifest, self.export + duplicate)

    def test_missing_export_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "found 0"):
            MODULE.lock_records(self.manifest, [])

    def test_duplicate_committed_record_reports_declaration(self):
        current = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        committed = {**current, "records": current["records"] * 2}
        with self.assertRaisesRegex(ValueError, "duplicate declaration.*Flapjack.exampleCorrect"):
            MODULE.check_lock(committed, current)

    def test_compact_lock_is_valid_json(self):
        lock = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        self.assertEqual(json.loads(MODULE.render_lock(lock)), lock)
        self.assertEqual(len(MODULE.render_lock(lock).splitlines()), 6)

    def test_exporter_uses_current_lake_build_graph(self):
        result = type("Completed", (), {
            "returncode": 0,
            "stdout": json.dumps(self.export[0]) + "\n",
            "stderr": "",
        })()
        with patch.object(MODULE.subprocess, "run", return_value=result) as run:
            self.assertEqual(MODULE.exported_types(), self.export)
        self.assertEqual(run.call_args.args[0], [
            "lake", "--quiet", "lean", str(MODULE.EXPORTER),
        ])

    def test_native_export_sees_recent_crep_props_source_declaration(self):
        # This exact declaration was missing from an old saved
        # Flapjack.setup.json after Lake had rebuilt CrepProps from source.
        # Exercise the real Lake path to ensure the fresh declaration is
        # visible and that no local OLean import is missing.
        names = {item["lean_name"] for item in MODULE.exported_types()}
        self.assertIn(
            "Flapjack.crepAssignedVarsHOL_nestedSeq_storesHOL", names
        )


if __name__ == "__main__":
    unittest.main()
