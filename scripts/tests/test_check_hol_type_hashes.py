"""Regression tests for the elaborated-type review lock."""

import hashlib
import importlib.util
import json
import unittest
from pathlib import Path


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
            hashlib.sha256(self.export[0]["type_expr"].encode()).hexdigest(),
        )

    def test_reviewer_status_controls_lock_membership(self):
        pending = [{**self.manifest[0], "statement_status": "pending_statement_review"}]
        self.assertEqual(MODULE.lock_records(pending, self.export), [])

    def test_ambiguous_reference_fails_closed(self):
        duplicate = [{**self.export[0], "lean_name": "Other.exampleCorrect"}]
        with self.assertRaisesRegex(ValueError, "found 2"):
            MODULE.lock_records(self.manifest, self.export + duplicate)

    def test_missing_export_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "found 0"):
            MODULE.lock_records(self.manifest, [])

    def test_compact_lock_is_valid_json(self):
        lock = MODULE.expected_lock(self.manifest, self.export, "leanprover/lean4:v4")
        self.assertEqual(json.loads(MODULE.render_lock(lock)), lock)
        self.assertEqual(len(MODULE.render_lock(lock).splitlines()), 6)


if __name__ == "__main__":
    unittest.main()
