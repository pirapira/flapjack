"""Regression tests for HOL theorem-map coverage and metadata validation."""

import runpy
import unittest
from pathlib import Path


MAP = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check_hol_theorem_map.py")
)


class ProofDeclarationScanTest(unittest.TestCase):
    def test_comments_and_check_commands_are_not_theorems(self):
        source = """
/-
theorem fakeInBlock : True := by trivial
/- theorem fakeNested : True := by trivial -/
-/
-- theorem fakeLine : True := by trivial
#check notAProofDeclaration
protected theorem actualProof : True := by trivial
"""
        stripped = MAP["strip_comments"](source)
        names = {
            match.group(1)
            for line in stripped.splitlines()
            if (match := MAP["THEOREM_RE"].match(line))
        }
        self.assertEqual(names, {"actualProof"})


class ReviewedSourceComparisonTest(unittest.TestCase):
    def test_exact_pan_to_crep_utility_ports_are_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "mod_eq_of_lt_eq"),
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "option_ne_none_iff_exists"),
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "prod_mk_pair_eq_id"),
        }
        for key in expected:
            with self.subTest(key=key):
                self.assertEqual(inventory[key]["statement_status"], "reviewed_exact")
                self.assertEqual(
                    inventory[key]["reviewer"], "Codex (source comparison)"
                )

    def test_locals_rel_lookup_ctxt_is_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "localsRelLookupCtxt")
        self.assertEqual(inventory[key]["hol_name"], "locals_rel_lookup_ctxt")
        self.assertEqual(inventory[key]["statement_status"], "reviewed_exact")
        self.assertEqual(inventory[key]["reviewer"], "Codex (source comparison)")


class ValidateInventoryTest(unittest.TestCase):
    path = "Flapjack/Pancake/Proofs/Example.lean"

    def record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_theorem",
            "lean_path": self.path,
            "lean_name": "exampleTheorem",
            "statement_status": "pending_statement_review",
            "reviewer": "Codex (reference inventory)",
        }
        record.update(overrides)
        return record

    def test_complete_mapped_entry_passes(self):
        errors = MAP["validate_inventory"](
            [self.record()],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertEqual(errors, [])

    def test_missing_proofs_declaration_fails(self):
        errors = MAP["validate_inventory"](
            [], {(self.path, "exampleTheorem")}, {}
        )
        self.assertTrue(any("Proofs theorem missing" in error for error in errors))

    def test_tag_mismatch_fails(self):
        errors = MAP["validate_inventory"](
            [self.record(hol_name="wrong_name")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("does not match its @[hol] tag" in error for error in errors))

    def test_missing_reviewer_fails(self):
        errors = MAP["validate_inventory"](
            [self.record(reviewer="")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("reviewer metadata is required" in error for error in errors))

    def test_shape_adjusted_status_is_not_a_reviewed_hol_port(self):
        errors = MAP["validate_inventory"](
            [self.record(statement_status="reviewed_adjusted")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("invalid statement_status" in error for error in errors))

    def test_unmapped_helper_is_explicitly_recorded(self):
        record = self.record(
            hol_path=None,
            hol_name=None,
            lean_name="localHelper",
            statement_status="no_hol_reference_pending_classification",
        )
        errors = MAP["validate_inventory"](
            [record], {(self.path, "localHelper")}, {}
        )
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
