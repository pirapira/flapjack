"""Regression tests for HOL theorem-map coverage and metadata validation."""

import runpy
import json
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
    def test_crep_state_shape_mismatch_is_not_mapped_as_exact(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        invalid_exact = (
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "lookup_locals_eq_map_vars"),
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "dec_clock_simp"),
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "empty_locals_simp"),
            ("Flapjack/Pancake/Semantics/CrepSem.lean", "decCrepClock"),
            ("Flapjack/Pancake/Semantics/CrepSem.lean", "clearCrepRuntimeLocals"),
        )
        for key in invalid_exact:
            with self.subTest(key=key):
                self.assertNotIn(key, inventory)

    def test_compile_prog_withdrawal_and_exact_proof_are_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        self.assertNotIn(
            ("Flapjack/Pancake/PanToCrep/CompileProg.lean", "compileProgTopHOL"),
            inventory,
        )
        expected = {
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "firstCompileProgAllDistinct"):
                "first_compile_prog_all_distinct",
        }
        for key, hol_name in expected.items():
            with self.subTest(key=key):
                self.assertEqual(inventory[key]["hol_name"], hol_name)
                self.assertEqual(inventory[key]["statement_status"], "reviewed_exact")
                self.assertEqual(inventory[key]["reviewer"], "Codex (source comparison)")

    def test_genlist_vmax_distinct_lists_port_is_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        generic_key = (
            "Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean",
            "genlistVmaxDistinctListsCompiledExps",
        )
        generic = inventory[generic_key]
        self.assertIsNone(generic["hol_name"])
        self.assertEqual(
            generic["statement_status"],
            "no_hol_reference_pending_classification",
        )

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        generic_record = manifest_by_key[generic_key]
        self.assertEqual(
            generic_record["hol_name"],
            "genlist_vmax_distinct_lists_compiled_exps",
        )
        self.assertEqual(generic_record["statement_status"], "documented_mismatch")

        exact_key = (
            "Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean",
            "genlistVmaxDistinctListsCompiledExpsW",
        )
        exact = inventory[exact_key]
        self.assertEqual(
            exact["hol_name"],
            "genlist_vmax_distinct_lists_compiled_exps",
        )
        self.assertEqual(exact["statement_status"], "reviewed_exact")
        self.assertTrue(exact["reviewer"])

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

    def test_locals_rel_lookup_ctxt_withdrawal_is_recorded(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "localsRelLookupCtxt")
        self.assertIsNone(inventory[key]["hol_name"])
        self.assertEqual(inventory[key]["statement_status"],
                         "no_hol_reference_pending_classification")
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "locals_rel_lookup_ctxt")
        self.assertEqual(record["statement_status"], "documented_mismatch")

    def test_compile_exp_not_mem_load_glob_withdrawal_is_recorded(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "compileExpNotMemLoadGlob")
        self.assertIsNone(inventory[key]["hol_name"])
        self.assertEqual(inventory[key]["statement_status"],
                         "no_hol_reference_pending_classification")
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "compile_exp_not_mem_load_glob")
        self.assertEqual(record["statement_status"], "documented_mismatch")


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

    def test_reviewed_list_as_array_requires_qualified_tag_and_fields(self):
        fields = ("degrees",)
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                fields,
            )
        }
        record = self.record(
            statement_status="reviewed_list_as_array", list_as_array=["degrees"]
        )
        self.assertEqual(
            MAP["validate_inventory"](
                [record], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

    def test_qualified_tag_rejects_absent_or_misnamed_witness_field(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                ("degrees",),
            )
        }
        exact = self.record(statement_status="reviewed_exact")
        errors = MAP["validate_inventory"](
            [exact], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("use reviewed_list_as_array" in e for e in errors))

        qualified = self.record(
            statement_status="reviewed_list_as_array", list_as_array=["move"]
        )
        errors = MAP["validate_inventory"](
            [qualified], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("fields do not match" in e for e in errors))

    def test_exact_tag_regression_remains_reviewed_exact(self):
        record = self.record(statement_status="reviewed_exact")
        errors = MAP["validate_inventory"](
            [record],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                    (),
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

    def test_documented_mismatch_keeps_source_candidate_untagged(self):
        reference = (
            "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
            "opt_mmap_eval_is_wf_shape_v",
        )
        record = self.record(
            hol_path=reference[0],
            hol_name=reference[1],
            lean_name="evalPanValueExpsWfShapeOfStateRel",
            statement_status="documented_mismatch",
            reviewer="Codex (source comparison)",
        )
        key = (self.path, record["lean_name"])
        self.assertEqual(MAP["validate_inventory"]([record], {key}, {}), [])
        errors = MAP["validate_inventory"]([record], {key}, {key: reference})
        self.assertTrue(any("must not carry an @[hol] tag" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
