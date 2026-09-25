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
    def test_pan_globals_compile_prog_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/PanGlobals.lean", "compileProgCake")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/pan_globalsScript.sml", "compile_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("ProgHOL width", record["reviewer"])
        self.assertIn("No byte-range premise", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_globals_transformation_carrier_mismatches_are_documented(self):
        cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameProg"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameDecls"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_decs_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalResortDecls"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "resort_decls_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalNewMainName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "new_main_name_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalDeclShapes"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "dec_shapes_def",
            ),
        }
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        tagged = MAP["tagged_declarations"]()
        for key, (hol_path, hol_name) in cases.items():
            with self.subTest(lean_name=key[1]):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("flapjack-6nn.3.1", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, tagged)

    def test_pan_globals_exception_carrier_mismatches_are_documented(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "exceptions_append"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "exceptions_append",
                "flapjack-dlc.48",
            ),
            (
                "Flapjack/Pancake/Proofs/PanGlobals.lean",
                "exceptions_FILTER_is_function",
            ): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "exceptions_FILTER_is_function",
                "flapjack-dlc.47",
            ),
        }
        tagged = MAP["tagged_declarations"]()
        for key, (hol_path, hol_name, bead) in cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("Exp α.Const", record["reviewer"])
                self.assertIn(bead, record["reviewer"])
                self.assertNotIn(key, tagged)
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "fpermName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_name_def",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cancel"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cancel",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cong"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cong",
            ),
        }
        for key, (hol_path, hol_name) in exact_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn("polymorphic", record["reviewer"])
                self.assertIn(key, tagged)
        mismatch_cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameFunctionName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_name_def",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_name_cancel"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cancel",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_name_cong"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cong",
            ),
        }
        for key, (hol_path, hol_name) in mismatch_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("specialization", record["reviewer"])
                self.assertNotIn(key, tagged)

    def test_pan_globals_fresh_name_exact_ports_and_production_forms(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "freshNameHOL_not_mem_hol"): (
                "fresh_name_correct",
                ["name", "names"],
            ),
            (
                "Flapjack/Pancake/Proofs/PanGlobals.lean",
                "freshNameHOL_not_mem_of_subset_hol",
            ): (
                "fresh_name_correct'",
                ["name", "names", "names'"],
            ),
        }
        for key, (hol_name, names_fields) in exact_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/proofs/pan_globalsProofScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"], "reviewed_names_as_string"
                )
                self.assertEqual(record["names_as_string"], names_fields)
                self.assertEqual(record["names_as_string_boundary"], ["name"])
                self.assertIn("byte-observable", record["reviewer"])
                for identifier in names_fields:
                    classification = (
                        "byte-observable" if identifier == "name"
                        else "equality/map-key-only"
                    )
                    self.assertIn(
                        f"{identifier}: {classification}", record["reviewer"]
                    )
                self.assertIn(key, tagged)
        mismatch_cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fresh_name_correct"): (
                "fresh_name_correct",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fresh_name_correct'"): (
                "fresh_name_correct'",
            ),
        }
        for key, (hol_name,) in mismatch_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/proofs/pan_globalsProofScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("globalFreshName", record["reviewer"])
                self.assertNotIn(key, tagged)

    def test_crep_sem_state_exact_helpers_are_reviewed_fmap_as_finite_support(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            "decClockCrepSemHOL": "dec_clock_def",
            "fixClockCrepSemHOL": "fix_clock_def",
            "fixClockCrepSemHOL_IMP_LESS_EQ": "fix_clock_IMP_LESS_EQ",
            "memLoadCrepSemHOL": "mem_load_def",
        }
        for lean_name, hol_name in exact_cases.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", lean_name)
            with self.subTest(lean_name=lean_name):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"], "reviewed_fmap_as_finite_support")
                self.assertEqual(
                    record["fmap_as_finite_support"], ["locals", "globals", "code"])
                self.assertIn(key, tagged)

    def test_crep_sem_holstate_update_helpers_are_reviewed_fmap_as_finite_support(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            "setVar": "set_var_def",
            "setGlobals": "set_globals_def",
            "updLocals": "upd_locals_def",
            "emptyLocals": "empty_locals_def",
        }
        for lean_name, hol_name in exact_cases.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", lean_name)
            with self.subTest(lean_name=lean_name):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"], "reviewed_fmap_as_finite_support")
                self.assertEqual(
                    record["fmap_as_finite_support"], ["locals", "globals", "code"])
                self.assertIn(key, tagged)
        # The Nat-fixed state-level resVar stays an untagged documented mismatch.
        res_var_key = (
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", "resVarEq")
        res_var_record = manifest_by_key[res_var_key]
        self.assertEqual(res_var_record["statement_status"], "documented_mismatch")
        self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.2.4", res_var_record["reviewer"])
        self.assertNotIn(res_var_key, tagged)

    def test_crep_assigned_vars_nested_seq_carrier_mismatch_is_documented(self):
        key = (
            "Flapjack/Pancake/Semantics/CrepProps.lean",
            "crepAssignedVars_nestedSeq_assign_zipWithW",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            (
                "cakeml/pancake/semantics/crepPropsScript.sml",
                "nested_seq_assigned_vars_eq",
            ),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("Call/ExtCall names are String", record["reviewer"])
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_res_var_definition_mismatch_is_in_review_inventory(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "resVarW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "res_var_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("infinite support", record["reviewer"])
        self.assertIn(key, MAP["data_declarations"]())
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_struct_convert_value_carrier_mismatch_is_documented(self):
        key = (
            "Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean",
            "panStructConvertValue",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/proofs/pan_structsProofScript.sml", "convert_v_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("word_lab wrapper", record["reviewer"])
        self.assertIn("flapjack-pxn.18.3.5.8.19", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_simp_functions_eq_filter_map_arb_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/PanSimp.lean", "functions_eq_filterMap")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "functions_eq_FILTER"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("ARB", record["reviewer"])
        self.assertIn("flapjack-4ac.4.109", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_props_res_var_flookup_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            "resVarHOLExact_flookup_some_eq_lookup": "flookup_res_var_some_eq_lookup",
            "resVarHOLExact_flookup_of_ne": "flookup_res_var_diff_eq_org",
            "resVarHOLExact_flookup": "FLOOKUP_pan_res_var_thm",
        }
        for lean_name, hol_name in cases.items():
            key = ("Flapjack/Pancake/Semantics/PanProps.lean", lean_name)
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("finite-map", record["reviewer"])
            self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.2.4", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_lang_with_shape_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            "length_withShape_eq_shape": "length_with_shape_eq_shape",
            "all_distinct_withShape": "all_distinct_with_shape",
            "mem_of_withShape_mem": "el_mem_with_shape",
            "mem_withShape_length": "mem_with_shape_length",
            "withShape_getElem_eq_take_drop": "with_shape_el_take_drop_eq",
        }
        for lean_name, hol_name in cases.items():
            key = ("Flapjack/Pancake/PanLang.lean", lean_name)
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("Shape", record["reviewer"])
            self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_props_flatten_and_disjoint_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem"):
                "all_distinct_with_shape_distinct",
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem_lt"):
                "all_distinct_disjoint_with_shape",
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_of_mem_zip_withShape"):
                "all_distinct_mem_zip_disjoint_with_shape",
            ("Flapjack/Pancake/PanLang.lean", "withShape_getElem_getElem"):
                "el_el_with_shape",
            ("Flapjack/PanValueFlatten.lean",
             "shapeSize_comb_eq_flatten_length_of_getElem"):
                "list_rel_length_shape_of_flatten_better",
            ("Flapjack/PanValueFlatten.lean",
             "shapeSize_comb_map_panValueShape_eq_flatten_length"):
                "list_rel_length_shape_of_flatten",
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "listRelFlattenWithShapeLength"):
                "list_rel_flatten_with_shape_length",
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "listRelFlattenWithShapeFlookup"):
                "list_rel_flatten_with_shape_flookup",
        }
        for key, hol_name in cases.items():
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pansem_state_defs_function_backed_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            ("Flapjack/Pancake/Semantics/PanSem/ClockExact.lean",
             "fixClockHOLExact_IMP_LESS_EQ"): "fix_clock_IMP_LESS_EQ",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "kvar_simps"): "kvar_simps",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "is_valid_value_simps"): "is_valid_value_simps",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "is_valid_value_simps2"): "is_valid_value_simps2",
            ("Flapjack/Pancake/Semantics/PanSem/StateDefsExact.lean",
             "kvar_defs"): "kvar_defs",
            ("Flapjack/Pancake/Semantics/PanSem/IsValidValueExact.lean",
             "isValidValueHOLExact"): "is_valid_value_def",
            ("Flapjack/Pancake/Semantics/PanSem/LocalUpdatesExact.lean",
             "updLocalsHOLExact"): "upd_locals_def",
            ("Flapjack/Pancake/Semantics/PanSem/LocalUpdatesExact.lean",
             "resVarHOLExact"): "res_var_def",
            ("Flapjack/Pancake/Semantics/PanSem/DecCallExact.lean",
             "lookupCodeHOLExact"): "lookup_code_def",
        }
        for key, hol_name in cases.items():
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panSemScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.2.5", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_global_rename_function_name_polymorphic_hol_mismatch_is_documented(
        self,
    ):
        key = ("Flapjack/Pancake/PanGlobals.lean", "globalRenameFunctionName")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/pan_globalsScript.sml", "fperm_name_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertNotIn("names_as_string", record)
        self.assertIn("polymorphic", record["reviewer"])
        self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_set_globals_state_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolGlobalsW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "set_globals_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("unrestricted Nat-to-Option locals", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_set_var_state_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolVarW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "set_var_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("infinite", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_clock_and_locals_carrier_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "decCrepHolClockW": "dec_clock_def",
            "emptyCrepHolLocalsW": "empty_locals_def",
            "fixCrepHolClockW": "fix_clock_def",
            "fixCrepHolClock_IMP_LESS_EQW": "fix_clock_IMP_LESS_EQ",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("infinite", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crepprops_simp_and_nested_seq_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "decCrepHolClock_simp": "dec_clock_simp",
            "emptyCrepHolLocals_simp": "empty_locals_simp",
            "crepAssignedFreeVars_nestedSeq_assign_zipWithW": "nested_seq_assigned_free_vars_eq",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepProps.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepPropsScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("withdrawn", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crepprops_globals_and_assigned_var_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "flookup_setCrepHolGlobals_localsW": "FLOOKUP_set_globals",
            "crepAssignedFreeVars_nestedSeq_storeGlobalsW":
                "assigned_free_vars_store_globals_empty",
            "crepAssignedVars_nestedSeq_storeGlobalsW":
                "assigned_vars_store_globals_empty",
            "mem_crepAssignedFreeVars_imp_mem_crepAssignedVarsW":
                "assigned_free_vars_IMP_assigned_vars",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepProps.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepPropsScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("String", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_empty_locals_definition_mismatch_is_in_review_inventory(self):
        key = (
            "Flapjack/Pancake/Semantics/PanSem.lean",
            "panEmptyLocals",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panSemScript.sml", "empty_locals_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("finite-map bridge", record["reviewer"])
        self.assertIn(key, MAP["data_declarations"]())
        self.assertNotIn(key, MAP["tagged_declarations"]())

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

    def test_compile_prog_distinctness_carrier_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        self.assertNotIn(
            ("Flapjack/Pancake/PanToCrep/CompileProg.lean", "compileProgTopHOL"),
            inventory,
        )
        documented_mismatches = (
            "firstCompileProgAllDistinct",
            "firstCompileToCrepAllDistinct",
        )
        for theorem_name in documented_mismatches:
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", theorem_name)
            with self.subTest(key=key):
                self.assertIsNone(inventory[key]["hol_name"])
                self.assertEqual(
                    inventory[key]["statement_status"],
                    "no_hol_reference_pending_classification",
                )

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        for theorem_name in documented_mismatches:
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", theorem_name)
            with self.subTest(review_record=key):
                self.assertEqual(
                    manifest_by_key[key]["statement_status"], "documented_mismatch"
                )
                self.assertIn("carrier", manifest_by_key[key]["reviewer"])

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

    def test_is_wf_shape_drop_carrier_mismatch_stays_untagged(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "isWfShape_drop")
        self.assertEqual(inventory[key]["hol_name"], "is_wf_shape_drop")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "is_wf_shape_drop")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("unrestricted String", record["reviewer"])
        self.assertIn("shapedFields", record["reviewer"])

    def test_old_exp_shapes_map_analogue_stays_untagged(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "structOldExpShapes_eq_map")
        self.assertEqual(inventory[key]["hol_name"], "old_exp_shapes_eq")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "old_exp_shapes_eq")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("byte-observable", record["reviewer"])
        self.assertIn("String", record["reviewer"])

    def test_fperm_decs_decls_carrier_mismatch_stays_untagged(self):
        key = ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_decs_decls")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        self.assertEqual(inventory[key]["hol_name"], "fperm_decs_decls")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")
        self.assertNotIn(key, MAP["tagged_declarations"]())

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "fperm_decs_decls")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        review = MAP["DOCUMENTED_MISMATCHES"][key][2]
        self.assertIn("unused ys binder", review)
        self.assertIn("arbitrary α global values", review)
        self.assertIn("no NameRanged premise", review)
        self.assertIn("arbitrary α global values", record["reviewer"])


    def test_fields_in_order_reorder_analogue_stays_untagged(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "fieldsInOrderReorderNoop")
        self.assertEqual(inventory[key]["hol_name"], "fields_in_order_reorder_noop")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "fields_in_order_reorder_noop")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("byte-observable", record["reviewer"])
        self.assertIn("No NameRanged premise", record["reviewer"])


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
                (),
                (),
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
                (),
                (),
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
                    (),
                    (),
                )
            },
        )
        self.assertEqual(errors, [])

    def test_reviewed_names_as_string_requires_matching_tag_and_source_review(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                (),
                ("key",),
                (),
            )
        }
        reviewed = self.record(
            statement_status="reviewed_names_as_string",
            reviewer="Codex (HOL source review: key: equality/map-key-only)",
            names_as_string=["key"],
        )
        self.assertEqual(
            MAP["validate_inventory"](
                [reviewed], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

        exact = self.record(
            statement_status="reviewed_exact", names_as_string=["key"]
        )
        errors = MAP["validate_inventory"](
            [exact], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("use reviewed_names_as_string" in e for e in errors))

        pending = self.record(
            statement_status="pending_statement_review",
            names_as_string=["key"],
        )
        errors = MAP["validate_inventory"](
            [pending], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("needs a reviewed source classification" in e for e in errors))

        generic_review = {**reviewed, "reviewer": "Codex (reference inventory)"}
        errors = MAP["validate_inventory"](
            [generic_review], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("source-review note" in e for e in errors))

        unclassified = {**reviewed, "reviewer": "Codex (HOL source review: key use reviewed)"}
        errors = MAP["validate_inventory"](
            [unclassified], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("must classify key as equality/map-key-only" in e for e in errors))

        wrong_field = {**reviewed, "names_as_string": ["other"]}
        errors = MAP["validate_inventory"](
            [wrong_field], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("names_as_string fields do not match" in e for e in errors))

    def test_boundary_qualifier_must_be_reviewed_subset_and_match_manifest(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                (),
                ("key", "generated"),
                ("generated",),
            )
        }
        record = self.record(
            statement_status="reviewed_names_as_string",
            reviewer=("Codex (HOL source review: key: equality/map-key-only; "
                      "generated: byte-observable)"),
            names_as_string=["key", "generated"],
            names_as_string_boundary=["key"],
        )
        errors = MAP["validate_inventory"](
            [record], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("names_as_string_boundary fields do not match" in e
                            for e in errors))

        reviewed_boundary = {
            **record,
            "names_as_string_boundary": ["generated"],
            "reviewer": ("Codex (HOL source review: key: equality/map-key-only; "
                         "generated: byte-observable)"),
        }
        self.assertEqual(
            MAP["validate_inventory"](
                [reviewed_boundary], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

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

    def test_res_var_hol_equality_forms_are_documented_mismatch(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        hol_forms = {
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "foldl_res_var_zip_lookup_var_hol"): "FOLDL_res_var_ZIP_lookup_var",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "foldl_res_var_zip_lookup_hol"): "FOLDL_res_var_ZIP_lookup",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_fupdate_submap_hol"): "SUBMAP_IMP_FUPDATE_SUBMAP",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_domsub_submap_hol"): "SUBMAP_IMP_DOMSUB_SUBMAP",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_domsub_fupdate_hol"): "SUBMAP_IMP_DOMSUB_FUPDATE",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_commutes_strong_hol"): "res_var_commutes_strong",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_foldl_commutes_strong_hol"): "res_var_foldl_commutes_strong",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "flookup_res_var_is_mem_zip_eq_hol"): "flookup_res_var_is_mem_zip_eq",
            ("Flapjack/Pancake/Semantics/CrepProps.lean",
             "flookup_res_var_distinct_zip_eq_hol"): "flookup_res_var_distinct_zip_eq",
        }
        for key, hol_name in hol_forms.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(record["hol_name"], hol_name)
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("infinite-support", record["reviewer"])
                self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.3.1",
                              record["reviewer"])
                self.assertNotIn(key, MAP["tagged_declarations"]())

        production = {
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "FOLDL_res_var_ZIP_lookup_var"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "FOLDL_res_var_ZIP_lookup"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_FUPDATE_SUBMAP"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_DOMSUB_SUBMAP"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_DOMSUB_FUPDATE"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_commutes_strong"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_foldl_commutes_strong"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "flookup_res_var_is_mem_zip_eq"),
        }
        for key in production:
            with self.subTest(key=key):
                self.assertEqual(by_key[key]["statement_status"],
                                 "documented_mismatch")
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_globals_lookup_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "globalsLookup")
        self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
        hol_path, hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
        self.assertEqual(
            (hol_path, hol_name),
            (
                "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
                "globals_lookup_def",
            ),
        )
        self.assertIn("flapjack-pxn.18.3.5.8.8", reviewer)

    def test_pan_to_crep_definition_cluster_mismatches_are_documented(self):
        expected = {
            "excpRel": "excp_rel_def",
            "ctxtFc": "ctxt_fc_def",
            "codeRel": "code_rel_def",
            "stateRel": "state_rel_def",
            "localsRel": "locals_rel_def",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", lean_name)
            self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
            hol_path, got_hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
            self.assertEqual(hol_path, "cakeml/pancake/proofs/pan_to_crepProofScript.sml")
            self.assertEqual(got_hol_name, hol_name)
            self.assertIn("flapjack-pxn.18.3.5.8", reviewer)

    def test_pan_value_evaluator_stability_mismatches_are_documented(self):
        expected = {
            "evalPanValueExps_update_local_not_mem": "update_locals_not_vars_eval_mmap",
            "evalPanValueExps_update_locals_not_mem": "opt_mmap_eval_distinct_lists_not_affect",
            "evalPanValueExp_update_locals_not_mem": "eval_distinct_lists_not_affect",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/PanValueEvaluatorStability.lean", lean_name)
            self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
            hol_path, got_hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
            self.assertEqual(hol_path, "cakeml/pancake/proofs/pan_to_crepProofScript.sml")
            self.assertEqual(got_hol_name, hol_name)
            self.assertIn("flapjack-pxn.18.3.5.8", reviewer)


    def test_pansem_word_lab_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/PanSem.lean", "HolWordLab")
        self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
        hol_path, hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
        self.assertEqual(hol_path, "cakeml/pancake/semantics/panSemScript.sml")
        self.assertEqual(hol_name, "word_lab")
        self.assertIn("flapjack-0lj.5", reviewer)
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        record = by_key[key]
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertEqual((record["hol_path"], record["hol_name"]), (hol_path, hol_name))


    def test_panprops_decs_stcnames_only_functions_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "decs_stcnames_only_functions"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "decsStcnamesHOLExact_of_functions"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "decs_stcnames_only_functions2"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_pansem_the_val_word_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/PanSemStateEval.lean", "holValueWord")
        self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
        hol_path, hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
        self.assertEqual(hol_path, "cakeml/pancake/semantics/panSemScript.sml")
        self.assertEqual(hol_name, "theValWord_def")
        self.assertIn("flapjack-0lj.5", reviewer)
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        record = by_key[key]
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertEqual((record["hol_path"], record["hol_name"]), (hol_path, hol_name))


    def test_pansem_set_var_set_global_finite_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            "setVarHOLFinite": "set_var_def",
            "setGlobalHOLFinite": "set_global_def",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean",
                   lean_name)
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual((record["hol_path"], record["hol_name"]),
                                 ("cakeml/pancake/semantics/panSemScript.sml",
                                  hol_name))
                self.assertEqual(
                    record["statement_status"], "reviewed_fmap_as_finite_support")
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_panlang_functions_append_filter_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/PanLang/Decl.lean", "isDeclHOL"): (
                "cakeml/pancake/panLangScript.sml", "is_decl_def"),
            ("Flapjack/Pancake/PanLang/Decl.lean", "isFunctionHOL"): (
                "cakeml/pancake/panLangScript.sml", "is_function_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "functionsHOL_append"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_append"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "functionsHOL_filter_isFunction"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_FILTER"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "functionsHOL_filter_isDecl"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_FILTER'"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

        # The ARB-carrying functions_eq_FILTER is deliberately not tagged.
        eq_filter = ("Flapjack/Pancake/Semantics/PanProps.lean",
                     "functionsHOL_eq_filter")
        self.assertNotIn(eq_filter, MAP["tagged_declarations"]())
        self.assertNotIn(eq_filter, by_key)

    def test_panprops_is_wf_shape_of_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "isWfShapeValueHOLExact_shapeOfHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "is_wf_shape_of_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_pan_primop_is_wf_shape_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "panPrimopHOLExact_isWfShapeValueHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml",
             "pan_primop_is_wf_shape_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_shape_wf_nil_and_drop_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeValueHOLExact_nil_step1"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_nil_step1"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_nil"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeValueHOLExact_drop"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_drop"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_mem_load_is_wf_shape_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "memLoadHOLExact_isWfShapeValueHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml",
             "mem_load_is_wf_shape_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_mem_load_shape_eq_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "memLoadHOLExact_shape_eq"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "mem_loads_some_shape_eq"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "memLoadHOLExact_some_shapeOf_eq"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "mem_load_some_shape_eq"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_every_exp_and_exps_of_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean", "everyExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "every_exp_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "expsOfHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "exps_of_def"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_panprops_localised_and_mmap_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "localised_exp_real_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "namelessExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "nameless_exp_real_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedProgHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "localised_prog_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "optMmapEqSomeHelper"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "opt_mmap_eq_some_helper"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

        # The production String-carrier predicate keeps the withdrawn tag.
        mismatch = ("Flapjack/PanLocalised.lean", "localisedProg")
        record = by_key[mismatch]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "localised_prog_def"))
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("String", record["reviewer"])
        self.assertNotIn(mismatch, MAP["tagged_declarations"]())


if __name__ == "__main__":
    unittest.main()
