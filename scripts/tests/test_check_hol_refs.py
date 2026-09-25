"""Regression checks for the HOL-reference scanner."""

import os
import runpy
import tempfile
import unittest
from pathlib import Path


CHECKER = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check-hol-refs.py")
)
SITES = CHECKER["hol_attribute_sites"]
REF_ERROR = CHECKER["hol_ref_error"]


class HolAttributeSitesTest(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]'])),
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), ())],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf", None, (), (), (), ())],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), ())],
        )

    def test_source_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"',
                        '  "locals_rel_wf_shape" 2345]'])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "locals_rel_wf_shape", 2345, (), (), (), ())],
        )

    def test_list_as_array_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml"',
                '  "dec_deg_def" (list_as_array := [degrees, moves])]'
            ])),
            [(1, "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml",
              "dec_deg_def", None, ("degrees", "moves"), (), (), ())],
        )

    def test_names_as_string_and_boundary_qualifiers(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/panLangScript.sml" "varname"',
                '  (names_as_string := [name, generated])',
                '  (names_as_string_boundary := [generated])]',
            ])),
            [(1, "cakeml/pancake/panLangScript.sml", "varname", None,
              (), ("name", "generated"), ("generated",), ())],
        )

    def test_fmap_as_finite_support_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"',
                '  (fmap_as_finite_support := [locals, globals])]'
            ])),
            [(1, "cakeml/pancake/semantics/panSemScript.sml",
              "set_var_def", None, (), (), (), ("locals", "globals"))],
        )

    def test_fmap_as_finite_support_accepts_canonical_carrier(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    HolFiniteMapExact MlS (ValueHOL width) -> State width -> State width :=",
            "  fun m s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"), "Example.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_witness_is_carrier_agnostic(self):
        lines = [
            "structure CrepStateExact where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    HolFiniteMapExact MlS (ValueHOL width) -> CrepStateExact width ->",
            "      CrepStateExact width := fun m s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Pancake/Semantics/CrepSem/StateExact.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_rejects_raw_option_map(self):
        lines = [
            "structure State where",
            "  locals : String → Option Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    HolFiniteMapExact MlS (ValueHOL width) -> State width -> State width :=",
            "  fun m s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(
            any("approved HolFiniteMapExact carrier" in error for error in errors)
        )

    def test_fmap_as_finite_support_requires_canonical_witness(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_witness_must_mention_owner(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    HolFiniteMapExact MlS (ValueHOL width) -> Unit := fun m => ()",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_representation_witness_is_checked_in_same_module(self):
        lines = [
            "structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees (state : State) (xs : List Nat)",
            "    (h : state.degrees = CakeNodeMap.ofList xs) :",
            "    RepresentsHOLNodeList state.degrees xs := by",
            "  rw [h]",
            "  exact CakeNodeMap.ofList_representsHOLNodeList xs",
        ]
        self.assertIn("degrees", CHECKER["structure_fields"](lines))
        self.assertTrue(CHECKER["has_list_array_witness"](lines, "degrees"))
        self.assertFalse(CHECKER["has_list_array_witness"](lines, "moves"))
        self.assertEqual(
            CHECKER["list_as_array_errors"](lines, ("degrees",), "Example.lean"),
            [],
        )
        errors = CHECKER["list_as_array_errors"](
            lines, ("moves",), "Example.lean"
        )
        self.assertTrue(any("not a field" in error for error in errors))
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

    def test_circular_representation_assumption_is_not_a_witness(self):
        lines = [
            "structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees (state : State) (xs : List Nat)",
            "    (h : RepresentsHOLNodeList state.degrees xs) :",
            "    RepresentsHOLNodeList state.degrees xs := h",
        ]
        self.assertFalse(
            CHECKER["has_list_array_witness"](lines, "degrees")
        )

    def test_comments_cannot_supply_qualified_field_or_witness(self):
        lines = [
            "/- structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees : RepresentsHOLNodeList s.degrees xs := by",
            "  exact h -/",
        ]
        errors = CHECKER["list_as_array_errors"](
            lines, ("degrees",), "Example.lean"
        )
        self.assertTrue(any("not a field" in error for error in errors))
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

    def test_equality_only_mlstring_identifier_needs_no_byte_witness(self):
        lines = ["def lookupByName (name : String) := name"]
        self.assertEqual(
            CHECKER["names_as_string_errors"](
                lines, ("name",), (), "Example.lean", "lookupByName"
            ),
            [],
        )

    def test_parameter_boundary_accepts_premise_aware_declaration_witness(self):
        lines = [
            "def freshNameHOL (name : String) (names : List String) := name",
            "theorem holMlStringWitness_freshNameHOL (name : String)",
            "    (names : List String) (hname : NameRanged name) :",
            "    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) := by",
            "  exact freshNameHOL_nameRanged name names hname",
        ]
        self.assertTrue(CHECKER["has_mlstring_witness"](lines, "freshNameHOL"))
        self.assertEqual(
            CHECKER["names_as_string_errors"](
                lines, ("name",), ("name",), "PanGlobals.lean", "freshNameHOL"
            ),
            [],
        )

    def test_boundary_requires_same_module_witness_for_tagged_declaration(self):
        missing = ["def freshNameHOL (name : String) := name"]
        errors = CHECKER["names_as_string_errors"](
            missing, ("name",), ("name",), "PanGlobals.lean", "freshNameHOL"
        )
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

        wrong_name = [
            "theorem holMlStringWitness_other (name : String) :",
            "    NameRanged name := by",
            "  exact h",
        ]
        self.assertFalse(CHECKER["has_mlstring_witness"](wrong_name, "freshNameHOL"))

    def test_boundary_classifier_must_be_qualified(self):
        lines = [
            "theorem holMlStringWitness_freshNameHOL (name : String)",
            "    (h : NameRanged name) : NameRanged (freshNameHOL name) := by",
            "  exact h",
        ]
        errors = CHECKER["names_as_string_errors"](
            lines, ("name",), ("generated",), "PanGlobals.lean", "freshNameHOL"
        )
        self.assertTrue(any("not listed by names_as_string" in error for error in errors))

    def test_boundary_witness_must_conclude_name_ranged(self):
        lines = [
            "theorem holMlStringWitness_freshNameHOL (name : String) :",
            "    name = name := by rfl",
        ]
        self.assertFalse(CHECKER["has_mlstring_witness"](lines, "freshNameHOL"))

    def test_duplicate_name_requires_correct_line(self):
        path = Path(__file__).resolve().parents[2] / \
            "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
        cache = {}
        self.assertIn("multiple lines", REF_ERROR(path, "locals_rel_wf_shape", None, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 2345, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 3008, cache))
        self.assertIn("not at line", REF_ERROR(path, "locals_rel_wf_shape", 2346, cache))


DECL = CHECKER["hol_declaration_lines"]


class HolDatatypeDeclarationsTest(unittest.TestCase):
    def _write_sml(self, text):
        handle = tempfile.NamedTemporaryFile(
            "w", suffix=".sml", delete=False, encoding="utf-8"
        )
        handle.write(text)
        handle.close()
        self.addCleanup(lambda: os.unlink(handle.name))
        return Path(handle.name)

    def test_datatype_block_type_name_is_indexed(self):
        path = self._write_sml(
            "Datatype:\n  shape = One\n        | Comb (shape list)\nEnd\n"
        )
        self.assertEqual(DECL(path, {})["shape"], [2])

    def test_panlang_shape_is_resolvable(self):
        path = (
            Path(__file__).resolve().parents[2]
            / "cakeml/pancake/panLangScript.sml"
        )
        cache = {}
        self.assertIsNone(REF_ERROR(path, "shape", None, cache))
        self.assertIn("declares no", REF_ERROR(path, "no_such_type", None, cache))
        self.assertIn("not at line", REF_ERROR(path, "shape", 1, cache))

    def test_repeated_datatype_name_requires_line(self):
        path = self._write_sml(
            "Datatype:\n  foo = A\nEnd\nDatatype:\n  foo = B\nEnd\n"
        )
        cache = {}
        self.assertEqual(DECL(path, cache)["foo"], [2, 5])
        self.assertIn("multiple lines", REF_ERROR(path, "foo", None, cache))
        self.assertIsNone(REF_ERROR(path, "foo", 2, cache))
        self.assertIsNone(REF_ERROR(path, "foo", 5, cache))

    def test_record_field_is_not_a_datatype_name(self):
        path = self._write_sml(
            "Datatype:\n  expr = Rec <| field : num |>\nEnd\n"
        )
        names = DECL(path, {})
        self.assertEqual(names["expr"], [2])
        self.assertNotIn("field", names)


if __name__ == "__main__":
    unittest.main()
