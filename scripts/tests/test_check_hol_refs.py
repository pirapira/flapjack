"""Regression checks for the HOL-reference scanner."""

import runpy
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
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, ())],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf", None, ())],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, ())],
        )

    def test_source_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"',
                        '  "locals_rel_wf_shape" 2345]'])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "locals_rel_wf_shape", 2345, ())],
        )

    def test_list_as_array_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml"',
                '  "dec_deg_def" (list_as_array := [degrees, moves])]'
            ])),
            [(1, "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml",
              "dec_deg_def", None, ("degrees", "moves"))],
        )

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

    def test_duplicate_name_requires_correct_line(self):
        path = Path(__file__).resolve().parents[2] / \
            "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
        cache = {}
        self.assertIn("multiple lines", REF_ERROR(path, "locals_rel_wf_shape", None, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 2345, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 3008, cache))
        self.assertIn("not at line", REF_ERROR(path, "locals_rel_wf_shape", 2346, cache))


if __name__ == "__main__":
    unittest.main()
