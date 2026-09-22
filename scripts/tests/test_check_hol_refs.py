"""Regression checks for the HOL-reference scanner."""

import runpy
import unittest
from pathlib import Path


SITES = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check-hol-refs.py")
)["hol_attribute_sites"]


class HolAttributeSitesTest(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]'])),
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def")],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf")],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def")],
        )


if __name__ == "__main__":
    unittest.main()
