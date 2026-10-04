"""Fail-closed coverage of the approved independent word-free dimension pair."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))


class TwoWordFreeDimensionsTest(unittest.TestCase):
    valid = "noncomputable def largest (t : Nat) (w : Nat) [NeZero t] [NeZero w] : ℝ := 2 ^ t / 2 ^ w"

    def errors(self, source=None, names=("t", "w")):
        return REFS["word_dimensions_as_widths_errors"](source or self.valid, "largest", names)

    def test_accepts_only_independent_explicit_dimensions(self):
        self.assertEqual(self.errors(), [])
        self.assertEqual(self.errors(self.valid.replace("ℝ", "Real")), [])

    def test_scanned_multiline_attribute_is_not_part_of_definition_header(self):
        lines = ['@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"',
                 ' (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts)]', self.valid]
        text = REFS["tagged_declaration_text"](lines, 1)
        self.assertEqual(self.errors(text), [])

    def test_rejects_missing_duplicate_or_fixed_dimensions(self):
        for names in [(), ("t",), ("t", "t"), ("t", "w", "x"), ("t", "0"), ("t", "52")]:
            with self.subTest(names=names):
                self.assertTrue(self.errors(names=names))

    def test_requires_both_independent_nat_and_nezero_binders(self):
        for replacement in ["[NeZero w]", "(w : Nat)", "(t : Nat)"]:
            with self.subTest(binder=replacement):
                self.assertTrue(self.errors(self.valid.replace(replacement, "")))
        self.assertTrue(self.errors(self.valid.replace("(w : Nat)", "(w : Int)")))
        self.assertTrue(self.errors(self.valid.replace("(w : Nat)", "{w : Nat}")))
        self.assertTrue(self.errors(self.valid.replace("[NeZero w]", "[NeZero t]")))
        self.assertTrue(self.errors(self.valid.replace("[NeZero w]", "[NeZero 0]")))

    def test_rejects_words_extra_dimensions_and_added_bounds(self):
        for extra in ["(x : BitVec t)", "(x : HolFloat t w)", "(n : Nat)",
                      "(positive : 0 < t)", "[NeZero 0]"]:
            with self.subTest(extra=extra):
                self.assertTrue(self.errors(self.valid.replace(" : ℝ", " " + extra + " : ℝ")))
        self.assertTrue(self.errors(self.valid.replace(" : ℝ", " : BitVec t")))
        self.assertTrue(self.errors(self.valid.replace(" : ℝ", " : Rat")))

    def test_attribute_scanner_preserves_order_and_rejects_repeated_qualifiers(self):
        def dimensions(text):
            site = list(REFS["hol_attribute_sites"](
                ['@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def" ' + text + ']'],
                include_word_dimensions_widths=True))[0]
            return site[-1]
        self.assertEqual(dimensions("(word_dimensions_as_widths := [t, w])"), ("t", "w"))
        self.assertTrue(self.errors(names=dimensions("(word_dimensions_as_widths := [])")))
        self.assertTrue(self.errors(names=dimensions("(word_dimensions_as_widths := [t]) (word_dimensions_as_widths := [w])")))
        self.assertTrue(self.errors(names=dimensions("(word_dimensions_as_widths := [t, w]) (word_dimensions_as_widths := [t, w])")))


class TwoDimensionManifestTest(unittest.TestCase):
    key = ("Flapjack/Example.lean", "largest")
    hol = ("HOL/src/floating-point/binary_ieeeScript.sml", "largest_def")

    def record(self, **kwargs):
        row = dict(lean_path=self.key[0], lean_name=self.key[1], hol_path=self.hol[0],
                   hol_name=self.hol[1], statement_status="reviewed_word_dimensions_as_widths",
                   word_dimensions_as_widths=["t", "w"],
                   reviewer="source comparison word_dimensions_as_widths: independent t and w")
        row.update(kwargs)
        return row

    def tag(self, **kwargs):
        fields = [*self.hol, (), (), (), (), False, (), False, False, (), (), None,
                  (), (), False, False, (), ("t", "w")]
        for index, value in kwargs.items():
            fields[int(index)] = value
        return {self.key: tuple(fields)}

    def errors(self, row=None, tags=None):
        return MAP["validate_inventory"]([row or self.record()], {self.key}, tags or self.tag(), set())

    def test_accepts_matching_pair_and_preserves_singular_route(self):
        self.assertEqual(self.errors(), [])
        row = self.record(word_dimensions_as_widths=None, word_dimension_as_width="t",
                          statement_status="reviewed_word_dimension_as_width")
        row.pop("word_dimensions_as_widths")
        self.assertEqual(self.errors(row, self.tag(**{"12": "t", "18": ()})), [])

    def test_rejects_manifest_mismatch_unqualified_or_exact_status(self):
        for row in [self.record(word_dimensions_as_widths=["w", "t"]),
                    self.record(word_dimensions_as_widths=[]),
                    self.record(statement_status="reviewed_exact"),
                    self.record(reviewer="kernel checked")]:
            with self.subTest(row=row):
                self.assertTrue(self.errors(row))
        self.assertTrue(self.errors(tags=self.tag(**{"18": ()})))

    def test_rejects_conflicting_qualifiers_and_duplicate_pair(self):
        for index, value in [("12", "t"), ("9", True), ("3", ("name",)),
                             ("6", True), ("18", ("t", "t"))]:
            with self.subTest(index=index):
                self.assertTrue(self.errors(tags=self.tag(**{index: value})))

    def test_native_export_requires_identical_ordered_pair(self):
        row = self.record()
        export = dict(lean_name="Example.largest", hol_path=self.hol[0], hol_name=self.hol[1],
                      qualifiers={"word_dimensions_as_widths": ["t", "w"]})
        self.assertEqual(EXPORT["check_records"]([row], [export]), 1)
        for fields in [["w", "t"], ["t"], [], "t"]:
            bad = dict(export, qualifiers={"word_dimensions_as_widths": fields})
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                EXPORT["check_records"]([row], [bad])


if __name__ == "__main__":
    unittest.main()
