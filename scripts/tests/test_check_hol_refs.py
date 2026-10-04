"""Regression checks for the HOL-reference scanner."""

import os
import runpy
import shutil
import tempfile
import unittest
import contextlib
import io
from unittest.mock import patch
from pathlib import Path


CHECKER = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check-hol-refs.py")
)
SITES = CHECKER["hol_attribute_sites"]
REF_ERROR = CHECKER["hol_ref_error"]
_REPO_REALS_RENDERING_NAMES = None


def repo_reals_rendering_names():
    """The real tree's rendering-name scan, computed once for the module."""
    global _REPO_REALS_RENDERING_NAMES
    if _REPO_REALS_RENDERING_NAMES is None:
        _REPO_REALS_RENDERING_NAMES = CHECKER["reals_rendering_names"](CHECKER["ROOT"])
    return _REPO_REALS_RENDERING_NAMES


class ExternalHolSourcesTest(unittest.TestCase):
    def fixture(self, root):
        import hashlib
        import json
        base = root / "hol4"
        (base / "src/finite_maps").mkdir(parents=True)
        (base / "src/n-bit").mkdir(parents=True)
        (base / "src/coalgebras").mkdir(parents=True)
        (base / "src/coretypes").mkdir(parents=True)
        (base / "examples/pl-semantics/lprefix_lub").mkdir(parents=True)
        (base / "COPYRIGHT").write_text("retained license")
        (base / "src/finite_maps/sptreeScript.sml").write_text("Theorem domain_union: T Proof simp[] QED")
        (base / "examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml").write_text(
            "Theorem IMP_build_lprefix_lub_EQ: T Proof simp[] QED")
        (base / "src/n-bit/fcpScript.sml").write_text(
            "Definition dimindex_def: dimindex = 1 End")
        (base / "src/coalgebras/llistScript.sml").write_text(
            "Theorem LPREFIX_TRANS: T Proof simp[] QED")
        (base / "src/coretypes/optionScript.sml").write_text(
            'val some_def = new_definition("some_def", ``some P = NONE``);')
        lock = {"repository": CHECKER["EXTERNAL_HOL_REPOSITORY"], "commit": "a" * 40,
                "files": {p: hashlib.sha256((base / p).read_bytes()).hexdigest()
                          for p in sorted(CHECKER["EXTERNAL_HOL_FILES"])}}
        (base / "SOURCES.json").write_text(json.dumps(lock))

    def test_repository_snapshot_pin(self):
        self.assertIsNone(CHECKER["hol_source_error"](CHECKER["ROOT"], CHECKER["EXTERNAL_HOL_PATH"]))
        self.assertIsNone(
            CHECKER["hol_source_error"](CHECKER["ROOT"], CHECKER["EXTERNAL_HOL_LPREFIX_LUB_PATH"]))
        self.assertIsNone(
            CHECKER["hol_source_error"](CHECKER["ROOT"], CHECKER["EXTERNAL_HOL_FCP_PATH"]))
        self.assertIsNone(
            CHECKER["hol_source_error"](CHECKER["ROOT"], CHECKER["EXTERNAL_HOL_LLIST_PATH"]))

    def test_option_source_and_old_style_declaration(self):
        path = CHECKER["EXTERNAL_HOL_OPTION_PATH"]
        self.assertIsNone(CHECKER["hol_source_error"](CHECKER["ROOT"], path))
        self.assertIsNone(REF_ERROR(CHECKER["ROOT"] / path, "some_def", 794, {}))

    def test_binary_ieee_verified_submodule_source_and_declaration(self):
        path = "HOL/src/floating-point/binary_ieeeScript.sml"
        self.assertIsNone(CHECKER["hol_source_error"](CHECKER["ROOT"], path))
        self.assertIsNone(REF_ERROR(CHECKER["ROOT"] / path, "float_some_qnan_def", 495, {}))
        self.assertIsNotNone(REF_ERROR(CHECKER["ROOT"] / path, "missing_ieee_def", None, {}))
        self.assertIsNotNone(CHECKER["hol_source_error"](
            CHECKER["ROOT"], "hol4/src/floating-point/binary_ieeeScript.sml"))

    def test_missing_option_pin_rejected(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            manifest = root / "hol4/SOURCES.json"
            lock = json.loads(manifest.read_text())
            del lock["files"]["src/coretypes/optionScript.sml"]
            manifest.write_text(json.dumps(lock))
            self.assertIsNotNone(CHECKER["hol_source_error"](
                root, CHECKER["EXTERNAL_HOL_OPTION_PATH"]))

    def test_upstream_identity_rejected(self):
        import json
        for field, value in [("commit", "not-a-commit"), ("repository", "https://example.com/other")]:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                manifest = root / "hol4/SOURCES.json"
                lock = json.loads(manifest.read_text())
                lock[field] = value
                manifest.write_text(json.dumps(lock))
                self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_valid_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            self.assertIsNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_missing_lprefix_pin_rejected(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            manifest = root / "hol4/SOURCES.json"
            lock = json.loads(manifest.read_text())
            del lock["files"]["examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml"]
            manifest.write_text(json.dumps(lock))
            self.assertIsNotNone(
                CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_LPREFIX_LUB_PATH"]))

    def test_missing_fcp_pin_rejected(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            manifest = root / "hol4/SOURCES.json"
            lock = json.loads(manifest.read_text())
            del lock["files"]["src/n-bit/fcpScript.sml"]
            manifest.write_text(json.dumps(lock))
            self.assertIsNotNone(
                CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_FCP_PATH"]))

    def test_missing_llist_pin_rejected(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            manifest = root / "hol4/SOURCES.json"
            lock = json.loads(manifest.read_text())
            del lock["files"]["src/coalgebras/llistScript.sml"]
            manifest.write_text(json.dumps(lock))
            self.assertIsNotNone(
                CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_LLIST_PATH"]))

    def test_valid_llist_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            self.assertIsNone(
                CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_LLIST_PATH"]))
            self.assertIsNotNone(CHECKER["hol_source_error"](
                root, "hol4/src/coalgebras/otherScript.sml"))

    def test_source_and_license_drift_rejected(self):
        for relative in ["COPYRIGHT", "src/finite_maps/sptreeScript.sml",
                         "examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml",
                         "src/n-bit/fcpScript.sml",
                         "src/coalgebras/llistScript.sml",
                         "src/coretypes/optionScript.sml"]:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                (root / "hol4" / relative).write_text("altered")
                self.assertIn("mismatch", CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_unpinned_and_traversal_rejected(self):
        for path in ["hol4/otherScript.sml", "/tmp/source.sml", "cakeml/../source.sml",
                     "cakeml//source.sml", "hol4/src/finite_maps/./sptreeScript.sml"]:
            with self.subTest(path=path):
                self.assertIsNotNone(CHECKER["hol_source_error"](Path("/tmp"), path))

    def test_missing_and_malformed_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))
            self.fixture(root)
            (root / "hol4/SOURCES.json").write_text("[]")
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_symlink_rejected_even_with_matching_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            source = root / CHECKER["EXTERNAL_HOL_PATH"]
            source.rename(root / "source-copy")
            source.symlink_to(root / "source-copy")
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))


class HolAttributeSitesTest(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]'])),
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_source_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"',
                        '  "locals_rel_wf_shape" 2345]'])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "locals_rel_wf_shape", 2345, (), (), (), (), False, (), False, False, ())],
        )

    def test_list_as_array_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml"',
                '  "dec_deg_def" (list_as_array := [degrees, moves])]'
            ])),
            [(1, "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml",
              "dec_deg_def", None, ("degrees", "moves"), (), (), (), False, (), False, False, ())],
        )

    def test_names_as_string_and_boundary_qualifiers(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/panLangScript.sml" "varname"',
                '  (names_as_string := [name, generated])',
                '  (names_as_string_boundary := [generated])]',
            ])),
            [(1, "cakeml/pancake/panLangScript.sml", "varname", None,
              (), ("name", "generated"), ("generated",), (), False, (), False, False, ())],
        )

    def test_word_dimension_as_width_qualifier(self):
        sites = list(SITES([
            '@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"',
            '  (word_dimension_as_width := width)]',
        ], include_fmap_existentials=True, include_word_dimension_width=True))
        self.assertEqual(sites[0][-1], "width")
        self.assertEqual(sites[0][-2], ())

    def test_nested_fmap_function_qualifier(self):
        sites = list(SITES([
            '@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type"',
            '  (fmap_as_finite_support_function := [argument_4, result_3])]',
        ], include_fmap_function=True))
        self.assertEqual(sites[0][-1], ("argument_4", "result_3"))

    def test_heterogeneous_nested_fmap_function_qualifier(self):
        sites = list(SITES([
            '@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def"',
            '  (fmap_as_finite_support_heterogeneous_function := [argument_1, result_2])]',
        ], include_fmap_heterogeneous_function=True))
        self.assertEqual(sites[0][-1], ("argument_1", "result_2"))

    def test_empty_heterogeneous_fmap_qualifier_is_not_silently_ignored(self):
        sites = list(SITES([
            '@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def"',
            '  (fmap_as_finite_support_heterogeneous_function := [])]',
        ], include_fmap_heterogeneous_function=True))
        self.assertEqual(sites[0][-1], ("",))


class FmapFunctionQualifierTest(unittest.TestCase):
    CHECK = staticmethod(CHECKER["fmap_as_finite_support_function_errors"])
    POSITIONS = ("argument_4", "result_3")
    SOURCE = """/-- HOL gc function type. -/
abbrev WordSemGcFun (width : Nat) : Type :=
  (List Nat × (Nat → Nat) × (Nat → Bool) × HolFiniteMapExact Nat Nat) →
    Option (List Nat × (Nat → Nat) × HolFiniteMapExact Nat Nat)
"""
    MODULE = SOURCE + """
theorem holFmapAsFiniteSupportWitness : True := by trivial
"""

    def test_main_rejects_out_of_range_function_position(self):
        main = CHECKER["main"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "cakeml/pancake").mkdir(parents=True)
            hol = root / "cakeml/pancake/fixtureScript.sml"
            hol.write_text("Definition gc_fun_def: gc_fun = T End\n")
            lean = root / "Fixture.lean"
            lean.write_text(
                '@[hol "cakeml/pancake/fixtureScript.sml" "gc_fun_def" '
                '(fmap_as_finite_support_function := [argument_9, result_3])]\n'
                + self.MODULE
            )
            output = io.StringIO()
            with patch.dict(main.__globals__, {
                "ROOT": root,
                "lean_files": lambda: [lean],
                "reachable_modules": lambda: {"Fixture"},
                "reals_rendering_names": lambda _: set(),
            }), contextlib.redirect_stderr(output), contextlib.redirect_stdout(output):
                self.assertEqual(main([]), 1)
            self.assertIn("argument_9 is outside the 4-component product", output.getvalue())

    def test_accepts_exact_argument_and_result_product_slots(self):
        self.assertEqual(
            self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                       "WordSemGcFun", self.POSITIONS),
            [],
        )

    def test_rejects_missing_argument_or_result_position(self):
        errors = self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                            "WordSemGcFun", ("argument_4",))
        self.assertTrue(any("requires both argument_N and result_N" in error
                            for error in errors))

    def test_rejects_wrong_slot_and_raw_function_map(self):
        wrong_slot = self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                                "WordSemGcFun", ("argument_3", "result_3"))
        self.assertTrue(any("argument_3 must use HolFiniteMapExact" in error
                            for error in wrong_slot))
        raw = self.SOURCE.replace("HolFiniteMapExact Nat Nat", "Nat → Option Nat")
        raw_errors = self.CHECK((self.MODULE.replace(self.SOURCE, raw)).splitlines(),
                                raw, "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("must use HolFiniteMapExact" in error
                            for error in raw_errors))

    def test_requires_same_map_type_and_canonical_witness(self):
        changed = self.SOURCE.replace(
            "HolFiniteMapExact Nat Nat)", "HolFiniteMapExact Nat Bool)", 1
        )
        changed_module = self.MODULE.replace(self.SOURCE, changed)
        errors = self.CHECK(changed_module.splitlines(), changed,
                            "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("same exact type" in error for error in errors))
        witness_errors = self.CHECK(self.SOURCE.splitlines(), self.SOURCE,
                                    "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("requires same-module canonical" in error
                            for error in witness_errors))

    def test_word_qualifier_checks_type_alias_body(self):
        check = CHECKER["words_as_type_indexed_bitvec_errors"]
        alias = """abbrev Words (width : Nat) [NeZero width] : Type :=
  BitVec width → BitVec width
"""
        self.assertEqual(check(alias, "Words"), [])
        missing_positive = alias.replace(" [NeZero width]", "")
        self.assertTrue(any("[NeZero width]" in error
                            for error in check(missing_positive, "Words")))


class HeterogeneousFmapFunctionQualifierTest(unittest.TestCase):
    CHECK = staticmethod(
        CHECKER["fmap_as_finite_support_heterogeneous_function_errors"]
    )
    POSITIONS = ("argument_1", "result_2")
    SOURCE = """@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def"
  (fmap_as_finite_support_heterogeneous_function := [argument_1, result_2])]
def lookupCodeHOLFiniteExact
    (code : HolFiniteMapExact MlS CodeEntry)
    (fname : MlS) (arguments : List Value) :
    Option (Prog × HolFiniteMapExact MlS Value × Shape) := none
"""
    WITNESS = """theorem holFmapAsFiniteSupportHeterogeneousFunctionWitness_lookupCodeHOLFiniteExact
    (code : HolFiniteMapExact MlS CodeEntry) (fname : MlS) (arguments : List Value) :
    (lookupCodeHOLFiniteExact code fname arguments).map
      (fun (body, locals, shape) => (body, locals.lookup, shape)) =
      lookupCodeHOLExact code.lookup fname arguments := by sorry
"""

    def module(self, source=None, witness=None):
        return (self.SOURCE if source is None else source) + (
            self.WITNESS if witness is None else witness
        )

    def test_accepts_distinct_canonical_input_and_result_maps(self):
        self.assertEqual(
            self.CHECK(self.module().splitlines(), self.SOURCE,
                       "lookupCodeHOLFiniteExact", self.POSITIONS),
            [],
        )

    def test_rejects_extra_implicit_proof_and_instance_binders(self):
        equality = self.WITNESS.split(" :\n", 1)[1].split(" :=", 1)[0]
        for binder in ("{h : True}", "[h : Inhabited Value]",
                       "{h : lookupCodeHOLExact code.lookup fname arguments = none}",
                       "{h : " + equality + "}"):
            witness = self.WITNESS.replace("(arguments : List Value) :",
                                          f"(arguments : List Value) {binder} :")
            with self.subTest(binder=binder):
                errors = self.CHECK(self.module(witness=witness).splitlines(),
                                    self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS)
                self.assertTrue(any("extra implicit premises" in e for e in errors))

    def test_accepts_matching_implicit_width_parameters(self):
        source = self.SOURCE.replace("    (code :", "    {width : Nat} [NeZero width] (code :", 1)
        witness = self.WITNESS.replace("    (code :", "    {width : Nat} [NeZero width] (code :", 1)
        self.assertEqual(self.CHECK(self.module(source, witness).splitlines(),
                                   source, "lookupCodeHOLFiniteExact", self.POSITIONS), [])

    def test_rejects_ambient_section_premises(self):
        equality = self.WITNESS.split(" :\n", 1)[1].split(" :=", 1)[0]
        for command in (
            "variable {h : ∀ code fname arguments, " + equality + "}\ninclude h\n",
            "variable {h : True}\n",
            "variables {h : True}\n",
            "include h in\n",
            "omit h in\n",
            "section Ambient variable {h : True}\n",
        ):
            with self.subTest(command=command):
                module = self.SOURCE + command + self.WITNESS
                errors = self.CHECK(module.splitlines(), self.SOURCE,
                                    "lookupCodeHOLFiniteExact", self.POSITIONS)
                self.assertTrue(any("without ambient" in e for e in errors))

    def test_rejects_kernel_valid_inherited_premise_reproducer(self):
        source = (Path(__file__).parent / "fixtures" /
                  "heterogeneous_ambient_premise.lean").read_text()
        errors = self.CHECK(source.splitlines(), source,
                            "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("without ambient" in e for e in errors))

    def test_accepts_sections_without_ambient_binders_and_commented_commands(self):
        module = "section\n/- variable {h : True}; include h -/\n" + self.module() + "end\n"
        self.assertEqual(self.CHECK(module.splitlines(), self.SOURCE,
                                   "lookupCodeHOLFiniteExact", self.POSITIONS), [])

    def test_rejects_inert_or_embedded_raw_application(self):
        raw = "lookupCodeHOLExact code.lookup fname arguments"
        for replacement in (f"(fun _ => none) ({raw})", f"id ({raw})",
                            f"({raw}) extra", f"(let discarded := {raw}; none)"):
            witness = self.WITNESS.replace(raw, replacement)
            with self.subTest(replacement=replacement):
                errors = self.CHECK(self.module(witness=witness).splitlines(),
                                    self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS)
                self.assertTrue(any("independent raw lookup" in e for e in errors))

    def test_rejects_inert_or_trailing_canonical_projection(self):
        projection = "(lookupCodeHOLFiniteExact code fname arguments).map\n      (fun (body, locals, shape) => (body, locals.lookup, shape))"
        for replacement in (f"(fun _ => none) ({projection})",
                            f"id ({projection})", f"{projection} extra",
                            projection.replace("(body, locals.lookup, shape))",
                                               "(body, locals.lookup, shape) extra)")):
            witness = self.WITNESS.replace(projection, replacement)
            with self.subTest(replacement=replacement):
                self.assertTrue(self.CHECK(self.module(witness=witness).splitlines(),
                                          self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS))

    def test_rejects_raw_map_in_either_position(self):
        raw_input = self.SOURCE.replace(
            "HolFiniteMapExact MlS CodeEntry", "MlS → Option CodeEntry", 1
        )
        input_errors = self.CHECK(self.module(raw_input).splitlines(),
                                  raw_input,
                                  "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("argument_1 must itself be HolFiniteMapExact" in e
                            for e in input_errors))
        raw_result = self.SOURCE.replace(
            "HolFiniteMapExact MlS Value", "MlS → Option Value", 1
        )
        result_errors = self.CHECK(self.module(raw_result).splitlines(),
                                   raw_result,
                                   "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("result_2 must itself be HolFiniteMapExact" in e
                            for e in result_errors))

    def test_rejects_omitted_map_occurrences_and_missing_witness(self):
        omitted = self.SOURCE.replace(
            "argument_1, result_2", "argument_1, result_1"
        )
        errors = self.CHECK(self.module(omitted).splitlines(), omitted,
                            "lookupCodeHOLFiniteExact",
                            ("argument_1", "result_1"))
        self.assertTrue(any("result_1 must itself be HolFiniteMapExact" in e
                            for e in errors))
        no_witness = self.CHECK(self.SOURCE.splitlines(), self.SOURCE,
                                "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("requires same-module projection theorem" in e
                            for e in no_witness))

    def test_rejects_vacuous_projection_witness(self):
        witness = self.WITNESS.replace(
            "lookupCodeHOLExact code.lookup fname arguments",
            "lookupCodeHOLFiniteExact code fname arguments",
        )
        errors = self.CHECK(self.module(witness=witness).splitlines(),
                            self.SOURCE,
                            "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("exactly one equality side" in e for e in errors))

    def test_rejects_wrong_argument_order_and_wrong_result_projection_slot(self):
        wrong_target_order = self.WITNESS.replace(
            "lookupCodeHOLFiniteExact code fname arguments",
            "lookupCodeHOLFiniteExact code arguments fname",
        )
        errors = self.CHECK(
            self.module(witness=wrong_target_order).splitlines(),
            self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
        )
        self.assertTrue(any("tagged operation to its explicit inputs" in e
                            for e in errors))

        wrong_raw_order = self.WITNESS.replace(
            "lookupCodeHOLExact code.lookup fname arguments",
            "lookupCodeHOLExact code.lookup arguments fname",
        )
        errors = self.CHECK(
            self.module(witness=wrong_raw_order).splitlines(),
            self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
        )
        self.assertTrue(any("independent raw lookup" in e for e in errors))

        wrong_projection = self.WITNESS.replace(
            "(body, locals.lookup, shape)", "(body, shape, locals.lookup)"
        )
        errors = self.CHECK(
            self.module(witness=wrong_projection).splitlines(),
            self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
        )
        self.assertTrue(any("selected result_N map slot" in e for e in errors))

    def test_rejects_extra_or_malformed_positions(self):
        for positions in (
            ("argument_1",),
            ("argument_1", "result_2", "result_3"),
            ("argument_1", "argument_2"),
            ("argument_0", "result_2"),
        ):
            with self.subTest(positions=positions):
                errors = self.CHECK(
                    self.module().splitlines(), self.SOURCE,
                    "lookupCodeHOLFiniteExact", positions,
                )
                self.assertTrue(errors)

    def test_requires_the_input_lookup_and_output_projection(self):
        missing_input_projection = self.WITNESS.replace(
            "lookupCodeHOLExact code.lookup fname arguments",
            "lookupCodeHOLExact code fname arguments",
        )
        errors = self.CHECK(
            self.module(witness=missing_input_projection).splitlines(),
            self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
        )
        self.assertTrue(any("canonical input's `.lookup`" in error for error in errors))

        missing_output_projection = self.WITNESS.replace("locals.lookup", "locals")
        errors = self.CHECK(
            self.module(witness=missing_output_projection).splitlines(),
            self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
        )
        self.assertTrue(any("project exactly one returned map" in error for error in errors))

    def test_projection_witness_has_no_extra_hypothesis_or_changed_inputs(self):
        for witness in (
            self.WITNESS.replace(
                "(arguments : List Value) :", "(arguments : List Value) (h : True) :"
            ),
            self.WITNESS.replace(
                "lookupCodeHOLExact code.lookup fname arguments",
                "lookupCodeHOLExact code.lookup arguments",
            ),
        ):
            with self.subTest(witness=witness):
                errors = self.CHECK(
                    self.module(witness=witness).splitlines(),
                    self.SOURCE, "lookupCodeHOLFiniteExact", self.POSITIONS,
                )
                self.assertTrue(any("quantify exactly" in e or "every explicit" in e
                                    for e in errors))

    def test_requires_selected_slots_to_be_the_map_carriers(self):
        wrapped = self.SOURCE.replace(
            "(code : HolFiniteMapExact MlS CodeEntry)",
            "(code : HolFiniteMapExact MlS CodeEntry × Nat)",
        )
        errors = self.CHECK(self.module(wrapped).splitlines(), wrapped,
                            "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("must itself be HolFiniteMapExact" in e for e in errors))

    def test_rejects_extra_map_slot_but_not_body_implementation_mentions(self):
        extra_binder = self.SOURCE.replace(
            "(fname : MlS)", "(fname : MlS) (other : HolFiniteMapExact MlS Bool)"
        )
        errors = self.CHECK(self.module(extra_binder).splitlines(), extra_binder,
                            "lookupCodeHOLFiniteExact", self.POSITIONS)
        self.assertTrue(any("exactly the two selected" in e for e in errors))

        body_map = self.SOURCE.replace(
            ":= none", ":= let _ : HolFiniteMapExact MlS Bool := sorry; none"
        )
        self.assertEqual(
            self.CHECK(self.module(body_map).splitlines(), body_map,
                       "lookupCodeHOLFiniteExact", self.POSITIONS),
            [],
        )

    def test_word_dimension_as_width_requires_its_nat_and_nezero_binders(self):
        check = CHECKER["word_dimension_as_width_errors"]
        valid = "def example (width : Nat) [NeZero width] : Nat := width"
        self.assertEqual(check(valid, "example", "width"), [])
        missing_nezero = "def example (width : Nat) : Nat := width"
        self.assertTrue(any("retain its own `[NeZero width]`" in error
                            for error in check(missing_nezero, "example", "width")))
        wrong_binder = "def example (n : Nat) [NeZero n] : Nat := n"
        self.assertTrue(any("explicit `(width : Nat)` binder" in error
                            for error in check(wrong_binder, "example", "width")))
        word_carrier = "def example (width : Nat) [NeZero width] : BitVec width := 0"
        self.assertTrue(any("word-free signatures" in error
                            for error in check(word_carrier, "example", "width")))

    def test_reals_as_rational_cuts_site_flag(self):
        sites = list(SITES([
            '@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"',
            '  (reals_as_rational_cuts)]',
        ], include_fmap_existentials=True, include_word_dimension_width=True,
            include_fmap_function=True, include_reals_as_rational_cuts=True))
        self.assertTrue(sites[0][-1])
        plain = list(SITES([
            '@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"]',
        ], include_reals_as_rational_cuts=True))
        self.assertFalse(plain[0][-1])

    def test_reals_as_rational_cuts_required_exactly_for_rendering_users(self):
        check = CHECKER["reals_as_rational_cuts_errors"]
        names = {"holFp64Sqrt", "holFp64Add"}
        user = "noncomputable def uop : BitVec 64 -> BitVec 64\n  | x => holFp64Sqrt .roundTiesToEven x"
        self.assertEqual(check(user, True, names), [])
        self.assertTrue(any("must carry (reals_as_rational_cuts)" in error
                            for error in check(user, False, names)))
        dependent = "def evaluate (s : State) : State := match inst s with | _ => s"
        self.assertEqual(check(dependent, False, names), [])
        self.assertTrue(any("dependents inherit" in error
                            for error in check(dependent, True, names)))
        comment_only = "def f : Nat := 0 -- see holFp64Sqrt"
        self.assertEqual(check(comment_only, False, names), [])

    def test_reals_as_rational_cuts_ignores_following_declarations(self):
        check = CHECKER["reals_as_rational_cuts_errors"]
        names = {"holFp64Equal"}
        datatype = """inductive FpCmp where
  | less | equal
  deriving DecidableEq

/-- next -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp_comp_def"]
noncomputable def cmp : FpCmp -> Bool
  | .equal => holFp64Equal 0 0
"""
        self.assertEqual(check(datatype, False, names), [])

    def test_rounding_enum_is_source_bound_and_real_free(self):
        root = CHECKER["ROOT"]
        self.assertTrue(CHECKER["source_bound_rounding_enum"](root))
        names = repo_reals_rendering_names()
        self.assertNotIn("HolRounding", names)
        check = CHECKER["reals_as_rational_cuts_errors"]
        enum = "def modes : Option HolRounding := some HolRounding.roundTiesToEven"
        self.assertEqual(check(enum, False, names), [])
        for source in [
            "def mixed (m : HolRounding) := holRound m 0",
            "def mixed (m : HolRounding) : HolFloat 52 11 := holRound m 0",
            "def mixed (m : HolRounding) := holFloatToReal (holRound m 0)",
        ]:
            self.assertTrue(any("must carry" in e for e in check(source, False, names)))

    def test_rounding_enum_exemption_fails_closed_on_carrier_or_owner_changes(self):
        enum = """namespace Flapjack
inductive HolRounding where
  | roundTiesToEven
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero
  deriving DecidableEq, Repr
"""
        hol = """Datatype:
  rounding = roundTiesToEven | roundTowardPositive
           | roundTowardNegative | roundTowardZero
End
"""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            owner = root / "Flapjack/Misc/BinaryIeeeRound.lean"
            original = root / "HOL/src/floating-point/binary_ieeeScript.sml"
            owner.parent.mkdir(parents=True)
            original.parent.mkdir(parents=True)
            owner.write_text(enum)
            original.write_text(hol)
            check = CHECKER["source_bound_rounding_enum"]
            self.assertTrue(check(root))
            for changed in [enum.replace("roundTowardZero", "extraConstructor"),
                            enum.replace("| roundTiesToEven", "| roundTiesToEven (r : Rat)"),
                            enum.replace("namespace Flapjack", "namespace Shadow"),
                            "abbrev HolRounding := Rat\n"]:
                owner.write_text(changed)
                self.assertFalse(check(root))
            owner.write_text(enum)
            original.write_text(hol.replace("roundTowardZero", "extraConstructor"))
            self.assertFalse(check(root))
            original.write_text("(* outer (* nested *) " + hol + " *)\n" +
                                hol.replace("roundTowardZero", "extraConstructor"))
            self.assertFalse(check(root))
            original.write_text(hol)
            shadow = root / "Flapjack/Shadow.lean"
            for declaration in ["inductive HolRounding where | fake\n",
                                "abbrev HolRounding := Rat\n",
                                "abbrev Local.HolRounding := Rat\n"]:
                shadow.write_text(declaration)
                self.assertFalse(check(root))
                self.assertIn("HolRounding", CHECKER["reals_rendering_names"](root))
            shadow.unlink()
            original.unlink()
            self.assertFalse(check(root))

    def test_bit_only_ieee_forms_do_not_require_real_qualifier(self):
        root = CHECKER["ROOT"]
        names = repo_reals_rendering_names()
        forms = CHECKER["REAL_FREE_IEEE_FORMS"]
        self.assertEqual(len(CHECKER["real_free_ieee_names"](root)),
                         len(CHECKER["REAL_FREE_IEEE_FORMS"]))
        for (_, name), form in forms.items():
            self.assertNotIn(name, names)
            self.assertEqual(CHECKER["reals_as_rational_cuts_errors"](form, False, names), [])
        # Rational values/rounding/sqrt still need the marker.
        for name in ("holFloatToReal", "holFp64Add", "holFp64Sqrt", "holFp64SqrtReal"):
            self.assertIn(name, names)
            self.assertTrue(CHECKER["reals_as_rational_cuts_errors"](
                "def caller := " + name, False, names))

    def test_bit_only_ieee_dependency_changes_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for relative in {path for path, _ in CHECKER["REAL_FREE_IEEE_FORMS"]}:
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text((CHECKER["ROOT"] / relative).read_text())
            self.assertEqual(len(CHECKER["real_free_ieee_names"](root)),
                         len(CHECKER["REAL_FREE_IEEE_FORMS"]))
            target = root / "Flapjack/Misc/BinaryIeee.lean"
            target.write_text(target.read_text().replace(
                "{ x with sign := 0 }", "{ x with sign := holFloatToReal x }"))
            self.assertEqual(CHECKER["real_free_ieee_names"](root), set())
            names = CHECKER["reals_rendering_names"](root)
            self.assertIn("holFp64ToFloat", names)
            self.assertIn("holFloatAbs", names)

    def test_bit_only_ieee_changed_width_or_duplicate_rejected(self):
        for change in ("width", "duplicate", "namespace", "shadow", "theorem_shadow", "field",
                       "missing_binder"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                for relative in {path for path, _ in CHECKER["REAL_FREE_IEEE_FORMS"]}:
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text((CHECKER["ROOT"] / relative).read_text())
                target = root / "Flapjack/Misc/MachineIeee.lean"
                if change == "width":
                    target.write_text(target.read_text().replace("extractLsb' 52 11", "extractLsb' 51 12"))
                elif change == "duplicate":
                    target.write_text(target.read_text() + "\ndef holFp64Abs (a : BitVec 64) := a\n")
                elif change == "namespace":
                    target.write_text(target.read_text().replace("namespace Flapjack", "namespace Other"))
                elif change == "shadow":
                    (root / "Flapjack/Shadow.lean").write_text("abbrev Local.holFp64Abs := Nat\n")
                elif change == "theorem_shadow":
                    (root / "Flapjack/Shadow.lean").write_text("theorem Local.holFp64Abs : True := by trivial\n")
                elif change == "missing_binder":
                    # The HOL dimindex positivity binders are part of the pinned carrier.
                    target = root / "Flapjack/Misc/BinaryIeee.lean"
                    target.write_text(target.read_text().replace(
                        "structure HolFloat (t : Nat) (w : Nat) [NeZero t] [NeZero w] where",
                        "structure HolFloat (t : Nat) (w : Nat) where"))
                else:
                    target = root / "Flapjack/Misc/BinaryIeee.lean"
                    target.write_text(target.read_text().replace("x.exponent ≠ 0", "x.exponent = 0"))
                self.assertEqual(CHECKER["real_free_ieee_names"](root), set())

    def test_bit_only_ieee_compiled_overrides_fail_closed(self):
        changes = {
            "implemented_by": '@[implemented_by replacement]\n',
            "combined_attributes": '@[inline, implemented_by replacement]\n',
            "multiline_attribute": '@[\n implemented_by replacement\n]\n',
            "extern": '@[extern "replacement"]\n',
            "unsafe": 'unsafe ',
        }
        for change in (*changes, "attribute_command", "imported_attribute"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                for relative in {path for path, _ in CHECKER["REAL_FREE_IEEE_FORMS"]}:
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text((CHECKER["ROOT"] / relative).read_text())
                target = root / "Flapjack/Misc/MachineIeee.lean"
                if change in changes:
                    target.write_text(target.read_text().replace(
                        "def holFp64Abs", changes[change] + "def holFp64Abs", 1))
                elif change == "attribute_command":
                    target.write_text(target.read_text() +
                        "\nattribute [implemented_by replacement] Flapjack.holFp64Abs\n")
                else:
                    (root / "Flapjack/Override.lean").write_text(
                        "import Flapjack.Misc.MachineIeee\n"
                        "attribute [extern \"replacement\"]\n  Flapjack.holFp64Abs\n")
                self.assertEqual(CHECKER["real_free_ieee_names"](root), set())
                self.assertIn("holFp64Abs", CHECKER["reals_rendering_names"](root))

    def test_reals_rendering_names_cover_nested_sqrt_real(self):
        # Real-tree membership is asserted by the bit-only test; nested
        # discovery by test_reals_rendering_names_recurse_beneath_binary_ieee.
        names = {"holFp64SqrtReal"}
        user = "noncomputable def sqrtCase : BitVec 64 -> BitVec 64 := holFp64SqrtReal .roundTiesToEven"
        check = CHECKER["reals_as_rational_cuts_errors"]
        self.assertEqual(check(user, True, names), [])
        self.assertTrue(any("must carry" in e for e in check(user, False, names)))
        self.assertEqual(check("def f : Nat := 0 -- holFp64SqrtReal", False, names), [])

    def test_reals_rendering_names_recurse_beneath_binary_ieee(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            nested = root / "Flapjack/Misc/BinaryIeeeSqrt"
            nested.mkdir(parents=True)
            (nested / "RoundAgreement.lean").write_text(
                "noncomputable def holFp64SqrtReal : Nat := 0\n"
                "theorem comparisonOnly : True := trivial\n")
            names = CHECKER["reals_rendering_names"](root)
            self.assertIn("holFp64SqrtReal", names)
            self.assertNotIn("comparisonOnly", names)

    def test_fmap_as_finite_support_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"',
                '  (fmap_as_finite_support := [locals, globals])]'
            ])),
            [(1, "cakeml/pancake/semantics/panSemScript.sml",
              "set_var_def", None, (), (), (), ("locals", "globals"), False, (), False, False, ())],
        )

    def test_fmap_as_finite_support_result_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def"',
                '  (fmap_as_finite_support_result)]'
            ])),
            [(1, "cakeml/pancake/pan_to_crepScript.sml",
              "get_eids_from_decls_def", None, (), (), (), (), True, (), False, False, ())],
        )

    def test_fmap_as_finite_support_parameters_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FEVERY_res_var_FLOOKUP"',
                '  (fmap_as_finite_support_parameters := [fm, fm2])]',
            ])),
            [(1, "cakeml/pancake/semantics/panPropsScript.sml",
              "FEVERY_res_var_FLOOKUP", None, (), (), (), (), False, (), False,
              False, ("fm", "fm2"))],
        )

    def test_fmap_as_finite_support_existentials_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"',
                '  "code_inl_rel_def"',
                '  (fmap_as_finite_support_existentials := [inl_bag])]',
            ], include_fmap_existentials=True)),
            [(1, "cakeml/pancake/proofs/crep_inlineProofScript.sml",
              "code_inl_rel_def", None, (), (), (), (), False, (), False,
              False, (), ("inl_bag",))],
        )

    def test_fmap_existential_requires_explicit_exact_carrier_and_witness(self):
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat) :",
            "    (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup ∧",
            "      (Broad.ofBroad (Broad.toBroad bag)).finiteSupport = bag.finiteSupport ∧",
            "      Broad.ofBroad (Broad.toBroad bag) = bag := by",
            "  cases bag; rfl",
        ]
        declaration = "theorem eval : ∃ bag : HolFiniteMapExact Nat Nat, P bag"
        self.assertEqual(
            CHECKER["fmap_as_finite_support_existentials_errors"](
                lines, "Example.lean", declaration, "eval", ("bag",)
            ),
            [],
        )

    def test_fmap_existential_rejects_raw_map_missing_binder_and_vacuous_witness(self):
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            [], "Example.lean", "theorem eval : ∃ bag : Nat → Option Nat, P bag",
            "eval", ("bag",),
        )
        self.assertTrue(any("must be an existential typed HolFiniteMapExact" in e for e in errors))
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat) :",
            "    ¬ (mapofBroad = maptoBroadlookup ∧ bag = bag) := by",
            "  intro h; exact absurd h (by decide)",
        ]
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            lines, "Example.lean",
            "theorem eval : ∃ bag : HolFiniteMapExact Nat Nat, P bag",
            "eval", ("bag",),
        )
        self.assertTrue(any("canonical lookup/finiteSupport" in e for e in errors))

    def test_fmap_existential_rejects_witness_assumption_and_scans_definition_body(self):
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat)",
            "    (h : (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup) :",
            "    (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup ∧",
            "      (Broad.ofBroad (Broad.toBroad bag)).finiteSupport = bag.finiteSupport ∧",
            "      Broad.ofBroad (Broad.toBroad bag) = bag := by",
            "  exact ⟨h, rfl, rfl⟩",
        ]
        declaration = "def eval (bag : HolFiniteMapExact Nat Nat) : Prop :=\n  ∃ bag : HolFiniteMapExact Nat Nat, P bag"
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            lines, "Example.lean", declaration, "eval", ("bag",)
        )
        self.assertTrue(any("canonical lookup/finiteSupport" in e for e in errors))

    def test_fmap_as_finite_support_parameters_requires_direct_exact_binders_and_witnesses(self):
        lines = [
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm",
            "    (fm : HolFiniteMapExact Nat Nat) :",
            "    mapofBroad (maptoBroadlookup fm) fm.finiteSupport = fm := by",
            "  cases fm; rfl",
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm2",
            "    (fm2 : HolFiniteMapExact Nat Nat) :",
            "    mapofBroad (maptoBroadlookup fm2) fm2.finiteSupport = fm2 := by",
            "  cases fm2; rfl",
        ]
        declaration = (
            "theorem eval (fm : HolFiniteMapExact Nat Nat) "
            "(fm2 : HolFiniteMapExact Nat Nat) : Prop"
        )
        self.assertEqual(
            CHECKER["fmap_as_finite_support_parameters_errors"](
                lines, "Example.lean", declaration, "eval", ("fm", "fm2")
            ),
            [],
        )

    def test_fmap_as_finite_support_parameters_rejects_raw_or_missing_binder(self):
        errors = CHECKER["fmap_as_finite_support_parameters_errors"](
            [], "Example.lean", "theorem eval (fm : Nat → Option Nat) : Prop",
            "eval", ("fm",),
        )
        self.assertTrue(any("must be an input parameter typed HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_parameters_rejects_vacuous_witness(self):
        lines = [
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm",
            "    (fm : HolFiniteMapExact Nat Nat) :",
            "    ¬ (ofBroad = toBroad ∧ lookup = finiteSupport ∧ fm = fm) := by",
            "  intro h; exact absurd h (by decide)",
        ]
        declaration = "theorem eval (fm : HolFiniteMapExact Nat Nat) : Prop"
        errors = CHECKER["fmap_as_finite_support_parameters_errors"](
            lines, "Example.lean", declaration, "eval", ("fm",)
        )
        self.assertTrue(
            any("canonical lookup/finiteSupport" in e for e in errors)
        )

    def test_fmap_as_finite_support_relation_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"',
                '  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, CrepSemHOLState.locals])]'
            ])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "state_rel_def", None, (), (), (), (), False,
              (("PanSemStateFiniteExact", "globals"), ("CrepSemHOLState", "locals")), False, False, ())],
        )

    def test_fmap_as_finite_support_relation_accepts_two_carriers(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "structure Target where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Target :",
            "    Target.toBroad (Target.ofBroad t) = t := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines,
            (("Source", "globals"), ("Target", "locals")),
            "Example.lean",
            "def stateRel (source : Source) (target : Target) : Prop",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_relation_rejects_raw_option_map(self):
        lines = [
            "structure Source where",
            "  globals : MlS \u2192 Option (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(any("HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_relation_requires_per_carrier_witness(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(
            any("holFmapAsFiniteSupportRelationWitness_Source" in e for e in errors)
        )

    def test_fmap_as_finite_support_relation_requires_carrier_in_declaration(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (a : Type) : Prop",
        )
        self.assertTrue(any("not named in the tagged declaration" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_unknown_carrier(self):
        lines = ["def stateRel : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Nope", "globals"),), "Example.lean", "def stateRel : Prop",
        )
        self.assertTrue(any("not a structure" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_duplicate_entries(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"), ("Source", "globals")), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(any("distinct" in e for e in errors))

    def test_fmap_as_finite_support_relation_accepts_bare_parameters(self):
        lines = [
            "structure Ctxt where",
            "  vars : HolFiniteMapExact MlS (ShapeHOL \u00d7 List Nat)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Ctxt :",
            "    Ctxt.toBroad (Ctxt.ofBroad c) = c := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines,
            (("Ctxt", "vars"), ("sourceLocals", ""), ("targetLocals", "")),
            "Example.lean",
            "def localsRel (context : Ctxt) (sourceLocals : HolFiniteMapExact MlS (ValueHOL width)) (targetLocals : HolFiniteMapExact Nat (HolWordLab width)) : Prop",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_relation_rejects_raw_parameter(self):
        lines = ["def localsRel (sourceLocals : MlS \u2192 Option (ValueHOL width)) : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("sourceLocals", ""),), "Example.lean",
            "def localsRel (sourceLocals : MlS \u2192 Option (ValueHOL width)) : Prop := True",
        )
        self.assertTrue(any("sourceLocals" in e and "HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_unbound_parameter(self):
        lines = ["def localsRel (other : HolFiniteMapExact MlS (ValueHOL width)) : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("sourceLocals", ""),), "Example.lean",
            "def localsRel (other : HolFiniteMapExact MlS (ValueHOL width)) : Prop := True",
        )
        self.assertTrue(any("sourceLocals" in e for e in errors))

    def test_fmap_as_finite_support_equalities_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_tlc_rw"',
                '  (fmap_as_finite_support_equalities)]'
            ])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "slc_tlc_rw", None, (), (), (), (), False, (), True, False, ())],
        )

    def test_fmap_as_finite_support_equalities_accepts_two_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL {width : Nat} [NeZero width] :\n"
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty xs = slcHOL xs args) \u2227\n"
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty ys = tlcHOL ys args)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 (k : Nat) :",
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty xs).lookup k =",
            "      (slcHOL xs args).lookup k := rfl",
            "",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 (k : Nat) :",
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty ys).lookup k =",
            "      (tlcHOL ys args).lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_equalities_requires_both_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("conjunct 2" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_non_conjunction(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a)"
        )
        lines = [declaration + " := by rfl"]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("at least two" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_ignored_proof_witness(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (fun _ => a.lookup k) slcTlcRwHOL = b.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("ignored-proof" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_self_equality(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = a.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("self-equality" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_one_sided_lookup(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = b := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("BOTH sides" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_iff_witness(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = b.lookup k \u2194 True := Iff.rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("not an iff" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_premise_assumed_relation(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1",
            "    (h : a.lookup k = b.lookup k) : a.lookup k = b.lookup k := h",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("assumes the target relation" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_raw_option_map(self):
        declaration = "theorem slcTlcRwHOL :\n    (a = b) \u2227 (c = d)"
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            [declaration + " := by constructor <;> rfl"],
            "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("HolFiniteMapExact" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_unrelated_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    p.lookup k = q.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    r.lookup k = s.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("not associated" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_mismatched_keys(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup j := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    (HolFiniteMapExact.empty).lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("SAME key" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_inert_let_bypass(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 (k : Nat) :",
            "    (let _ := HolFiniteMapExact.empty; HolFiniteMapExact.empty.lookup k) =",
            "      (let _ := a; HolFiniteMapExact.empty.lookup k) := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(
            any("not associated" in error or "precisely" in error for error in errors)
        )

    def test_fmap_as_finite_support_equalities_rejects_fixed_key(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup 0 = a.lookup 0 := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    (HolFiniteMapExact.empty).lookup 0 = b.lookup 0 := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("universally" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_ignored_proof_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem helper : (getEidsFromDeclsHOL d).lookup k = (raw d).lookup k := rfl",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (d : DeclHOL width) (k : MlS) :",
            "    (fun _ => (getEidsFromDeclsHOL d).lookup k) helper =",
            "      (raw d).lookup k :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("directly" in error for error in errors))

    def test_fmap_as_finite_support_result_accepts_lookup_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) :=",
            "  fun _ => none",
            "",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS) :",
            "    (getEidsFromDeclsHOL decls).lookup key =",
            "      (rawDecls decls).lookup key :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_result_rejects_self_equality(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS) :",
            "    (getEidsFromDeclsHOL decls).lookup key =",
            "      (getEidsFromDeclsHOL decls).lookup key :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("self-equality" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_premise_assumed_relation(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS)",
            "    (h : (getEidsFromDeclsHOL decls).lookup key = (rawDecls decls).lookup key) :",
            "    (getEidsFromDeclsHOL decls).lookup key = (rawDecls decls).lookup key :=",
            "  h",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("assumes the target relation" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_raw_option_map(self):
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            ["def getEids : MlS → Option (BitVec width) := fun _ => none"],
            "Example.lean",
            "def getEids : MlS → Option (BitVec width)",
            "getEids",
        )
        self.assertTrue(any("HolFiniteMapExact" in error for error in errors))

    def test_fmap_as_finite_support_result_requires_canonical_witness(self):
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            ["def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none"],
            "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("witness" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_vacuous_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL : True := trivial",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(errors)

    def test_fmap_as_finite_support_result_rejects_wrong_declaration(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (x : Nat) : x = x := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("tagged declaration" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_unrelated_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (other : HolFiniteMapExact MlS (BitVec width)) : other.lookup k = other.lookup k :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("tagged declaration" in error for error in errors))

    def test_fmap_as_finite_support_accepts_canonical_carrier(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "structure Broad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : State width, ofExact (toExact s) = s) :=",
            "  fun _ => rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"), "Example.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_witness_is_carrier_agnostic(self):
        lines = [
            "structure CrepStateExact where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure CrepSemBroad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepStateExact width,",
            "      ofExact (toExact s) = s) :=",
            "  fun _ => rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Pancake/Semantics/CrepSem/StateExact.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_witness_accepts_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (ofExact (toExact (State width)) = State width) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_rejects_raw_option_map(self):
        lines = [
            "structure State where",
            "  locals : String → Option Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> State width := fun s => ofExact s",
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

    def test_fmap_as_finite_support_rejects_split_owners(self):
        lines = [
            "structure A where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure B where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    A width -> A width := fun s => ofExact s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"), "Example.lean"
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_rejects_unrelated_witness(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure Other where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    Other width -> Other width := fun s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_witness_requires_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> State width := fun s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_rejects_counterpart_without_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure Broad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> Broad width -> State width := fun s _ => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_disambiguates_shared_fields_by_carrier(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "  globals : HolFiniteMapExact (BitVec 5) (PanWordLab (ι → Bool))",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
            "@[hol \"cakeml/pancake/semantics/crepSemScript.sml\" \"foo_def\"",
            "  (fmap_as_finite_support := [locals, globals])]",
            "def helper (s : CrepSemHOLState width) := s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"),
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean",
            "def helper (s : CrepSemHOLState width) := s",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_rejects_ambiguous_shared_fields(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean"
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_rejects_carrier_naming_neither_owner(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "structure Other where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",),
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean",
            "def helper (s : Other) := s",
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_reads_type_from_tagged_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : Nat \u2192 Option Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : FiniteState) := s",
        )
        self.assertEqual(
            errors, [],
            "the type must be read from the disambiguated owning carrier, not the "
            "first structure declaring the field",
        )

    def test_fmap_as_finite_support_accepts_imported_carrier_witness(self):
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (context : PanToCrepContextExact) :",
                    "    PanToCrepContextExact.ofBroad",
                    "      (PanToCrepContextExact.toBroad context) = context := by",
                    "  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context",
                    '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                    "  (fmap_as_finite_support := [vars, funcs, eids])]",
                    "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                errors = CHECKER["fmap_as_finite_support_errors"](
                    lines, ("vars", "funcs", "eids"),
                    "Flapjack/PanToCrep/CompileExact.lean",
                    CHECKER["tagged_declaration_text"](lines, 6),
                )
                self.assertEqual(errors, [])
            finally:
                checker_globals["ROOT"] = original_root

    def test_combined_fmap_words_qualifiers_with_imported_owner(self):
        """A real imported-owner + evaluator-local witness + both qualifiers.

        Mirrors the crepSem `evaluate_def` arrangement: `CrepSemHOLState` lives
        in an imported module, the tagged declaration is in the consumer module
        with a local `holFmapAsFiniteSupportWitness`, and the tag carries both
        `(fmap_as_finite_support := [...])` and `(words_as_type_indexed_bitvec)`.
        """
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure CrepStateExact (width : Nat) where",
                    "  locals : HolFiniteMapExact Nat (HolWordLab width)",
                    "  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)",
                    "  code : HolFiniteMapExact Name Prog",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (state : CrepStateExact width) :",
                    "    CrepStateExact.ofBroad",
                    "      (CrepStateExact.toBroad state) = state := by",
                    "  exact CrepStateExact.holFmapAsFiniteSupportWitness state",
                    '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
                    "  (fmap_as_finite_support := [locals, globals, code])",
                    "  (words_as_type_indexed_bitvec)]",
                    "def evalProg {width : Nat} (state : CrepStateExact width) [NeZero width]",
                    "    (address : BitVec width) := address",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                declaration_text = CHECKER["tagged_declaration_text"](lines, 6)
                self.assertEqual(
                    CHECKER["fmap_as_finite_support_errors"](
                        lines, ("locals", "globals", "code"),
                        "Flapjack/PanToCrep/CompileExact.lean",
                        declaration_text,
                    ),
                    [],
                )
                self.assertEqual(
                    CHECKER["words_as_type_indexed_bitvec_errors"](
                        declaration_text, "evalProg",
                    ),
                    [],
                )
            finally:
                checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_local_duplicate_of_imported_owner(self):
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (context : PanToCrepContextExact) :",
                    "    PanToCrepContextExact.ofBroad",
                    "      (PanToCrepContextExact.toBroad context) = context := by",
                    "  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context",
                    '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                    "  (fmap_as_finite_support := [vars, funcs, eids])]",
                    "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                errors = CHECKER["fmap_as_finite_support_errors"](
                    lines, ("vars", "funcs", "eids"),
                    "Flapjack/PanToCrep/CompileExact.lean",
                    CHECKER["tagged_declaration_text"](lines, 11),
                )
                self.assertTrue(
                    any("one owning carrier structure" in e for e in errors),
                    errors,
                )
            finally:
                checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_imported_wrong_owner_type_and_witness(self):
        for wrong_field_type, wrong_witness in [
            ("String \u2192 Option Nat", False),
            ("HolFiniteMapExact Name Shape", True),
        ]:
            with self.subTest(wrong_field_type=wrong_field_type,
                              wrong_witness=wrong_witness):
                checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
                original_root = checker_globals["ROOT"]
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
                    consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
                    owner.parent.mkdir(parents=True)
                    owner.write_text(
                        "\n".join([
                            "structure PanToCrepContextExact where",
                            f"  vars : {wrong_field_type}",
                            "structure OtherContext where",
                            "  vars : HolFiniteMapExact Name Shape",
                        ]),
                        encoding="utf-8",
                    )
                    witness_owner = "OtherContext" if wrong_witness else "PanToCrepContextExact"
                    consumer.write_text(
                        "\n".join([
                            "import Flapjack.PanToCrep.ContextExact",
                            "theorem holFmapAsFiniteSupportWitness",
                            f"    (context : {witness_owner}) :",
                            f"    {witness_owner}.ofBroad ({witness_owner}.toBroad context) = context := by",
                            f"  exact {witness_owner}.roundtrip context",
                            '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                            "  (fmap_as_finite_support := [vars])]",
                            "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                        ]),
                        encoding="utf-8",
                    )
                    checker_globals["ROOT"] = root
                    try:
                        lines = consumer.read_text(encoding="utf-8").splitlines()
                        errors = CHECKER["fmap_as_finite_support_errors"](
                            lines, ("vars",),
                            "Flapjack/PanToCrep/CompileExact.lean",
                            CHECKER["tagged_declaration_text"](lines, 6),
                        )
                        if wrong_witness:
                            self.assertTrue(any("canonical witness" in e for e in errors))
                        else:
                            self.assertTrue(any("approved HolFiniteMapExact" in e
                                                for e in errors))
                    finally:
                        checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_num_map_sptree_field(self):
        # A HOL `sptree$num_map` field (here `Spt`) is not a `|->` finite map and
        # must not be claimed by `fmap_as_finite_support`, even though its Lean
        # field could plausibly be represented by a finite-map carrier.
        lines = [
            "structure LoopStateNumMap where",
            "  locals : Spt Nat Nat",
            "  globals : HolFiniteMapExact (BitVec 5) Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : LoopStateNumMap, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/LoopState.lean",
            "def getVarImm (s : LoopStateNumMap) := s.locals",
        )
        self.assertTrue(
            any("approved HolFiniteMapExact" in error for error in errors),
            errors,
        )

    def test_fmap_as_finite_support_rejects_raw_type_on_named_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : Nat \u2192 Option Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : BroadState) := s",
        )
        self.assertTrue(
            any(
                "owning structure `BroadState`" in error
                and "HolFiniteMapExact" in error
                for error in errors
            ),
            errors,
        )

    def test_fmap_as_finite_support_matches_owner_as_identifier_token(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact Nat Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : FiniteState) := s",
        )
        self.assertEqual(
            errors, [],
            "`State` must not match inside `FiniteState`; the owner is a whole "
            "identifier token",
        )

    def test_tagged_declaration_text_stops_before_next_declaration(self):
        lines = [
            '@[hol "cakeml/pancake/semantics/panSemScript.sml" "eval_def"',
            "  (fmap_as_finite_support := [locals])]",
            "def evalHOLFinite (s : State width) : Nat := s.clock",
            "",
            "def other : Nat := 0",
        ]
        text = CHECKER["tagged_declaration_text"](lines, 1)
        self.assertIn("State width", text)
        self.assertNotIn("other : Nat", text)

    def test_tagged_noncomputable_def_disambiguates_finite_map_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "eval_def"',
            "  (fmap_as_finite_support := [locals])]",
            "noncomputable def evalHOLFinite (s : FiniteState) : Nat := 0",
            "def unrelated (s : BroadState) : Nat := 0",
        ]
        declaration_text = CHECKER["tagged_declaration_text"](lines, 7)
        self.assertIn("FiniteState", declaration_text)
        self.assertNotIn("unrelated", declaration_text)
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Crep/HOLState.lean", declaration_text
        )
        self.assertEqual(errors, [])

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


class HolRelnTupleDeclarationsTest(unittest.TestCase):
    def fixture(self, text):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "fixtureScript.sml"
        path.write_text(text)
        return path

    def test_direct_generated_triple_and_exact_line(self):
        path = self.fixture("Theory fixture\nval (step_rules, step_ind, step_cases) = Hol_reln`\n  step x y\n`;\n")
        for name in ("step_rules", "step_ind", "step_cases"):
            self.assertEqual(DECL(path, {})[name], [2])
            self.assertIsNone(REF_ERROR(path, name, 2, {}))
            self.assertIn("not at line", REF_ERROR(path, name, 3, {}))

    def test_actual_parmove_composition_bindings(self):
        path = CHECKER["ROOT"] / "cakeml/compiler/backend/reg_alloc/parmoveScript.sml"
        for stem, line in (("step", 29), ("dstep", 478)):
            for suffix in ("_rules", "_ind", "_cases"):
                self.assertEqual(DECL(path, {})[stem + suffix], [line])
                self.assertIsNone(REF_ERROR(path, stem + suffix, line, {}))

    def test_repeated_generated_name_requires_line(self):
        binding = "val (step_rules,step_ind,step_cases) = Hol_reln`step x y`;\n"
        path = self.fixture(binding + binding)
        self.assertEqual(DECL(path, {})["step_rules"], [1, 2])
        self.assertIn("multiple lines", REF_ERROR(path, "step_rules", None, {}))
        self.assertIsNone(REF_ERROR(path, "step_rules", 2, {}))

    def test_generated_and_modern_collision_requires_line(self):
        path = self.fixture(
            "val (step_rules,step_ind,step_cases) = Hol_reln`step x y`;\n"
            "Theorem step_rules: T Proof simp[] QED\n"
        )
        self.assertEqual(DECL(path, {})["step_rules"], [1, 2])
        self.assertIn("multiple lines", REF_ERROR(path, "step_rules", None, {}))
        self.assertIsNone(REF_ERROR(path, "step_rules", 1, {}))
        self.assertIsNone(REF_ERROR(path, "step_rules", 2, {}))

    def test_arbitrary_tuple_alias_and_inconsistent_names_rejected(self):
        for rhs in ("other_generator`step x y`", "make (Hol_reln`step x y`)", "Hol_reln_alias`step x y`"):
            with self.subTest(rhs=rhs):
                path = self.fixture("val (step_rules,step_ind,step_cases) = " + rhs + ";\n")
                self.assertNotIn("step_rules", DECL(path, {}))
        path = self.fixture("val (step_rules,other_ind,step_cases) = Hol_reln`step x y`;\n")
        self.assertNotIn("step_rules", DECL(path, {}))

    def test_comment_string_quotation_and_local_binding_rejected(self):
        binding = "val (step_rules,step_ind,step_cases) = Hol_reln`step x y`;"
        texts = (
            "(* outer (* nested *)\n" + binding + "\n*)\n",
            'val text = "\n' + binding + '\n";\n',
            "val term = ``\n" + binding + "\n``;\n",
            "val term = “\n" + binding + "\n”;\n",
            "val term = ‘\n" + binding + "\n’;\n",
            "  " + binding + "\n",
        )
        for text in texts:
            with self.subTest(text=text):
                self.assertNotIn("step_rules", DECL(self.fixture(text), {}))

    def test_unterminated_quote_and_unterminated_binding_rejected(self):
        for ending in ("step x y", "step x y`"):
            path = self.fixture("val (step_rules,step_ind,step_cases) = Hol_reln`" + ending)
            self.assertNotIn("step_rules", DECL(path, {}))

    def test_unindented_nested_sml_bindings_rejected(self):
        binding = "val (step_rules,step_ind,step_cases) = Hol_reln`step x y`;\n"
        for opening, closing in (
            ("local\n", "in\nval exported = 1;\nend;\n"),
            ("val value = let\n", "in 1 end;\n"),
            ("structure Hidden = struct\n", "end;\n"),
            ("local\nlocal\n", "in end\nin end;\n"),
        ):
            with self.subTest(opening=opening):
                path = self.fixture(opening + binding + closing)
                self.assertNotIn("step_rules", DECL(path, {}))
                # Recognition resumes after the containing scope ends.
                path = self.fixture(opening + binding + closing + binding)
                self.assertEqual(len(DECL(path, {})["step_rules"]), 1)


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

    def test_datatype_name_on_its_own_line_is_indexed(self):
        path = self._write_sml(
            "Datatype:\n"
            "  shmem_info_num\n"
            "  = <| entry_pc : num\n"
            "     ; nbytes : word8 |>\n"
            "End\n"
        )
        self.assertEqual(DECL(path, {})["shmem_info_num"], [2])

    def test_lab_to_target_shmem_info_num_is_resolvable(self):
        path = (
            Path(__file__).resolve().parents[2]
            / "cakeml/compiler/backend/lab_to_targetScript.sml"
        )
        cache = {}
        self.assertIsNone(REF_ERROR(path, "shmem_info_num", None, cache))
        self.assertIsNone(REF_ERROR(path, "shmem_info_num", 350, cache))

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

    def test_one_line_datatype_header_is_indexed(self):
        path = self._write_sml(
            "Datatype: float_value = Float real | Infinity | NaN\nEnd\n\n"
            "Datatype:  float_compare = LT | EQ | GT | UN\nEnd\n"
        )
        names = DECL(path, {})
        self.assertEqual(names["float_value"], [1])
        self.assertEqual(names["float_compare"], [4])
        for constructor in ("Float", "Infinity", "NaN", "LT", "UN"):
            self.assertNotIn(constructor, names)

    def test_one_line_datatype_header_keeps_block_until_end(self):
        path = self._write_sml(
            "Datatype: ring = <| buffer : num ;\n"
            "  size : num |>\n"
            "End\n"
            "Definition after_def:\n  after = 0\nEnd\n"
        )
        names = DECL(path, {})
        self.assertEqual(names["ring"], [1])
        self.assertNotIn("buffer", names)
        self.assertNotIn("size", names)
        self.assertEqual(names["after_def"], [4])

    def test_one_line_datatype_header_rejects_near_misses(self):
        path = self._write_sml(
            "Datatypes: alpha = A\n"
            "(* Datatype: beta = B *)\n"
            "  Datatype: gamma = C\n"
            "Datatype: delta\n"
        )
        names = DECL(path, {})
        for name in ("alpha", "beta", "gamma", "delta"):
            self.assertNotIn(name, names)

    def test_binary_ieee_one_line_datatypes_are_resolvable(self):
        path = (
            Path(__file__).resolve().parents[2]
            / "HOL/src/floating-point/binary_ieeeScript.sml"
        )
        cache = {}
        self.assertIsNone(REF_ERROR(path, "float_value", None, cache))
        self.assertIsNone(REF_ERROR(path, "float_compare", None, cache))
        self.assertIn("not at line", REF_ERROR(path, "float_compare", 754, cache))

    def test_record_field_is_not_a_datatype_name(self):
        path = self._write_sml(
            "Datatype:\n  expr = Rec <| field : num |>\nEnd\n"
        )
        names = DECL(path, {})
        self.assertEqual(names["expr"], [2])
        self.assertNotIn("field", names)


class HolProgWordAliasTest(unittest.TestCase):
    SIGNATURE = "theorem example {width : Nat} [NeZero width] (p : HolProg width) : True := by trivial"
    MODULE = "Flapjack.AliasProbe"

    def fixture(self, root):
        for module in ("Flapjack.Compiler.Backend.StackLang.Prog",
                       "Flapjack.Compiler.Backend.StackLang",
                       "Flapjack.Compiler.Encoders.Asm"):
            relative = Path(module.replace(".", "/") + ".lean")
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text((CHECKER["ROOT"] / relative).read_text())
        (root / "Flapjack/AliasProbe.lean").write_text(
            "import Flapjack.Compiler.Backend.StackLang.Prog\n" + self.SIGNATURE)

    def errors(self, root, signature=None):
        signature = signature or self.SIGNATURE
        return CHECKER["words_as_type_indexed_bitvec_errors"](
            signature, "example", module=self.MODULE, root=str(root), lines=signature.splitlines())

    def test_exact_alias(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            for name in ("HolProg", "StackLang.HolProg", "Compiler.Backend.StackLang.HolProg",
                         "Flapjack.Compiler.Backend.StackLang.HolProg"):
                self.assertEqual(self.errors(root, self.SIGNATURE.replace("HolProg", name)), [])

    def test_rejects_source_drift(self):
        for old, new in (("[NeZero width]", ""),
                         ("(HolAddr width)", "(HolAddr 64)"),
                         ("HolRegImm width", "HolRegImm 0"),
                         ("HolCmp", "Nat")):
            with self.subTest(change=new), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/Compiler/Backend/StackLang/Prog.lean"
                path.write_text(path.read_text().replace(old, new))
                self.assertTrue(self.errors(root))

    def test_rejects_shadow_and_unimported_alias(self):
        for declaration in ("abbrev HolProg (width : Nat) := Nat",
                            "abbrev Evil.HolProg (width : Nat) := Nat",
                            "inductive HolInst (width : Nat) [NeZero width] where | fake"):
            with self.subTest(shadow=declaration), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/AliasProbe.lean"
                path.write_text(path.read_text() + "\n" + declaration)
                self.assertTrue(self.errors(root))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "Flapjack/AliasProbe.lean").write_text(self.SIGNATURE)
            self.assertTrue(self.errors(root))

    def test_rejects_imported_payload_alias_shadow(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "Flapjack/Shadow.lean").write_text("abbrev HolInst (width : Nat) := Nat")
            path = root / "Flapjack/AliasProbe.lean"
            path.write_text("import Flapjack.Shadow\n" + path.read_text())
            self.assertTrue(self.errors(root))

    def test_rejects_missing_or_wrong_positive_width(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            for signature in (self.SIGNATURE.replace("[NeZero width]", ""),
                              self.SIGNATURE.replace("[NeZero width]", "[NeZero other]"),
                              self.SIGNATURE.replace("HolProg width", "HolProg 0"),
                              self.SIGNATURE.replace("HolProg width", "Evil.HolProg width"),
                              self.SIGNATURE.replace("(p : HolProg width)",
                                  "(p : Evil.HolProg width) (unrelated : BitVec width)")):
                self.assertTrue(self.errors(root, signature))

    def test_rejects_payload_without_own_word_and_positive_width(self):
        for old, new in (("(value : BitVec width)", "(value : Nat)"),
                         ("inductive HolInst (width : Nat) [NeZero width]", "inductive HolInst (width : Nat)")):
            with self.subTest(change=new), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/Compiler/Encoders/Asm.lean"
                path.write_text(path.read_text().replace(old, new))
                self.assertTrue(self.errors(root))


class WordsAsTypeIndexedBitvecQualifierTest(unittest.TestCase):
    """The word-dimension / FFI-universe translation qualifier."""

    ERRORS = staticmethod(CHECKER["words_as_type_indexed_bitvec_errors"])

    PREDICATE = """def wordPredicate (width : Nat) [NeZero width] : Prop :=
  (∀ register (value : BitVec width), value.toNat = register) ∧
  (∃ (offset : BitVec width), offset.toNat = 0)
"""

    def test_accepts_explicit_internal_predicate_word_quantifiers(self):
        self.assertEqual(self.ERRORS(self.PREDICATE, "wordPredicate"), [])

    def test_internal_predicate_words_require_signature_nat_and_nezero(self):
        for old, new in [("(width : Nat)", "(width : Int)"),
                         (" [NeZero width]", ""),
                         ("[NeZero width]", "[NeZero other]")]:
            with self.subTest(mutation=old + new):
                self.assertTrue(self.ERRORS(self.PREDICATE.replace(old, new), "wordPredicate"))

    def test_internal_predicate_words_check_every_dimension(self):
        for dimension in ["0", "(0)", "other"]:
            text = self.PREDICATE.replace("(offset : BitVec width)",
                                          f"(offset : BitVec {dimension})")
            with self.subTest(dimension=dimension):
                self.assertTrue(self.ERRORS(text, "wordPredicate"))

    def test_internal_word_route_rejects_nonpredicate_and_proof_commands(self):
        for text in [self.PREDICATE.replace("def wordPredicate", "theorem wordPredicate"),
                     self.PREDICATE.replace(": Prop :=", ": Bool :="),
                     self.PREDICATE.replace(": Prop :=", ": Prop := by\n  exact")]:
            with self.subTest(text=text):
                self.assertTrue(self.ERRORS(text, "wordPredicate"))

    def test_internal_word_route_rejects_discarded_or_unquantified_carriers(self):
        for body in ["let unused : BitVec width := 0; True",
                     "let unused := (∀ (value : BitVec width), True); True",
                     "have unused : BitVec width := 0; True",
                     "True -- ∀ (value : BitVec width), True",
                     '"∀ (value : BitVec width), True" = "unrelated"',
                     "True"]:
            text = "def wordPredicate (width : Nat) [NeZero width] : Prop := " + body
            with self.subTest(body=body):
                self.assertTrue(self.ERRORS(text, "wordPredicate"))

    def test_internal_word_route_rejects_word_mentions_in_proof_binders(self):
        text = """def wordPredicate (width : Nat) [NeZero width] : Prop :=
          ∀ (proof : ∀ value : BitVec width, value = value), True"""
        self.assertTrue(self.ERRORS(text, "wordPredicate"))

    def test_internal_predicate_resolves_imported_word_carrier_and_its_width(self):
        root = Path(__file__).resolve().parents[2]
        module = "Flapjack/Compiler/Backend/WordCse/InstructionKeys.lean"
        lines = (root / module).read_text().splitlines()
        text = """def wordPredicate (width : Nat) [NeZero width] : Prop :=
          ∀ (operation : HolArith width), True"""
        self.assertEqual(self.ERRORS(text, "wordPredicate", module, str(root), lines), [])
        for mutation in [text.replace("[NeZero width]", ""),
                         text.replace("HolArith width", "HolArith other"),
                         text.replace("HolArith width", "HolArith 0"),
                         text.replace("HolArith width", "HolArith 64"),
                         text.replace("HolArith width", "HolArith (64)")]:
            with self.subTest(mutation=mutation):
                self.assertTrue(self.ERRORS(mutation, "wordPredicate", module, str(root), lines))

    def test_internal_direct_word_does_not_hide_another_carrier_width(self):
        root = Path(__file__).resolve().parents[2]
        module = "Flapjack/Compiler/Backend/WordCse/InstructionKeys.lean"
        lines = (root / module).read_text().splitlines()
        text = self.PREDICATE + " ∧ (∀ (operation : HolArith other), True)"
        self.assertTrue(self.ERRORS(text, "wordPredicate", module, str(root), lines))

    PREDICATE_USER = """theorem keep {width : Nat} [NeZero width] (data : Knowledge)
    (h : wfData width data) : wfData width data := h"""

    def predicate_user_errors(self, text, extra_lines=()):
        root = Path(__file__).resolve().parents[2]
        module = "Flapjack/Compiler/Backend/WordCse/Proofs/SemanticInvariant.lean"
        lines = (root / module).read_text().splitlines() + list(extra_lines)
        return self.ERRORS(text, "keep", module, str(root), lines)

    def test_accepts_theorem_over_reviewed_internal_word_predicate(self):
        self.assertEqual(self.predicate_user_errors(self.PREDICATE_USER), [])
        equation = """theorem keep {width : Nat} [NeZero width] :
    ∀ (rs : List Nat) (data : Knowledge), wfData width data → wfData width data
  | [], _, h => h
  | _ :: _, _, h => h"""
        self.assertEqual(self.predicate_user_errors(equation), [])

    def test_predicate_route_requires_own_positive_width(self):
        for mutation in [self.PREDICATE_USER.replace(" [NeZero width]", ""),
                         self.PREDICATE_USER.replace("[NeZero width]", "[NeZero other]"),
                         self.PREDICATE_USER.replace("{width : Nat}", "{width : Int}"),
                         self.PREDICATE_USER.replace(": wfData width data", ": wfData 64 data"),
                         self.PREDICATE_USER.replace(": wfData width data", ": wfData (0) data"),
                         self.PREDICATE_USER.replace(": wfData width data", ": wfData other data")]:
            with self.subTest(mutation=mutation):
                self.assertTrue(self.predicate_user_errors(mutation))

    def test_predicate_route_rejects_discarded_or_unapplied_uses(self):
        premise_only = """theorem keep {width : Nat} [NeZero width] (data : Knowledge)
    (h : wfData width data) : True := trivial"""
        unapplied = """theorem keep {width : Nat} [NeZero width] (data : Knowledge)
    (f : Nat → Knowledge → Prop) (e : f = wfData) : wfData width data := sorry"""
        anonymous = premise_only.replace("(h : wfData", "(_h : wfData").replace(
            ": True := trivial", ": sptLookup 0 data.toCanonical = none := sorry")
        for text in [premise_only, unapplied, anonymous]:
            with self.subTest(text=text):
                self.assertTrue(self.predicate_user_errors(text))

    def test_predicate_route_accepts_named_premise_of_nontrivial_statement(self):
        text = """theorem keep {width : Nat} [NeZero width] (data : Knowledge) (x : Nat)
    (h : wfData width data) : sptLookup x data.toCanonical = none ∨ True := sorry"""
        self.assertEqual(self.predicate_user_errors(text), [])

    def test_predicate_route_rejects_untagged_or_shadowed_predicates(self):
        fake = self.PREDICATE_USER.replace("wfData", "fakePredicate")
        self.assertTrue(self.predicate_user_errors(fake))
        shadow = ["def wfData (width : Nat) [NeZero width] (data : Knowledge) : Prop := True"]
        self.assertTrue(self.predicate_user_errors(self.PREDICATE_USER, shadow))

    GOOD = (
        "@[hol \"cakeml/pancake/semantics/crepSemScript.sml\" \"evaluate_def\" 240",
        "  (fmap_as_finite_support := [locals, globals, code])",
        "  (words_as_type_indexed_bitvec)]",
        "def evalProg {width : Nat} [NeZero width] {σ : Type}",
        "    (state : CrepSemHOLState width σ) (addr : BitVec width)",
        "    (ffi : HolFfiState σ) : HolWordLab width := HolWordLab.word addr",
        "",
    )

    def test_sites_parses_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
                '  (words_as_type_indexed_bitvec)]',
            ])),
            [(1, "cakeml/pancake/semantics/crepSemScript.sml", "evaluate_def", 240,
              (), (), (), (), False, (), False, True, ())],
        )

    def test_accepts_dimindex_and_universe(self):
        self.assertEqual(self.ERRORS("\n".join(self.GOOD), "evalProg"), [])

    def test_rejects_missing_bitvec(self):
        text = "\n".join(self.GOOD).replace("BitVec", "Word")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_missing_nezero(self):
        text = "\n".join(self.GOOD).replace("[NeZero width]", "")
        self.assertTrue(any("NeZero" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_extra_positivity_hypothesis(self):
        text = "\n".join(self.GOOD).replace(
            "(state : CrepSemHOLState width σ)",
            "(hpos : width ≠ 0) (state : CrepSemHOLState width σ)",
        )
        self.assertTrue(
            any("positivity" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_ffi_universe_level_variable(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Type u}")
        self.assertTrue(
            any("universe-level" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_empty_declaration_text(self):
        self.assertTrue(
            any("resolvable" in e for e in self.ERRORS("", "evalProg"))
        )

    def test_accepts_combined_fmap_and_words_qualifiers(self):
        self.assertEqual(self.ERRORS("\n".join(self.GOOD), "evalProg"), [])

    def test_rejects_bitvec_only_in_body(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : Nat)",
        ).replace(
            ": HolWordLab width := HolWordLab.word addr",
            ": Nat := addr + (1 : BitVec width).toNat",
        )
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_sort_host_universe(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Sort u}")
        self.assertTrue(
            any("universe" in e or "Type" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_one_le_width_hypothesis(self):
        text = "\n".join(self.GOOD).replace(
            "(state : CrepSemHOLState width σ)",
            "(hpos : 1 ≤ width) (state : CrepSemHOLState width σ)",
        )
        self.assertTrue(
            any("positivity" in e for e in self.ERRORS(text, "evalProg"))
        )


    def test_rejects_direct_bitvec_of_other_width(self):
        # `BitVec 5` next to a `Nat` width binder and an unrelated
        # `[NeZero width]` is not evidence of a `BitVec width` translation.
        text = "\n".join(self.GOOD).replace("(addr : BitVec width)", "(addr : BitVec 5)")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_direct_nezero_of_other_width(self):
        # `BitVec width` with `[NeZero other]` must not pass: positivity must be
        # discharged for the same width identifier.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero other]")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_second_unconstrained_width(self):
        # A second word dimension must also be bound at a `Nat` width with its
        # own `[NeZero <id>]` discharge.
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (other : BitVec otherWidth)",
        ).replace(
            "{width : Nat} [NeZero width] {σ : Type}",
            "{width : Nat} {otherWidth : Nat} [NeZero width] {σ : Type}",
        )
        self.assertTrue(
            any("otherWidth" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_bitvec_zero_beside_good_width(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (zero : BitVec 0)",
        )
        self.assertTrue(
            any("BitVec 0" in e or "positive" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_bitvec_zero_as_only_word(self):
        text = "\n".join(self.GOOD).replace("(addr : BitVec width)", "(addr : BitVec 0)")
        self.assertTrue(
            any("BitVec 0" in e or "BitVec" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_nezero_zero(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 0]",
        )
        self.assertTrue(
            any("NeZero 0" in e or "positive" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_standalone_nezero_zero(self):
        # `[NeZero 0]` with no surrounding width discharge must still be caught
        # by the regex scan; the zero spelling is never a valid positivity
        # instance, so it cannot license a `BitVec width` translation.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero 0]")
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_standalone_nezero_leading_zero(self):
        # A leading-zero literal (`00`) is the same nonpositive dimension as
        # `0`; the regex must not let the extra digit smuggle it through.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero 00]")
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_parenthesized_zero_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)", "(addr : BitVec width) (leak : BitVec (0))",
        )
        self.assertTrue(
            any("positive width" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_leading_zero_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)", "(addr : BitVec width) (leak : BitVec 00)",
        )
        self.assertTrue(
            any("positive width" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_arithmetic_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (leak : BitVec (width - width))",
        )
        self.assertTrue(
            any("positive width identifier" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_nezero_leading_zero(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 00]",
        )
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_literal_nezero_argument(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 5]",
        )
        self.assertTrue(
            any("NeZero 5" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_compound_nezero_argument(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero (width - width)]",
        )
        self.assertTrue(
            any("NeZero (width - width)" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_accepts_parenthesized_identifier_dimension(self):
        text = "\n".join(self.GOOD).replace("BitVec width", "BitVec (width)")
        self.assertEqual(self.ERRORS(text, "evalProg"), [])

    def test_rejects_ffi_host_at_type_one(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Type 1}")
        self.assertTrue(
            any("universe" in e or "Type" in e for e in self.ERRORS(text, "evalProg"))
        )


THEOREM_MAP = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check_hol_theorem_map.py")
)


class RealCombinedQualifierFixtureTest(unittest.TestCase):
    """End-to-end positive fixture for the combined fmap+words qualifier.

    The three exact HOL `crepSem` shared-memory ports are committed, real
    declarations carrying both `(fmap_as_finite_support := [locals, globals,
    code])` and `(words_as_type_indexed_bitvec)`. This class checks the real
    declarations through the reference checker and through the theorem-map
    manifest validator, including negatives that omit each qualifier/status.
    """

    MODULE = "Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean"
    MODULE_NAME = "Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL"
    HOL_NAMES = ("sh_mem_load_def", "sh_mem_store_def", "sh_mem_op_def")
    FMAP_FIELDS = ("locals", "globals", "code")

    def _lines(self):
        return (Path(__file__).resolve().parents[2] / self.MODULE).read_text(
            encoding="utf-8"
        ).splitlines()

    def _sites(self, lines):
        found = {}
        for site in SITES(lines):
            if site[2] in self.HOL_NAMES:
                found[site[2]] = site
        return found

    def test_real_declarations_carry_both_qualifiers(self):
        sites = self._sites(self._lines())
        for hol_name in self.HOL_NAMES:
            self.assertIn(hol_name, sites, f"{hol_name} is no longer tagged")
            site = sites[hol_name]
            self.assertEqual(tuple(site[7]), self.FMAP_FIELDS, hol_name)
            self.assertTrue(site[11], f"{hol_name} must carry (words_as_type_indexed_bitvec)")

    def test_real_declarations_pass_reference_checker(self):
        lines = self._lines()
        sites = self._sites(lines)
        self.assertEqual(set(sites), set(self.HOL_NAMES))
        for hol_name, site in sites.items():
            declaration_text = CHECKER["tagged_declaration_text"](lines, site[0])
            self.assertEqual(
                CHECKER["fmap_as_finite_support_errors"](
                    lines, self.FMAP_FIELDS, self.MODULE, declaration_text
                ),
                [],
                hol_name,
            )
            self.assertEqual(
                CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration_text, hol_name
                ),
                [],
                hol_name,
            )

    def test_real_imported_carrier_only_clauses_pass_checker(self):
        # Skip and Break are currently untagged pending whole-evaluator review;
        # neither signature names a literal `BitVec`. Both still exercise
        # resolution of the imported CrepSemHOLState word carrier.
        lines = self._lines()
        for clause, expected_tag in (("skip", False), ("break", False)):
            name = f"evalCrepSemHOLProgExact_{clause}"
            with self.subTest(clause=clause):
                start = next(
                    (index for index, line in enumerate(lines, start=1)
                     if line.startswith(f"theorem {name}")),
                    None,
                )
                self.assertIsNotNone(start, f"{name} not found")
                preceding = lines[max(0, start - 4):start - 1]
                self.assertEqual(
                    any(
                        line.lstrip().startswith("@[hol")
                        for line in preceding
                    ),
                    expected_tag,
                )
                region = []
                for line in lines[start - 1:]:
                    region.append(line)
                    if ":=" in line:
                        break
                self.assertEqual(
                    CHECKER["words_as_type_indexed_bitvec_errors"](
                        "\n".join(region),
                        name,
                        module=self.MODULE_NAME,
                        root=str(Path(__file__).resolve().parents[2]),
                        lines=lines,
                    ),
                    [],
                )

    def _tagged(self, lines):
        tagged = {}
        for hol_name, site in self._sites(lines).items():
            value = (
                site[1], site[2], site[4], site[5], site[6], site[7],
                site[8], site[9], site[10], site[11],
            )
            tagged[(self.MODULE, self._lean_name(hol_name))] = value
        return tagged

    @staticmethod
    def _lean_name(hol_name):
        return {
            "sh_mem_load_def": "crepShMemLoadExactHOL",
            "sh_mem_store_def": "crepShMemStoreExactHOL",
            "sh_mem_op_def": "crepShMemOpExactHOL",
        }[hol_name]

    def _record(self, hol_name, **overrides):
        record = {
            "hol_path": "cakeml/pancake/semantics/crepSemScript.sml",
            "hol_name": hol_name,
            "lean_path": self.MODULE,
            "lean_name": self._lean_name(hol_name),
            "statement_status": (
                "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec"
            ),
            "fmap_as_finite_support": list(self.FMAP_FIELDS),
            "words_as_type_indexed_bitvec": True,
            "reviewer": "source comparison of the HOL word/finite-map carriers",
        }
        record.update(overrides)
        return record

    def _errors(self, records, tagged):
        return THEOREM_MAP["validate_inventory"](records, set(), tagged, set())

    def test_manifest_accepts_real_combined_fixture(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        self.assertEqual(
            self._errors([self._record(h) for h in self.HOL_NAMES], tagged), []
        )

    def test_manifest_rejects_real_fixture_omitting_words_qualifier(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, words_as_type_indexed_bitvec=False) for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)

    def test_manifest_rejects_real_fixture_omitting_fmap_qualifier(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, fmap_as_finite_support=[], words_as_type_indexed_bitvec=False)
             for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)

    def test_manifest_rejects_real_fixture_with_single_status(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        for status in (
            "reviewed_fmap_as_finite_support",
            "reviewed_words_as_type_indexed_bitvec",
        ):
            errors = self._errors(
                [self._record(h, statement_status=status) for h in self.HOL_NAMES],
                tagged,
            )
            self.assertTrue(errors, status)

    def test_manifest_rejects_real_fixture_omitting_combined_status(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, statement_status="reviewed_exact") for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)


class WordsCarrierResolutionTest(unittest.TestCase):
    """Carrier resolution for `(words_as_type_indexed_bitvec)`.

    A tagged signature may omit a literal `BitVec` when it names a reviewed
    width-indexed structure or inductive carrier whose fields/constructor
    payloads include `BitVec width` and whose declaration retains
    `[NeZero width]`. The carrier is resolved from its declaration (local or
    imported), never from its name alone.
    """

    MODULE = "Flapjack/PanToCrep/CarrierExact.lean"
    MODULE_NAME = "Flapjack.PanToCrep.CarrierExact"

    def _checker_globals(self):
        return CHECKER["words_as_type_indexed_bitvec_errors"].__globals__

    def _run(self, owner_text, consumer_text):
        checker_globals = self._checker_globals()
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / self.MODULE
            owner.parent.mkdir(parents=True)
            if owner_text is not None:
                owner.write_text(owner_text, encoding="utf-8")
            consumer.write_text(consumer_text, encoding="utf-8")
            checker_globals["ROOT"] = root
            try:
                self.imported_headers = CHECKER["imported_structure_headers"](
                    self.MODULE_NAME, str(root)
                )
                self.imported_field_types = CHECKER[
                    "imported_structure_field_types"
                ](self.MODULE_NAME, str(root))
                self.imported_owners = CHECKER["imported_structure_owners"](
                    self.MODULE_NAME, str(root)
                )
                lines = consumer_text.splitlines()
                attribute_start = next(
                    (
                        index
                        for index, line in enumerate(lines)
                        if "@[hol" in line
                    ),
                    0,
                )
                declaration_text = CHECKER["tagged_declaration_text"](
                    lines, attribute_start
                )
                return CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration_text,
                    "evalProg",
                    module=self.MODULE_NAME,
                    root=str(root),
                    lines=lines,
                )
            finally:
                checker_globals["ROOT"] = original_root

    OWNER = "\n".join([
        "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
        "  locals : HolFiniteMapExact Nat (HolWordLab width)",
        "  memory : BitVec width → HolWordLab width",
        "  baseAddr : BitVec width",
    ])

    CONSUMER = "\n".join([
        "import Flapjack.PanToCrep.ContextExact",
        '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
        "  (fmap_as_finite_support := [locals])",
        "  (words_as_type_indexed_bitvec)]",
        "def evalProg {width : Nat} [NeZero width] {σ : Type}",
        "    (state : CrepStateExact width σ) : Nat := width",
    ])

    def test_accepts_imported_carrier_with_bitvec_fields(self):
        self.assertEqual(self._run(self.OWNER, self.CONSUMER), [])
        self.assertIn("CrepStateExact", self.imported_headers)
        self.assertIn("CrepStateExact", self.imported_field_types)
        self.assertIn("CrepStateExact", self.imported_owners)

    def test_accepts_local_carrier_with_bitvec_fields(self):
        local = "\n".join([
            self.OWNER,
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        self.assertEqual(self._run(None, local), [])

    def test_accepts_imported_inductive_carrier_with_bitvec_payload(self):
        owner = "\n".join([
            "inductive CrepProgExact (width : Nat) [NeZero width] where",
            "  | skip",
            "  | raise (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def unreachExact {width : Nat} [NeZero width]",
            "    (program : CrepProgExact width) : Nat := width",
        ])
        self.assertEqual(self._run(owner, consumer), [])

    def test_accepts_hol_ast_carrier_reaching_nested_bitvec_payload(self):
        owner = "\n".join([
            '@[hol "cakeml/pancake/panLangScript.sml" "decl"]',
            "inductive DeclHOL (width : Nat) [NeZero width] where",
            "  | decl (value : ExpHOL width)",
            '@[hol "cakeml/pancake/panLangScript.sml" "exp"]',
            "inductive ExpHOL (width : Nat) [NeZero width] where",
            "  | const (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def compileExact {width : Nat} [NeZero width]",
            "    (declarations : List (DeclHOL width)) : Nat := width",
        ])
        self.assertEqual(self._run(owner, consumer), [])

    def test_rejects_untagged_intermediate_ast_carrier(self):
        owner = "\n".join([
            '@[hol "cakeml/pancake/panLangScript.sml" "decl"]',
            "inductive DeclHOL (width : Nat) [NeZero width] where",
            "  | decl (value : ExpHOL width)",
            "inductive ExpHOL (width : Nat) [NeZero width] where",
            "  | const (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def compileExact {width : Nat} [NeZero width]",
            "    (declarations : List (DeclHOL width)) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    VALUE_HOL_OWNER = "\n".join([
        "inductive HolWordLab (width : Nat) [NeZero width] where",
        "  | word (value : BitVec width)",
        "inductive ValueHOL (width : Nat) [NeZero width] where",
        "  | val (value : HolWordLab width)",
        "  | rStruct (fields : List (ValueHOL width))",
        "  | nStruct (name : MlS) (fields : List (MlS × ValueHOL width))",
    ])

    VALUE_HOL_CONSUMER = "\n".join([
        "import Flapjack.PanToCrep.ContextExact",
        '@[hol "cakeml/pancake/semantics/panSemScript.sml" "flatten_def"',
        "  (words_as_type_indexed_bitvec)]",
        "def flattenExact {width : Nat} [NeZero width]",
        "    (value : ValueHOL width) : Nat := width",
    ])

    def test_accepts_value_hol_only_through_resolved_word_lab_payload(self):
        self.assertEqual(
            self._run(self.VALUE_HOL_OWNER, self.VALUE_HOL_CONSUMER), []
        )

    def test_rejects_value_hol_without_width_indexed_word_payload(self):
        owner = self.VALUE_HOL_OWNER.replace(
            "  | val (value : HolWordLab width)",
            "  | val (value : Nat)",
        )
        errors = self._run(owner, self.VALUE_HOL_CONSUMER)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    def test_rejects_value_hol_if_word_lab_payload_is_not_positive_bitvec(self):
        owner = self.VALUE_HOL_OWNER.replace(
            "inductive HolWordLab (width : Nat) [NeZero width] where",
            "inductive HolWordLab (width : Nat) where",
        )
        errors = self._run(owner, self.VALUE_HOL_CONSUMER)
        self.assertTrue(
            any("positive width" in error or "NeZero" in error for error in errors),
            errors,
        )

    def test_rejects_unrelated_aggregate_with_word_lab_field(self):
        owner = self.VALUE_HOL_OWNER.replace("ValueHOL", "OtherValue")
        consumer = self.VALUE_HOL_CONSUMER.replace("ValueHOL", "OtherValue")
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    def test_rejects_inductive_carrier_without_same_owner_word_payload(self):
        owner = "\n".join([
            "inductive CrepProgExact (width : Nat) [NeZero width] where",
            "  | skip",
            "  | clock (value : Nat)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def unreachExact {width : Nat} [NeZero width]",
            "    (program : CrepProgExact width) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)


    def test_rejects_fake_carrier_without_bitvec_field(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  clock : Nat",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_carrier_missing_positivity(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        consumer = self.CONSUMER.replace(" [NeZero width]", "")
        errors = self._run(owner, consumer)
        self.assertTrue(any("NeZero" in e for e in errors), errors)

    def test_rejects_carrier_name_not_declared(self):
        owner = "\n".join([
            "structure SomethingElse (width : Nat) [NeZero width] where",
            "  memory : BitVec width → Nat",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_carrier_width_field_without_width_variable(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  tag : BitVec 5",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_owner_header_nezero_different_width(self):
        # The owner's header discharges a DIFFERENT width identifier, so the
        # caller's own `[NeZero width]` must not substitute for carrier
        # positivity.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero other] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_field_bitvec_of_other_width(self):
        # A field mentioning `BitVec` and the width token separately (here
        # `BitVec 5 × HolWordLab width`) is not an actual `BitVec width` field.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec 5 × HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_accepts_carrier_field_via_word_abbrev(self):
        # A reviewed word abbreviation such as `RiscV.Word width` denotes the
        # standard `BitVec width` translation of HOL `'a word`, so a carrier
        # typed through the abbrev must satisfy the qualifier.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : RiscV.Word width → HolWordLab width",
            "  baseAddr : RiscV.Word width",
        ])
        self.assertEqual(self._run(owner, self.CONSUMER), [])

    def test_rejects_carrier_word_abbrev_of_other_width(self):
        # `RiscV.Word 5` is not a word field at the carrier's width identifier.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : RiscV.Word 5 → HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_ambiguous_owners_borrowing_cross_owner_evidence(self):
        # The imported owner has `[NeZero width]` but no `BitVec width` field;
        # the local same-named shadow has a `BitVec width` field but no
        # positivity. Pooling the two owners' evidence would wrongly accept the
        # tag, so the name is ambiguous and must be rejected.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  clock : Nat",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(
            any("ambiguous same-named owners" in e for e in errors), errors
        )

    def test_rejects_ambiguous_owners_without_positivity(self):
        # Both owners are same-named with `BitVec width` fields, but only the
        # local shadow retains `[NeZero width]`; no single owner supplies both
        # and the name is ambiguous.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(
            any("ambiguous same-named owners" in e for e in errors), errors
        )


class QualifiedWordsCarrierResolutionTest(unittest.TestCase):
    def _run(self, carrier="Flapjack.Source.State", *, source_positive=True,
             source_word=True, local_shadow=False):
        positive = " [NeZero width]" if source_positive else ""
        payload = "BitVec width" if source_word else "Nat"
        source = ("namespace Flapjack\nnamespace Source\nsection CarrierScope\n"
                  f"structure State (width : Nat){positive} where\n"
                  f"  word : {payload}\nend CarrierScope\nend Source\nend Flapjack\n")
        target = ("namespace Flapjack.Target\n"
                  "structure State (width : Nat) [NeZero width] where\n"
                  "  clock : Nat\nend Flapjack.Target\n")
        shadow = ("namespace Flapjack.Source\n"
                  "structure State (width : Nat) [NeZero width] where\n"
                  "  word : BitVec width\nend Flapjack.Source\n") if local_shadow else ""
        declaration = ("def checkCarrier {width : Nat} [NeZero width]\n"
                       f"    (state : {carrier} width) : Nat := width")
        consumer = ("import Flapjack.Carriers.A\nimport Flapjack.Carriers.B\n"
                    + shadow + declaration + "\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module, text in [("Flapjack/Carriers/A.lean", source),
                                 ("Flapjack/Carriers/B.lean", target),
                                 ("Flapjack/Consumer.lean", consumer)]:
                path = root / module
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            return CHECKER["words_as_type_indexed_bitvec_errors"](
                declaration, "checkCarrier", module="Flapjack.Consumer",
                root=str(root), lines=consumer.splitlines())

    def test_selects_source_namespace_not_module_filename(self):
        self.assertEqual(self._run(), [])

    def test_bare_same_named_imports_remain_ambiguous(self):
        errors = self._run("State")
        self.assertTrue(any("ambiguous same-named owners" in e for e in errors), errors)

    def test_qualified_owner_without_word_cannot_borrow_other_payload(self):
        self.assertTrue(self._run("Flapjack.Target.State"))

    def test_qualified_owner_without_positivity_cannot_borrow_other_header(self):
        self.assertTrue(self._run(source_positive=False))

    def test_qualified_owner_with_no_word_remains_ineligible(self):
        self.assertTrue(self._run(source_word=False))

    def test_same_full_name_local_shadow_remains_ambiguous(self):
        errors = self._run(local_shadow=True)
        self.assertTrue(any("ambiguous same-named owners" in e for e in errors), errors)


class RealCrepPropsWordCarrierResolutionTest(unittest.TestCase):
    """The real CrepProps imports must resolve the exact state carrier."""

    MODULE = "Flapjack/Pancake/Semantics/CrepProps.lean"
    MODULE_NAME = "Flapjack.Pancake.Semantics.CrepProps"
    HOL_NAMES = {
        "dec_clock_simp",
        "empty_locals_simp",
        "FLOOKUP_set_globals",
        "eval_upd_clock_eq",
        "update_locals_not_vars_eval_eq",
    }

    def test_real_imported_crep_state_resolves_for_five_tags(self):
        root = Path(__file__).resolve().parents[2]
        lines = (root / self.MODULE).read_text(encoding="utf-8").splitlines()
        sites = {site[2]: site for site in SITES(lines) if site[2] in self.HOL_NAMES}
        self.assertEqual(set(sites), self.HOL_NAMES)
        for hol_name, site in sites.items():
            declaration = CHECKER["tagged_declaration_text"](lines, site[0])
            self.assertEqual(
                CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration,
                    hol_name,
                    module=self.MODULE_NAME,
                    root=str(root),
                    lines=lines,
                ),
                [],
                hol_name,
            )



class FmapEqualityQualifierTest(unittest.TestCase):
    """Single finite-map equality qualifier shape checks."""

    SITES_FLAG = dict(include_fmap_as_finite_support_equality=True)

    def test_qualifier_site_flag(self):
        sites = list(SITES(
            ['@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY"',
             '  (fmap_as_finite_support_equality)]'],
            **self.SITES_FLAG,
        ))
        self.assertEqual(len(sites), 1)
        self.assertEqual(sites[0][-1], True)

    def test_accepts_single_witness(self):
        declaration = (
            "theorem resVarFEMPTYExact :\n"
            "    HolFiniteMapExact.empty = a"
        )
        lines = [
            declaration + " := by rfl",
            "",
            "theorem holFmapAsFiniteSupportEqualityWitness_resVarFEMPTYExact (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "resVarFEMPTYExact")
        self.assertEqual(errors, [])

    def test_rejects_conjunction(self):
        declaration = (
            "theorem t :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [declaration + " := by constructor <;> rfl"]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(any("exactly one" in e for e in errors), errors)

    def test_rejects_missing_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [declaration + " := by rfl"]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(
            any("has no same-module checked witness" in e for e in errors), errors)

    def test_rejects_raw_map(self):
        declaration = "theorem t :\n    (f : Nat \u2192 Option Nat) = f"
        lines = [declaration + " := by rfl"]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(any("HolFiniteMapExact" in e for e in errors), errors)

    def test_rejects_self_equality_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    a.lookup k = a.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(
            any("self-equality" in e for e in errors), errors)

    def test_rejects_fixed_key(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t :",
            "    (HolFiniteMapExact.empty).lookup 3 = a.lookup 3 := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(
            any("universally" in e for e in errors), errors)

    def test_rejects_witness_mentioning_tagged_theorem(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (fun _ => a.lookup k) t = a.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")
        self.assertTrue(
            any("ignored-proof" in e for e in errors), errors)


class FmapEqualityStrictnessTest(unittest.TestCase):
    """Singular qualifier: unconditional witness, theorem-only, data binders."""

    def _errors(self, declaration, lines):
        return CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean", declaration, "t")

    def test_rejects_arrow_premise_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    False \u2192 (HolFiniteMapExact.empty).lookup k = a.lookup k := by",
            "  intro _; rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_proof_binder_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (h : False) (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := by",
            "  cases h",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_implicit_proof_binder_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t {h : False} (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := by",
            "  cases h",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_instance_bracket_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t [h : False] (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := by",
            "  cases h",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_accepts_data_binder_witness(self):
        declaration = "theorem t :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        self.assertEqual(self._errors(declaration, lines), [])

    def test_rejects_def_tagged(self):
        declaration = "def t :\n    HolFiniteMapExact.empty = a"
        lines = [declaration + " := by rfl"]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("theorem or lemma" in e for e in errors), errors)

    def test_rejects_opaque_tagged(self):
        declaration = "opaque t :\n    HolFiniteMapExact.empty = a"
        lines = [declaration + " := by rfl"]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("theorem or lemma" in e for e in errors), errors)

    def test_rejects_tagged_arrow_premise(self):
        declaration = (
            "theorem t :\n    False \u2192 HolFiniteMapExact.empty = a"
        )
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_tagged_quantified_arrow_premise(self):
        declaration = (
            "theorem t :\n"
            "    \u2200 n, (n = n) \u2192 HolFiniteMapExact.empty = a"
        )
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_tagged_equality_binder(self):
        declaration = "theorem t (h : x = y) :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_rejects_tagged_forall_conclusion(self):
        declaration = "theorem t :\n    \u2200 n, HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(errors, errors)

    def test_rejects_tagged_proof_binder(self):
        declaration = "theorem t (h : False) :\n    HolFiniteMapExact.empty = a"
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = self._errors(declaration, lines)
        self.assertTrue(any("unconditional" in e for e in errors), errors)

    def test_accepts_tagged_data_and_typeclass_binders(self):
        declaration = (
            "theorem t {ex : Type} [DecidableEq ex] (n : ex) :\n"
            "    HolFiniteMapExact.empty = a"
        )
        lines = [
            declaration + " := by rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_t (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        self.assertEqual(self._errors(declaration, lines), [])


class HolMlBindingClassificationTest(unittest.TestCase):
    """Header declarations and ML ``val NAME =`` bindings resolve by syntax.

    The scanner accepts any ``val NAME =`` binding and does not check whether
    the value is a proof, so these tests pin the scanner's evidence only; the
    theorem-status rule is enforced by source review.
    """

    def _fixture(self, text):
        root = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: shutil.rmtree(root, ignore_errors=True))
        path = root / "FixtureScript.sml"
        path.write_text(text)
        return path, {}

    def test_theorem_valued_qprove_binding_is_a_declaration(self):
        path, cache = self._fixture(
            "val llist_shorter_lnth = Q.prove (\n"
            "  ``!ll1 ll2. T``,\n"
            "  simp[]);\n"
        )
        self.assertIsNone(REF_ERROR(path, "llist_shorter_lnth", None, cache))
        self.assertIsNone(REF_ERROR(path, "llist_shorter_lnth", 1, cache))

    def test_val_binding_does_not_register_quoted_goal_names(self):
        path, cache = self._fixture(
            "val proved_lemma = Q.prove (``!x. x = x``, simp[]);\n"
        )
        self.assertIsNone(REF_ERROR(path, "proved_lemma", None, cache))
        self.assertEqual(
            REF_ERROR(path, "goal", None, cache), "declares no `goal`"
        )

    def test_quoted_goal_term_without_binding_is_rejected(self):
        path, cache = self._fixture("val shared = build_goal goal names;\n")
        self.assertEqual(
            REF_ERROR(path, "goal", None, cache), "declares no `goal`"
        )

    def test_arbitrary_val_binding_resolves_syntactically(self):
        # Scanner evidence only: every ``val NAME =`` binds the name, whether or
        # not the value is a proof.  Theorem status is a source-review rule the
        # checker does not enforce.
        path, cache = self._fixture("val goal = ``!x. x = x``;\n")
        self.assertIsNone(REF_ERROR(path, "goal", None, cache))

    def test_header_keyword_declaration_resolves(self):
        path, cache = self._fixture("Theorem LPREFIX_TRANS:\n  T\nProof simp[] QED\n")
        self.assertIsNone(REF_ERROR(path, "LPREFIX_TRANS", None, cache))

    def test_unknown_name_rejected(self):
        path, cache = self._fixture("Theorem Known:\n  T\nProof simp[] QED\n")
        self.assertEqual(REF_ERROR(path, "Missing", None, cache), "declares no `Missing`")

    def test_wrong_source_line_rejected(self):
        path, cache = self._fixture(
            "val proved_lemma = Q.prove (``T``, simp[]);\n"
        )
        self.assertEqual(
            REF_ERROR(path, "proved_lemma", 2, cache),
            "declares `proved_lemma` at [1], not at line 2",
        )


class PinnedPathAllowlistAlignmentTest(unittest.TestCase):
    """The Lean tag elaborator and the Python checker must allow the same pins."""

    def test_lean_allowlist_matches_python_pins(self):
        import re
        holref = (CHECKER["ROOT"] / "Flapjack/HolRef.lean").read_text()
        lean_paths = set(
            re.findall(r'path == "(hol4/[^"]+\.sml)"', holref)
        )
        self.assertEqual(lean_paths, set(CHECKER["EXTERNAL_HOL_PATHS"]))

    def test_every_python_pin_is_snapshotted(self):
        for path in CHECKER["EXTERNAL_HOL_PATHS"]:
            self.assertTrue((CHECKER["ROOT"] / path).is_file(), path)



ROOT_HOL = Path(CHECKER["ROOT"]) / "HOL"
LIST_SCRIPT = "src/list/src/listScript.sml"


def _run(*args, cwd=None):
    import subprocess
    subprocess.run(list(args), cwd=cwd, check=True, capture_output=True)


@unittest.skipUnless((ROOT_HOL / ".git").exists(), "pinned HOL submodule not initialized")
class HolSubmoduleSourcesTest(unittest.TestCase):
    """``HOL/<rel>.sml`` citations need gitlink, checkout and blob provenance."""

    def fixture(self, root):
        pinned = CHECKER["HOL_SUBMODULE_COMMIT"]
        _run("git", "init", "--quiet", str(root))
        (root / ".gitmodules").write_text(
            '[submodule "HOL"]\n\tpath = HOL\n'
            "\turl = https://github.com/HOL-Theorem-Prover/HOL.git\n")
        _run("git", "clone", "--quiet", "--shared", "--no-checkout",
             str(ROOT_HOL), str(root / "HOL"))
        _run("git", "-C", str(root / "HOL"), "update-ref", "--no-deref", "HEAD", pinned)
        _run("git", "-C", str(root / "HOL"), "checkout", pinned, "--", LIST_SCRIPT)
        _run("git", "-C", str(root), "update-index", "--add", "--cacheinfo",
             f"160000,{pinned},HOL")
        return "HOL/" + LIST_SCRIPT

    def error(self, root, path):
        return CHECKER["hol_source_error"](root, path)

    def test_verified_submodule_file_is_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.fixture(root)
            self.assertIsNone(self.error(root, path))

    def test_untracked_path_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            self.assertIn("not tracked", self.error(root, "HOL/src/list/src/noSuchScript.sml"))

    def test_locally_modified_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.fixture(root)
            target = root / path
            target.write_text(target.read_text() + "\n(* local edit *)\n")
            self.assertIn("differs from the pinned blob", self.error(root, path))

    def test_wrong_superproject_gitlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.fixture(root)
            _run("git", "-C", str(root), "update-index", "--cacheinfo",
                 f"160000,{'1' * 40},HOL")
            self.assertIn("gitlink", self.error(root, path))

    def test_checkout_at_other_commit_is_rejected(self):
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.fixture(root)
            # CI initializes HOL with --depth 1, so its parent need not exist.
            # Create a distinct commit using the available pinned tree instead.
            pinned = CHECKER["HOL_SUBMODULE_COMMIT"]
            other_commit = subprocess.run(
                ["git", "-C", str(root / "HOL"),
                 "-c", "user.name=HOL provenance test",
                 "-c", "user.email=hol-provenance-test@example.invalid",
                 "commit-tree", pinned + "^{tree}", "-p", pinned,
                 "-m", "Distinct local commit for checkout rejection test"],
                check=True, capture_output=True, text=True).stdout.strip()
            self.assertNotEqual(other_commit, pinned)
            _run("git", "-C", str(root / "HOL"), "update-ref", "--no-deref", "HEAD", other_commit)
            self.assertIn("not at the pinned commit", self.error(root, path))

    def test_wrong_submodule_url_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.fixture(root)
            (root / ".gitmodules").write_text(
                '[submodule "HOL"]\n\tpath = HOL\n\turl = https://example.com/HOL.git\n')
            self.assertIn(".gitmodules", self.error(root, path))

    def test_repository_checkout_accepts_pinned_list_script(self):
        self.assertIsNone(self.error(Path(CHECKER["ROOT"]), "HOL/" + LIST_SCRIPT))

    def test_existing_hol4_snapshot_paths_unchanged(self):
        self.assertIsNone(self.error(Path(CHECKER["ROOT"]), CHECKER["EXTERNAL_HOL_PATH"]))



@unittest.skipUnless((ROOT_HOL / ".git").exists(), "pinned HOL submodule not initialized")
class HolSubmoduleDeclarationTest(unittest.TestCase):
    """Declarations cited under ``HOL/`` resolve in the verified pinned file."""

    def test_list_and_sorting_definitions_resolve(self):
        root = Path(CHECKER["ROOT"])
        cache = {}
        for rel, name in [("src/list/src/listScript.sml", "EL_def"),
                          ("src/sort/sortingScript.sml", "SORTED_DEF"),
                          ("src/sort/sortingScript.sml", "PART_DEF"),
                          ("src/sort/sortingScript.sml", "PARTITION_DEF")]:
            self.assertIsNone(CHECKER["hol_source_error"](root, "HOL/" + rel))
            self.assertIsNone(REF_ERROR(root / "HOL" / rel, name, None, cache), (rel, name))

    def test_missing_declaration_is_reported(self):
        root = Path(CHECKER["ROOT"])
        self.assertIsNotNone(
            REF_ERROR(root / "HOL/src/list/src/listScript.sml", "no_such_def", None, {}))

@unittest.skipUnless((ROOT_HOL / ".git").exists(), "pinned HOL submodule not initialized")
class MachineIeeeGeneratedDeclarationsTest(unittest.TestCase):
    """Only the reviewed fixed-format factory and unchanged generator qualify."""

    def machine_fixture(self, root):
        HolSubmoduleSourcesTest.fixture(self, root)
        for path in (CHECKER["MACHINE_IEEE_SCRIPT"], CHECKER["MACHINE_IEEE_GENERATOR"]):
            _run("git", "-C", str(root / "HOL"), "checkout",
                 CHECKER["HOL_SUBMODULE_COMMIT"], "--", path[len("HOL/"):])
        return root / CHECKER["MACHINE_IEEE_SCRIPT"]

    def test_all_reviewed_generated_names_resolve_at_literal_call(self):
        path = Path(CHECKER["ROOT"]) / CHECKER["MACHINE_IEEE_SCRIPT"]
        cache = {}
        self.assertEqual(len(CHECKER["MACHINE_IEEE_FP64_NAMES"]), 47)
        for name in CHECKER["MACHINE_IEEE_FP64_NAMES"]:
            self.assertIsNone(REF_ERROR(path, name, 16, cache), name)

    def test_binary32_prerequisites_resolve_only_at_literal_call(self):
        path = Path(CHECKER["ROOT"]) / CHECKER["MACHINE_IEEE_SCRIPT"]
        self.assertEqual(len(CHECKER["MACHINE_IEEE_FP32_NAMES"]), 3)
        for name in CHECKER["MACHINE_IEEE_FP32_NAMES"]:
            self.assertIsNone(REF_ERROR(path, name, 15, {}), name)
            for line in (None, 13, 14, 16, 17):
                self.assertIn("source line 15", REF_ERROR(path, name, line, {}))

    def test_changed_binary32_format_rejected_independently_of_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.machine_fixture(root)
            path.write_text(path.read_text().replace('("fp32", 23, 8,', '("fp32", 22, 9,'))
            self.assertIsNotNone(REF_ERROR(path, "fp32_to_float_def", 15, {}))
            fn = CHECKER["machine_ieee_fp32_source_error"]
            with patch.dict(fn.__globals__, {"hol_submodule_source_error": lambda *_: None}):
                self.assertIn("23/8/32", fn(root))

    def test_generated_names_require_call_line(self):
        path = Path(CHECKER["ROOT"]) / CHECKER["MACHINE_IEEE_SCRIPT"]
        for line in (None, 13, 15, 17, 63):
            self.assertIn("source line 16", REF_ERROR(path, "fp64_to_float_def", line, {}))

    def test_fabricated_or_other_format_names_are_not_generated(self):
        path = Path(CHECKER["ROOT"]) / CHECKER["MACHINE_IEEE_SCRIPT"]
        for name in ("fp64_fake_def", "fp32_add_def", "fp64_to_float_11"):
            self.assertIn("declares no", REF_ERROR(path, name, 16, {}))

    def test_missing_or_drifted_generator_rejected(self):
        for missing in (False, True):
            with self.subTest(missing=missing), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = self.machine_fixture(root)
                generator = root / CHECKER["MACHINE_IEEE_GENERATOR"]
                if missing:
                    generator.unlink()
                else:
                    generator.write_text(generator.read_text() + "\n(* drift *)\n")
                self.assertIn("machine_ieeeLib.sml", REF_ERROR(path, "fp64_add_def", 16, {}))
                self.assertIn("machine_ieeeLib.sml", REF_ERROR(path, "fp32_to_float_def", 15, {}))
                self.assertIsNotNone(CHECKER["hol_source_error"](
                    root, CHECKER["MACHINE_IEEE_SCRIPT"]))

    def test_changed_fixed_format_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.machine_fixture(root)
            path.write_text(path.read_text().replace('("fp64", 52, 11,', '("fp64", 51, 12,'))
            self.assertIsNotNone(REF_ERROR(path, "fp64_add_def", 16, {}))
            # Even after a provenance provider returns success, literal format
            # checking remains independent of that provider.
            fn = CHECKER["machine_ieee_fp64_source_error"]
            with patch.dict(fn.__globals__, {"hol_submodule_source_error": lambda *_: None}):
                self.assertIn("52/11/64", fn(root))






class FmapResultObservationTest(unittest.TestCase):
    def fixture(self):
        import json
        root = CHECKER["ROOT"]
        records = json.loads((root / "docs/HOL-THEOREM-MAP.json").read_text())
        return root, records

    def errors(self, signature=None, producers=("toFmap",), records=None, root=None):
        default_root, default_records = self.fixture()
        return CHECKER["fmap_result_observation_errors"](
            ["import Flapjack.Misc.BalancedMap.Semantics"], "Fixture",
            signature or "theorem observer : (toFmap cmp tree).lookup keys ≠ none → True",
            producers, default_records if records is None else records,
            default_root if root is None else root)

    def test_reviewed_real_producer(self):
        self.assertEqual([], self.errors())

    def test_unused_producer(self):
        self.assertTrue(any("unused" in e for e in self.errors("theorem observer : True")))

    def test_unreviewed_producer(self):
        self.assertTrue(any("manifest" in e for e in self.errors(records=[])))

    def test_nonmap_producer(self):
        self.assertTrue(any("return HolFiniteMapExact" in e for e in
                            self.errors("theorem observer : keySet cmp key = keys", ("keySet",))))

    def test_unqualified_and_missing_witness(self):
        root, records = self.fixture()
        source = (root / "Flapjack/Misc/BalancedMap/Semantics.lean").read_text()
        for alteration, expected in [
            (source.replace("(fmap_as_finite_support_result)", ""), "qualification"),
            (source.replace("holFmapAsFiniteSupportResultWitness_toFmap", "removedWitness"), "witness"),
        ]:
            with tempfile.TemporaryDirectory() as directory:
                temporary = Path(directory)
                path = temporary / "Flapjack/Misc/BalancedMap/Semantics.lean"
                path.parent.mkdir(parents=True)
                path.write_text(alteration)
                self.assertTrue(any(expected in e for e in self.errors(records=records, root=temporary)))

    def test_empty_duplicate_unknown_names(self):
        for names in [(), ("toFmap", "toFmap"), ("unknown",)]:
            self.assertTrue(self.errors(producers=names))

    def test_scanner_retains_producer_list(self):
        source = ['@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "to_fmap_key_set"',
                  ' (fmap_as_finite_support_result_observations := [BalancedMap.toFmap])]',
                  'theorem observer : True := by trivial']
        self.assertEqual(("BalancedMap.toFmap",), next(SITES(source, include_result_observations=True))[-1])


class FmapResultObservationShadowTest(unittest.TestCase):
    def test_observer_binder_cannot_impersonate_producer(self):
        fixture = FmapResultObservationTest()
        errors = fixture.errors("theorem observer (toFmap : Nat) : toFmap = toFmap")
        self.assertTrue(any("shadowed" in error for error in errors))


class FmapResultObservationLiteralTest(unittest.TestCase):
    def test_string_literal_does_not_establish_dependency(self):
        errors = FmapResultObservationTest().errors('theorem observer : "toFmap" = "toFmap"')
        self.assertTrue(any("unused" in error for error in errors))


class FmapResultObservationQualifiedTest(unittest.TestCase):
    def test_fully_qualified_producer(self):
        producer = "Flapjack.Misc.BalancedMap.toFmap"
        fixture = FmapResultObservationTest()
        self.assertEqual([], fixture.errors(
            f"theorem observer : ({producer} cmp tree).lookup keys ≠ none → True", (producer,)))

    def test_local_shadow_rejected(self):
        root, records = FmapResultObservationTest().fixture()
        errors = CHECKER["fmap_result_observation_errors"](
            ["import Flapjack.Misc.BalancedMap.Semantics", "def toFmap : Nat := 0"],
            "Fixture", "theorem observer : toFmap = toFmap", ("toFmap",), records, root)
        self.assertTrue(any("shadowed" in error for error in errors))


class MutualScopedProducerResolutionTest(unittest.TestCase):
    """A `mutual`/`section` bare `end` must not close the enclosing namespace."""

    def test_namespace_prefix_tracks_mutual_section_and_end(self):
        prefix = CHECKER["lean_namespace_prefix"]
        self.assertEqual("Flapjack.Foo", prefix(
            ["namespace Flapjack", "namespace Foo", "mutual", "def a := 1",
             "end", "def b := 2", "end Foo", "end Flapjack"], 6))
        self.assertEqual("Flapjack", prefix(
            ["namespace Flapjack", "section S", "theorem t : True := by trivial",
             "end", "def d := 0", "end Flapjack"], 4))
        self.assertEqual("", prefix(
            ["namespace Flapjack", "end Flapjack", "def c := 0"], 3))
        self.assertEqual("", prefix(
            ["namespace A", "mutual", "section S", "end", "end", "end A",
             "def c := 0"], 7))

    def test_qualified_producer_after_mutual_resolves(self):
        root, records = FmapResultObservationTest().fixture()
        producer = "Flapjack.crepToLoopMakeFuncsExactHOL"
        errors = CHECKER["fmap_result_observation_errors"](
            ["import Flapjack.Pancake.CrepToLoop.ContextExact"], "Fixture",
            f"theorem observer : ({producer} prog).lookup key ≠ none → True",
            (producer,), records, root)
        self.assertEqual([], errors)


class FmapResultObservationAmbiguityTest(unittest.TestCase):
    def test_unqualified_imported_shadow_rejected(self):
        root, records = FmapResultObservationTest().fixture()
        with tempfile.TemporaryDirectory() as directory:
            temporary = Path(directory)
            producer = temporary / "Flapjack/Misc/BalancedMap/Semantics.lean"
            producer.parent.mkdir(parents=True)
            producer.write_text((root / "Flapjack/Misc/BalancedMap/Semantics.lean").read_text())
            shadow = temporary / "Flapjack/Other.lean"
            shadow.write_text("namespace Other\ndef toFmap : Nat := 0\nend Other\n")
            errors = CHECKER["fmap_result_observation_errors"](
                ["import Flapjack.Misc.BalancedMap.Semantics", "import Flapjack.Other"],
                "Fixture", "theorem observer : (toFmap cmp tree).lookup keys ≠ none → True",
                ("toFmap",), records, temporary)
            self.assertTrue(any("ambiguous" in error for error in errors))


class PanSemGeneratedEvalIndTest(unittest.TestCase):
    def test_real_source_and_bounded_negative_cases(self):
        path = CHECKER["ROOT"] / CHECKER["PANSEM_EVAL_IND_PATH"]
        source = path.read_text()
        recognize = CHECKER["pansem_eval_ind_declaration"]
        line = recognize(path, source)
        self.assertIsNotNone(line)
        self.assertEqual(CHECKER["hol_declaration_lines"](path, {})["eval_ind"], [line])
        self.assertIsNotNone(REF_ERROR(path, "other_ind", None, {}))
        for changed in [source.replace("Definition eval_def:", "Definition other_def:"),
                        source.replace("Termination\n  wf_rel_tac `measure (exp_size ARB o SND)`", "Termination\n  cheat"),
                        source.replace("(eval s BytesInWord =", "(eval s TopAddr =")]:
            with self.subTest(source=changed[-100:]):
                self.assertIsNone(recognize(path, changed))
        self.assertIsNone(recognize(path.with_name("otherScript.sml"), source))
        self.assertIsNone(recognize(Path("other/pancake/semantics/panSemScript.sml"), source))
        block = source[source.index("Definition eval_def:"):]
        self.assertIsNone(recognize(path, source + "\n" + block))


class NoRetCorrectFmapRegressionTest(unittest.TestCase):
    """Protect the reviewed theorem even if tag and manifest are both weakened."""

    MODULE = "Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenHelpers.lean"

    def test_native_state_maps_have_explicit_relation_qualifier_and_witness(self):
        root = CHECKER["ROOT"]
        lines = (root / self.MODULE).read_text().splitlines()
        sites = [site for site in SITES(lines) if site[2] == "no_ret_correct"]
        self.assertEqual(len(sites), 1)
        site = sites[0]
        state_lines = (root / "Flapjack/Compiler/Backend/Semantics/StackSem/State.lean").read_text().splitlines()
        fields = CHECKER["structure_field_types"](state_lines)["StackSemStateFiniteExact"]
        required = tuple(("StackSemStateFiniteExact", field)
                         for field, typ in fields.items() if "HolFiniteMapExact" in typ)
        self.assertEqual(len(required), 3)
        self.assertEqual(site[9], required)
        signature = CHECKER["tagged_declaration_text"](lines, site[0])
        self.assertIn("∀ s : StackSemStateFiniteExact", signature)
        self.assertEqual(CHECKER["fmap_as_finite_support_relation_errors"](
            lines, required, self.MODULE, signature), [])

    def test_manifest_retains_combined_qualifier_and_inherited_assumption(self):
        import json
        root = CHECKER["ROOT"]
        records = json.loads((root / "docs/HOL-THEOREM-MAP.json").read_text())
        rows = [row for row in records if row.get("lean_path") == self.MODULE
                and row.get("lean_name") == "noRetCorrect"]
        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row["statement_status"],
                         "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec")
        self.assertEqual(row["fmap_as_finite_support_relation"],
                         ["StackSemStateFiniteExact.regs", "StackSemStateFiniteExact.fpRegs",
                          "StackSemStateFiniteExact.store"])
        self.assertTrue(row["words_as_type_indexed_bitvec"])
        self.assertTrue(row["inherits_reals_as_rational_cuts"])


class L3RiscvStepNopDeclarationsTest(unittest.TestCase):
    """`class_rd0` companions are registered narrowly for the reviewed script."""

    def test_generated_names_from_factory_bindings(self):
        source = "\n".join([
            "val arithi = class_rd0 `(rd, rs1, imm)`",
            "val ADDI  = arithi [] \"ADDI\"",
            "val ADD   = arithr [] \"ADD\"",
            "val JAL   = class_rd0 `(rd, imm)` [] \"JAL\"",
            "val load = class_rd0 `(rd, rs1, offs)`",
            "val LD    = load [[``^archbase <> 0w``, aligned_d]] \"LD\"",
            "val cbranch = class `(rs1, rs2, offs)` []",
            "val BEQ  = cbranch \"BEQ\"",
        ])
        found = dict(CHECKER["l3_riscv_step_nop_declarations"](source))
        self.assertEqual(set(found), {"ADDI_NOP", "ADD_NOP", "JAL_NOP", "LD_NOP"})
        self.assertEqual(found["ADDI_NOP"], 2)
        self.assertEqual(found["JAL_NOP"], 4)
        self.assertEqual(found["LD_NOP"], 6)

    def test_real_script_names_resolve(self):
        path = Path(CHECKER["ROOT"]) / CHECKER["L3_RISCV_STEP_SCRIPT"]
        if not path.exists():
            self.skipTest("pinned HOL submodule not initialized")
        cache = {}
        for name in ("ADD_NOP", "SUB_NOP", "AND_NOP", "OR_NOP", "XOR_NOP",
                     "ADDI_NOP", "ANDI_NOP", "ORI_NOP", "XORI_NOP",
                     "LUI_NOP", "AUIPC_NOP"):
            self.assertIsNone(REF_ERROR(path, name, None, cache), name)

    def test_unrelated_name_not_generated(self):
        found = dict(CHECKER["l3_riscv_step_nop_declarations"](
            "val BEQ = cbranch \"BEQ\"\nval SW = store [] \"SW\""))
        self.assertEqual(found, {})

    def test_generated_name_follows_instruction_string_not_binder(self):
        source = "\n".join([
            "val FAKE = arithi [] \"ADD\"",
            "val arithr = class_rd0 `(rd, rs1, rs2)`",
            "val MISPICK = arithr [] \"OR\"",
        ])
        found = dict(CHECKER["l3_riscv_step_nop_declarations"](source))
        self.assertEqual(set(found), {"ADD_NOP", "OR_NOP"})
        self.assertNotIn("FAKE_NOP", found)
        self.assertNotIn("MISPICK_NOP", found)


if __name__ == "__main__":
    unittest.main()
