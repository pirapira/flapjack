#!/usr/bin/env python3
"""Unit tests for the HOL dependency inventory and its index parser.

These run without the generated ``.hol-index/`` directory: the parser is
exercised on temporary SML sources and a temporary dependency graph so that a
regression in attribute stripping, section termination, or graph sanitisation
fails here first.
"""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


TESTS_DIR = Path(__file__).resolve().parent
SCRIPTS = TESTS_DIR.parent


def _load(module_name: str, filename: str):
    spec = importlib.util.spec_from_file_location(module_name, SCRIPTS / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


INDEX_HOL = _load("index_hol", "index-hol.py")
INVENTORY = _load("hol_dependency_inventory", "hol-dependency-inventory.py")


def _write_script(root: Path, name: str, body: str) -> Path:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


class AncestorsParserTests(unittest.TestCase):
    def test_strips_attributes_and_stops_at_section_keyword(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  integer[qualified] words[qualified] string[qualified]\n"
                "  location[qualified]\n"
                "\n"
                "(* a comment line *)\n"
                "Datatype:\n"
                "  t = A | B\n"
                "End\n"
                "val _ = x + 1;\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(
            dependencies,
            [
                ("example", "integer"),
                ("example", "words"),
                ("example", "string"),
                ("example", "location"),
            ],
        )

    def test_stops_at_unindented_line_without_section_keyword(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  alpha beta\n"
                "\n"
                "open Gamma\n"
                "val _ = alpha beta;\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(dependencies, [("example", "alpha"), ("example", "beta")])

    def test_drops_non_identifier_tokens_from_body_scan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = _write_script(
                root,
                "exampleScript.sml",
                "Theory example\n"
                "Ancestors\n"
                "  alpha\n"
                "  (\n"
                "  SOME(SOME, st.facts);\n",
            )
            _, dependencies, _ = INDEX_HOL.parse_file(root, path)
        self.assertEqual(dependencies, [("example", "alpha")])


class TheoryGraphTests(unittest.TestCase):
    def test_rejects_non_identifier_nodes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "theory-deps.txt"
            path.write_text("good -> fine\nbroken -> :\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                INVENTORY.load_theory_graph(path)

    def test_closure_is_transitive_and_cycle_safe(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "theory-deps.txt"
            path.write_text(
                "a -> b\na -> c\nb -> d\nc -> d\nd -> a\ne -> f\n",
                encoding="utf-8",
            )
            graph = INVENTORY.load_theory_graph(path)
        self.assertEqual(
            sorted(INVENTORY.theory_closure(graph, ["a"])), ["a", "b", "c", "d"]
        )
        self.assertEqual(sorted(INVENTORY.theory_closure(graph, ["e"])), ["e", "f"])


class CommittedReportTests(unittest.TestCase):
    REPORT = INVENTORY.ROOT / "docs" / "HOL-DEPENDENCY-INVENTORY.md"

    def test_report_is_validated(self):
        text = self.REPORT.read_text(encoding="utf-8")
        self.assertIn("## Validation", text)
        self.assertNotIn("**UNVALIDATED**", text)
        self.assertIn("All count invariants hold", text)


if __name__ == "__main__":
    unittest.main()