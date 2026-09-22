#!/usr/bin/env python3
"""Unit tests for the HOL port candidate navigator."""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "next-hol-port.py"
SPEC = importlib.util.spec_from_file_location("next_hol_port", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PORT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PORT
SPEC.loader.exec_module(PORT)


class NextHolPortTests(unittest.TestCase):
    def test_selects_untagged_declarations_before_goal_in_source_order(self):
        with tempfile.TemporaryDirectory() as directory:
            index = Path(directory) / "hol-index.tsv"
            index.write_text(
                "# cakeml_commit\ttest\n"
                "Definition\tbase_def\tpancake/proofs/exampleScript.sml:2-5\texample\n"
                "Definition\tported_def\tpancake/proofs/exampleScript.sml:8-9\texample\n"
                "Theorem\tgoal\tpancake/proofs/exampleScript.sml:12-20\texample\n"
                "Definition\tlater_def\tpancake/proofs/exampleScript.sml:22-24\texample\n"
            )
            declarations = PORT.read_index(index)
        tagged = PORT.read_mapping(
            "Flapjack/Example.lean:4\tported\t"
            "cakeml/pancake/proofs/exampleScript.sml\tported_def\n"
        )
        found, count = PORT.candidates(
            declarations, tagged, "pancake/proofs/exampleScript.sml", "goal", {"Definition"}
        )
        self.assertEqual([entry.name for entry in found], ["base_def"])
        self.assertEqual(count, 1)

    def test_rejects_unknown_goal(self):
        declaration = PORT.Declaration("Definition", "base_def", "pancake/example.sml", 2, 4)
        with self.assertRaisesRegex(ValueError, "expected one declaration"):
            PORT.candidates([declaration], set(), "pancake/example.sml", "missing", {"Definition"})


if __name__ == "__main__":
    unittest.main()
