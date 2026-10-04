"""Regression mutations for full original jump guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("jump_guard", ROOT / "scripts/hol-probes/check-l3-step-jump.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class JumpGuard(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        for name in [guard.LEAN, *guard.CHECKS, "scripts/hol-probes/regenerate.sh"]:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        return root

    def mutate(self, name, before, after, after_marker=None):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            path = root / name
            text = path.read_text()
            self.assertIn(before, text)
            if after_marker is None:
                path.write_text(text.replace(before, after, 1))
            else:
                prefix, rest = text.split(after_marker, 1)
                self.assertIn(before, rest)
                path.write_text(prefix + after_marker + rest.replace(before, after, 1))
            with self.assertRaises(ValueError):
                guard.check(root)

    def test_complete_original(self):
        self.assertTrue(guard.check())

    def test_no_added_alignment_premise(self):
        self.mutate(guard.LEAN, "(h : rd ≠ 0)", "(alignment : s.c_PC s.procID = 0) (h : rd ≠ 0)")

    def test_link_uses_original_pc_and_skip(self):
        self.mutate(guard.LEAN, "s.c_PC s.procID + Skip s", "s.c_PC s.procID")

    def test_exception_is_preserved(self):
        self.mutate(guard.LEAN, "signalAddressException (.Fetch_Misaligned, v) s", "s")

    def test_companion_keeps_next_fetch_effect(self):
        self.mutate(guard.LEAN, "c_NextFetch := if v.getLsbD 0", "c_NextFetch := if false", after_marker="theorem dfnJalNop ")

    def test_jalr_zero_source_read_is_preserved(self):
        self.mutate(guard.LEAN, "if rs1 = 0 then", "if false then")

    def test_hypothesis_capture_not_fabricated(self):
        self.mutate("scripts/hol-probes/l3_step_jump_probe.out", "jal_hypothesis_count=1", "jal_hypothesis_count=0")

    def test_all_companion_capture_rows_registered(self):
        self.mutate("scripts/hol-probes/regenerate.sh", "jalr_nop_hypotheses", "")

if __name__ == "__main__":
    unittest.main()
