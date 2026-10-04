"""Regression mutations for full original register comparison guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("register_comparison_guard", ROOT / "scripts/hol-probes/check-l3-step-register-comparison.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class RegisterComparisonGuard(unittest.TestCase):
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

    def test_original_architecture_guard_retained(self):
        self.mutate(guard.LEAN, "(arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2)", "(arch : (s.c_MCSR s.procID).mcpuid.ArchBase = 2#2)", after_marker="theorem dfnSlt ")

    def test_signed_low32_conversion(self):
        self.mutate(guard.LEAN, ").signExtend 64", ").setWidth 64", after_marker="theorem dfnSlt ")

    def test_unsigned_low32_conversion(self):
        self.mutate(guard.LEAN, ").setWidth 64", ").signExtend 64", after_marker="theorem dfnSltU ")

    def test_second_zero_source_read(self):
        self.mutate(guard.LEAN, "if rs2 = 0#5 then 0#64", "if false then 0#64")

    def test_source_bank_not_updated_before_read(self):
        self.mutate(guard.LEAN, "s.c_gpr s.procID rs1", "s.c_gpr s.procID rd", after_marker="theorem dfnSlt ")

    def test_companion_architecture_guard_retained(self):
        self.mutate(guard.LEAN, "(arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2)", "", after_marker="theorem dfnSltUNop ")

    def test_original_two_hypotheses_captured(self):
        self.mutate("scripts/hol-probes/l3_step_register_comparison_probe.out", "slt_hypothesis_count=2", "slt_hypothesis_count=1")

    def test_companion_evidence_registered(self):
        self.mutate("scripts/hol-probes/regenerate.sh", "sltu_nop_hypotheses", "")

if __name__ == "__main__":
    unittest.main()
