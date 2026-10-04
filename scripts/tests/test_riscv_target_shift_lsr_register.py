"""Mutation regressions for full original native Lsr register statement evidence protection."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('const_guard', ROOT / 'scripts/hol-probes/check-riscv-target-shift-lsr-register.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ShiftLsrRegisterGuard(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        for name in list(guard.CHECKS) + ['scripts/hol-probes/regenerate.sh']:
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text((ROOT / name).read_text())
        return root
    def test_complete_original(self):
        self.assertTrue(guard.check())
    def test_extra_target_run_premise(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/ShiftLsrRegister.lean'
            p.write_text(p.read_text().replace('(rd rs1 rs2 : Nat)', '(run_assumption : True) (rd rs1 rs2 : Nat)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_false_original_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_target_shift_lsr_register_probe.out'
            p.write_text(p.read_text().replace('riscv_encoder_correct_shiftLsrRegister_hypotheses=0', 'riscv_encoder_correct_shiftLsrRegister_hypotheses=1'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_lost_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('riscv_encoder_correct_shiftLsrRegister_types', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
