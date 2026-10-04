"""Mutation regressions for unrestricted native Binop instruction signature/boundary evidence protection."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('binop_guard', ROOT / 'scripts/hol-probes/check-riscv-binop-run.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class BinopGuard(unittest.TestCase):
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
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/BinopRun.lean'
            p.write_text(p.read_text().replace('(ms : riscv_state)', '(run_assumption : True) (ms : riscv_state)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_false_original_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_binop_run_probe.out'
            p.write_text(p.read_text().replace('native_add_hypotheses=0', 'native_add_hypotheses=1'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_lost_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('native_sub_types', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
