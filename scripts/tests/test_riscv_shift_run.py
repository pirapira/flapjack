"""Mutation regressions for complete original Shift source/runtime evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('shift_guard', ROOT / 'scripts/hol-probes/check-riscv-shift-run.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ShiftRunGuard(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        for name in list(guard.CHECKS) + ['scripts/hol-probes/regenerate.sh']:
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text((ROOT / name).read_text())
        return root
    def test_complete_original(self):
        self.assertTrue(guard.check())
    def test_narrowed_amount_domain(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/ShiftRun.lean'
            p.write_text(p.read_text().replace('(amount : BitVec 6)', '(amount : BitVec 5)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_changed_original_hypotheses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_shift_run_probe.out'
            p.write_text(p.read_text().replace('source_shift_hypotheses=0', 'source_shift_hypotheses=1'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_missing_type_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('run_srai_types', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
