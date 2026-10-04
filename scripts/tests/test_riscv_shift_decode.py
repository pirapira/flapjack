"""Mutation regressions for unrestricted original native Shift decode evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('shift_guard', ROOT / 'scripts/hol-probes/check-riscv-shift-decode.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ShiftDecodeGuard(unittest.TestCase):
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
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/DecodeShift.lean'
            p.write_text(p.read_text().replace('(imm : BitVec 6)', '(imm : BitVec 5)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_false_original_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_shift_decode_probe.out'
            p.write_text(p.read_text().replace('srai_decode_high_bit=T', 'srai_decode_high_bit=F'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_missing_type_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('srai_carrier_types', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
