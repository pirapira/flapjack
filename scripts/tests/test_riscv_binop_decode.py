"""Mutation regressions for unrestricted native Binop instruction signature/boundary evidence protection."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('binop_guard', ROOT / 'scripts/hol-probes/check-riscv-binop-decode.py')
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
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/DecodeBinop.lean'
            p.write_text(p.read_text().replace('(imm : BitVec 12)', '(run_assumption : True) (imm : BitVec 12)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_false_original_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_binop_decode_probe.out'
            p.write_text(p.read_text().replace('andi_decode_zero=T', 'andi_decode_zero=F'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_lost_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('sub_decode_sign_bit', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
