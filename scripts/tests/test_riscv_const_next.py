"""Mutation regressions for unrestricted native Const instruction signature/boundary evidence protection."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('const_guard', ROOT / 'scripts/hol-probes/check-riscv-const-next.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ConstGuard(unittest.TestCase):
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
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/ConstNext.lean'
            p.write_text(p.read_text().replace('(rd rs : BitVec 5)', '(run_assumption : True) (rd rs : BitVec 5)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_false_original_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/riscv_const_next_probe.out'
            p.write_text(p.read_text().replace('const_next_lui_zero=T', 'const_next_lui_zero=F'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_lost_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'scripts/hol-probes/regenerate.sh'
            p.write_text(p.read_text().replace('const_next_xor_all_ones', ''))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_narrowed_shift_domain(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/ConstNext.lean'
            p.write_text(p.read_text().replace('(shamt : BitVec 6)', '(shamt : BitVec 5)'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_wrong_fetch_byte(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/ConstNext.lean'
            p.write_text(p.read_text().replace('ms.c_PC ms.procID + 3', 'ms.c_PC ms.procID + 4'))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_wrong_next_pc(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            p = root / 'Flapjack/RiscV/CorrectnessEncoding/InstructionStep.lean'
            p.write_text(p.read_text().replace('ms.c_PC ms.procID + 4', 'ms.c_PC ms.procID + 8'))
            with self.assertRaises(ValueError):
                guard.check(root)
if __name__ == '__main__':
    unittest.main()
