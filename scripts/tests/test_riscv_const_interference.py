import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('const_interference_guard', ROOT / 'scripts/hol-probes/check-riscv-const-interference.py')
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)
SOURCE = 'Flapjack/RiscV/CorrectnessEncoding/ConstInterference.lean'

class ConstInterferenceGuardTests(unittest.TestCase):
    def test_original(self):
        self.assertTrue(GUARD.check())

    def test_rejects_narrowing_and_iteration_drift(self):
        source = (ROOT / SOURCE).read_text()
        mutations = [
            ('shamt : BitVec 6', 'shamt : BitVec 5'),
            ('| xor (rd rs rt : BitVec 5)', '| xor (rd rs rt : BitVec 4)'),
            ('(index + 1) tail', '(index + 2) tail'),
            ('(ok : riscvOk ms = true) (interference', '(targetRun : False) (ok : riscvOk ms = true) (interference'),
            ('env index (Run i ms)', 'env 0 (Run i ms)'),
        ]
        for before, after in mutations:
            with self.subTest(mutation=before), tempfile.TemporaryDirectory() as folder:
                self.assertIn(before, source)
                p = Path(folder) / SOURCE
                p.parent.mkdir(parents=True)
                p.write_text(source.replace(before, after))
                with self.assertRaises(ValueError):
                    GUARD.check(Path(folder))
