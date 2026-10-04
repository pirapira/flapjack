import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('const_step_guard', ROOT / 'scripts/hol-probes/check-riscv-const-step.py')
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)
SOURCE = 'Flapjack/RiscV/CorrectnessEncoding/ConstStep.lean'

class ConstStepGuardTests(unittest.TestCase):
    def test_original(self):
        self.assertTrue(GUARD.check())

    def test_rejects_effect_and_statement_drift(self):
        source = (ROOT / SOURCE).read_text()
        mutations = [
            ('c_Skip := holUpdate ms.procID 4', 'c_Skip := holUpdate ms.procID 8'),
            ('ms.c_PC ms.procID + 4)', 'ms.c_PC ms.procID + 8)'),
            ('(index + 1) tail', '(index + 2) tail'),
            ('env index (constStep i ms)', 'env 0 (constStep i ms)'),
            ('(ok : riscvOk ms = true) (bytes', '(targetRun : False) (ok : riscvOk ms = true) (bytes'),
            ('BitVec.ofNat 64 (4 * is.length)', 'BitVec.ofNat 64 (8 * is.length)'),
            ('| .ArithR (.XOR (rd,_,_)) => rd', '| .ArithR (.XOR (rd,_,_)) => 0#5'),
        ]
        for before, after in mutations:
            with self.subTest(mutation=before), tempfile.TemporaryDirectory() as folder:
                self.assertIn(before, source)
                p = Path(folder) / SOURCE
                p.parent.mkdir(parents=True)
                p.write_text(source.replace(before, after))
                with self.assertRaises(ValueError):
                    GUARD.check(Path(folder))
