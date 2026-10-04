import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('const_execution_guard', ROOT / 'scripts/hol-probes/check-riscv-const-execution.py')
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)
SOURCE = 'Flapjack/RiscV/CorrectnessEncoding/ConstExecution.lean'

class ConstExecutionGuardTests(unittest.TestCase):
    def test_original(self):
        self.assertTrue(GUARD.check())

    def test_rejects_execution_and_original_premise_drift(self):
        source = (ROOT / SOURCE).read_text()
        mutations = [
            ('env index (riscvTarget.next ms)', 'env index (constStep (0#5) ms)'),
            ('(index + 1) tail', '(index + 2) tail'),
            ('(ok : riscvOk ms = true)', '(targetRun : False) (ok : riscvOk ms = true)'),
            ('(is.flatMap riscvEncode) ms.MEM8 d)', '(is.flatMap riscvEncode) ms.MEM8 (fun _ => True))'),
            ('BitVec.ofNat 64 (4 * is.length)', 'BitVec.ofNat 64 (8 * is.length)'),
            ('index + is.length - k', 'index + is.length + k'),
            ('¬ d a → before.MEM8 a = after.MEM8 a', 'd a → before.MEM8 a = after.MEM8 a'),
        ]
        for before, after in mutations:
            with self.subTest(mutation=before), tempfile.TemporaryDirectory() as folder:
                self.assertIn(before, source)
                p = Path(folder) / SOURCE
                p.parent.mkdir(parents=True)
                p.write_text(source.replace(before, after))
                with self.assertRaises(ValueError):
                    GUARD.check(Path(folder))
