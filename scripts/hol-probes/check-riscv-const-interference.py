#!/usr/bin/env python3
"""Pin full native Const projection transport shape; Lean checks proofs.
Untagged infrastructure, not a full encoder/Next correctness claim.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
NAMES = ['riscv_ok_of_projection_eq', 'const_run_ok', 'const_run_projection_eq', 'const_list_projection_eq', 'const_interleaved_run_projection']
EXPECTED = 'e915dc1153c12a2ee8e239fc312cdfe3998faaececaa74304644464652cbc706'

def check(root=ROOT):
    s = (root / 'Flapjack/RiscV/CorrectnessEncoding/ConstInterference.lean').read_text()
    parts = [s.split('inductive ConstRegisterInstruction', 1)[1].split('/--', 1)[0]]
    parts += [s.split('theorem ' + n, 1)[1].split(' := by', 1)[0] for n in NAMES]
    parts += [s.split('noncomputable def constRunInterleaved', 1)[1].split('/--', 1)[0]]
    if hashlib.sha256(''.join(parts).encode()).hexdigest() != EXPECTED:
        raise ValueError('native Const unrestricted projection/interference statement drift')
    return True

if __name__ == '__main__':
    check()
    print('Native Const full-family original projection/interference shape PASS')
