#!/usr/bin/env python3
"""Pin complete Const native Next/effect/list transport shape.
Syntactic regression only: Lean checks proofs; original source review is separate.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
NAMES = ['next_const_step', 'const_run_frame', 'const_step_frame', 'const_step_ok', 'const_step_projection_eq', 'const_step_list_projection_eq', 'const_interleaved_step_projection', 'const_step_list_frame']
EXPECTED = '13b833e7cbf7fb62b4ad5874dc069d0657ab4f6db0830d2618fc25890d23c248'

def check(root=ROOT):
    s = (root / 'Flapjack/RiscV/CorrectnessEncoding/ConstStep.lean').read_text()
    parts = [s.split('def constDestination',1)[1].split('/--',1)[0],
             s.split('noncomputable def constStep ',1)[1].split('/--',1)[0],
             s.split('noncomputable def constStepInterleaved',1)[1].split('/--',1)[0]]
    parts += [s.split('theorem '+n,1)[1].split(' := by',1)[0] for n in NAMES]
    if hashlib.sha256(''.join(parts).encode()).hexdigest() != EXPECTED:
        raise ValueError('native Const complete step/list statement or effect drift')
    return True

if __name__ == '__main__':
    check()
    print('Native Const complete Next/effect/list original projection transport PASS')
