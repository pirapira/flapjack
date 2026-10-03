#!/usr/bin/env python3
"""Pinned unrestricted Const32 value composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Const32.lean': 'a9a43a7853dbb007b1a85c2989f7648aee3f77ba43c12bdb5042899139f43cc4', 'scripts/hol-probes/riscv_const32_value_probeScript.sml': '4a673cde8d99b6380b8ba0edce93991085bb384e41a42ae680cc5f320333dc8f', 'scripts/hol-probes/riscv_const32_value_probe.out': '2cfc2ae53e517fab43e948e33d0ee751fef489649cad104a83c2ae7eba533238'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Const32.lean'):
            text = '\n'.join(text.split('theorem ' + decl, 1)[1].split(' := by', 1)[0] for decl in ('const32_value_reconstruction', 'run_const32'))
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Const32 value original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_const32_value_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Const32 value probe must have one full registration')
    for label in ('const32_value_zero', 'const32_value_low_positive_max', 'const32_value_low_sign_bit', 'const32_value_low_all_ones', 'const32_value_high_one', 'const32_value_positive_sign_boundary', 'const32_value_positive_max', 'const32_value_negative_min', 'const32_value_negative_min_low_sign', 'const32_value_negative_low_positive', 'const32_value_negative_low_sign', 'const32_value_all_ones'):
        if label not in registered[0]:
            raise ValueError('missing original Const32 value evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Const32 value full-domain statement/boundary evidence PASS')
