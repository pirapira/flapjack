#!/usr/bin/env python3
"""Pinned unrestricted whole Const Run composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ConstRun.lean': 'a156be848e2f2d0b6586714b3630718c3b46e30f7f3e485ae04d4a41a28d6533', 'scripts/hol-probes/riscv_const_run_probeScript.sml': '91f955a42309683805ab5524086c9104496ec85ce0321de84980fb916c712c1a', 'scripts/hol-probes/riscv_const_run_probe.out': 'd3d15bc4bd24057561c00de5830e94832a6344535c3d09069792b6b112eef229'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ConstRun.lean'):
            text = text.split('def constRunPost', 1)[1].split('/-- Flapjack infrastructure', 1)[0] + text.split('theorem run_const', 1)[1].split(' := by', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full whole Const Run original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_const_run_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('whole Const Run probe must have one full registration')
    for label in ('const_run_small_zero', 'const_run_small_positive', 'const_run_small_negative', 'const_run_small_all_ones', 'const_run_medium_positive', 'const_run_medium_positive_max', 'const_run_medium_negative', 'const_run_medium_negative_low11', 'const_run_wide_or', 'const_run_wide_or_high11', 'const_run_wide_xor', 'const_run_wide_xor_low11_high11'):
        if label not in registered[0]:
            raise ValueError('missing original whole Const Run evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native whole Const Run full-domain statement/boundary evidence PASS')
