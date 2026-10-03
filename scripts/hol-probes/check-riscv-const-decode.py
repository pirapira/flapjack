#!/usr/bin/env python3
"""Pinned unrestricted Const instruction composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeConst.lean': '865ac96b6d1fb6a1c6a7f67b1bd6f8d5aaaca32f2f1dd798dfeefeffb9b43c75', 'scripts/hol-probes/riscv_const_decode_probeScript.sml': 'aafdf5ca54eea6035fe6676f5a73fa86713578a2546795dda9ec30eb221c9b56', 'scripts/hol-probes/riscv_const_decode_probe.out': '3be7ba7060808bb2060b670f1ed3e73a88b6971fe17a6a8fb6090bb07ed6f3ef'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('DecodeConst.lean'):
            text = '\n'.join(text.split('theorem ' + decl, 1)[1].split(' := by', 1)[0] for decl in ('decode_encode_ori', 'decode_encode_xori', 'decode_encode_slli', 'decode_encode_or', 'decode_encode_xor'))
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Const instruction original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_const_decode_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Const instruction probe must have one full registration')
    for label in ('ori_decode_zero', 'ori_decode_all_ones', 'ori_decode_sign_bit', 'ori_decode_positive_max', 'xori_decode_zero', 'xori_decode_all_ones', 'xori_decode_sign_bit', 'xori_decode_positive_max', 'slli_decode_zero', 'slli_decode_all_ones', 'slli_decode_sign_bit', 'slli_decode_positive_max', 'or_decode_zero', 'or_decode_all_ones', 'or_decode_sign_bit', 'or_decode_positive_max', 'xor_decode_zero', 'xor_decode_all_ones', 'xor_decode_sign_bit', 'xor_decode_positive_max'):
        if label not in registered[0]:
            raise ValueError('missing original Const instruction evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Const instruction full-domain statement/boundary evidence PASS')
