#!/usr/bin/env python3
"""Pinned unrestricted Binop instruction composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeBinop.lean': '18639b182b8d85e4f59964acef1c389b313842dfe7a90f5ece91d87088b43ba7', 'scripts/hol-probes/riscv_binop_decode_probeScript.sml': 'a8c5442f7a404f78d6e8edd8f0370912bc4b4aa10455e57b76f85bf953b5ccb9', 'scripts/hol-probes/riscv_binop_decode_probe.out': '23d00fd6ff06f1a963d4c97fa6b66d421fe0b42d699c157e9357ca55ea917fbe'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('DecodeBinop.lean'):
            text = '\n'.join(text.split('theorem ' + decl, 1)[1].split(' := by', 1)[0] for decl in ('decode_encode_andi', 'decode_encode_add', 'decode_encode_sub', 'decode_encode_and'))
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Binop instruction original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_binop_decode_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Binop instruction probe must have one full registration')
    for label in ('andi_decode_zero', 'andi_decode_all_ones', 'andi_decode_sign_bit', 'andi_decode_positive_max', 'add_decode_zero', 'add_decode_all_ones', 'add_decode_sign_bit', 'add_decode_positive_max', 'sub_decode_zero', 'sub_decode_all_ones', 'sub_decode_sign_bit', 'sub_decode_positive_max', 'and_decode_zero', 'and_decode_all_ones', 'and_decode_sign_bit', 'and_decode_positive_max', 'andi_encode_source_clause', 'andi_encode_source_hypotheses', 'andi_carrier_types', 'andi_symbolic_replay_query', 'add_encode_source_clause', 'add_encode_source_hypotheses', 'add_carrier_types', 'add_symbolic_replay_query', 'sub_encode_source_clause', 'sub_encode_source_hypotheses', 'sub_carrier_types', 'sub_symbolic_replay_query', 'and_encode_source_clause', 'and_encode_source_hypotheses', 'and_carrier_types', 'and_symbolic_replay_query'):
        if label not in registered[0]:
            raise ValueError('missing original Binop instruction evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Binop instruction full-domain statement/boundary evidence PASS')
