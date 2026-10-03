#!/usr/bin/env python3
"""Pinned unrestricted ADDI composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeAddi.lean': '1479ec298009eba758079d02a0ddc521a3177268c174f59b099b013e7f5afa99', 'scripts/hol-probes/riscv_addi_decode_probeScript.sml': 'c79e02ebc0bd72f07b06e013b3cf23baab571083ef3d0c220ce73130616e1d4c', 'scripts/hol-probes/riscv_addi_decode_probe.out': '8c979e259abedf2de19f1d7f93869163fc86b0423fb02b4aad80dde4cdffea69'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('DecodeAddi.lean'):
            text = text.split('theorem decode_encode_addi', 1)[1].split(' := by', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ADDI original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_addi_decode_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ADDI probe must have one full registration')
    for label in ('zero', 'all_ones', 'sign_bit', 'positive_max'):
        if 'addi_decode_' + label not in registered[0]:
            raise ValueError('missing original ADDI evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ADDI full-domain statement/boundary evidence PASS')
