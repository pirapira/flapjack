#!/usr/bin/env python3
"""Pinned full original Binop Reg case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/BinopRegister.lean': '622c814a35ca95c2d8ecb5b34e09061f690c686de0ebeb2e20ef4c96f3b4c462', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_binop_register_probeScript.sml': '51a625edb04c57cece37c82733d51162d638cbf9e1ac9c0b35aa101525bfca78', 'scripts/hol-probes/riscv_target_binop_register_probe.out': 'a51fe52ff7e490922d0779acbdb92e3b2704d1209e4b40560e3d169a91241aeb'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('BinopRegister.lean'):
            text = text.split('theorem riscv_encoder_correct_binopRegister', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Binop Reg original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_binop_register_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Binop Reg probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_binop_register_' + label not in registered[0]:
            raise ValueError('missing original Binop Reg evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Binop Reg constructor statement/evidence PASS')
