#!/usr/bin/env python3
"""Pinned full original Const case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ConstAssertions.lean': '6927e75a79406d9d22d37418683ce12d868b19e63a7903091cbb11ca3eb50c67', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_const_probeScript.sml': 'ad6c3261f937a294bb11254e7d4beaeec453805b728794297556c4f2ec3ed95c', 'scripts/hol-probes/riscv_target_const_probe.out': '72cc5c7908d0a86b45b14fe52546149b8313c3ac3192818c59780f7f43abde71'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ConstAssertions.lean'):
            text = text.split('theorem riscv_encoder_correct_const', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Const original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_const_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Const probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_const_' + label not in registered[0]:
            raise ValueError('missing original Const evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Const constructor statement/evidence PASS')
