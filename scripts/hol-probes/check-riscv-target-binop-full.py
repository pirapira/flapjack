#!/usr/bin/env python3
"""Pinned full original full Binop case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Binop.lean': '939ac8ab7a1d111fc8e73a996ced01f000e2dc964ab75152bebadcf7d5c2cb3a', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_binop_full_probeScript.sml': 'e82ca3a551383291f0028b5b41c4a8e60ab4f423ab3daff69411da2b4e33b30d', 'scripts/hol-probes/riscv_target_binop_full_probe.out': 'bb4a8e4b441f65960faa63e76be656178c871adfc58bc54028dc0667f8d7a288'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Binop.lean'):
            text = text.split('theorem riscv_encoder_correct_binop', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full full Binop original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_binop_full_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('full Binop probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_binop_full_' + label not in registered[0]:
            raise ValueError('missing original full Binop evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native full Binop constructor statement/evidence PASS')
