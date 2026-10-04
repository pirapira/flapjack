#!/usr/bin/env python3
"""Pinned full original Div case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Div.lean': '80a4bacff19e788580db8f42e8f6d02baafdd8252f3415e9caa5439d3a1caf10', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_div_probeScript.sml': '948210288d0a6a2ff384bd8f42a577999405e8fafdc9dfc79f54bdb2707404cd', 'scripts/hol-probes/riscv_target_div_probe.out': '6c1362c5fa865bab88d66be9b97254bb089b73ce599d21957942b2c74adaac0e'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Div.lean'):
            text = text.split('theorem riscv_encoder_correct_div', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Div original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_div_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Div probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_div_' + label not in registered[0]:
            raise ValueError('missing original Div evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Div constructor statement/evidence PASS')
