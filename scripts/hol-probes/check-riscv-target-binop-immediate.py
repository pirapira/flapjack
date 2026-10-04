#!/usr/bin/env python3
"""Pinned full original Binop Imm case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/BinopImmediate.lean': '3c787dffd4e79020cc510826a7c3dd4b43da8e06c3e4feb83fee3cf830386f16', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_binop_immediate_probeScript.sml': '87bb873fb95a678a253e23aa45c5a73703d14b88c632df53a770658d2ea424ce', 'scripts/hol-probes/riscv_target_binop_immediate_probe.out': '1c043e17be14d61c7641de4f5b79142caf27bcbaffc5039fb97864886ee5dd5a'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('BinopImmediate.lean'):
            text = text.split('theorem riscv_encoder_correct_binopImmediate', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Binop Imm original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_binop_immediate_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Binop Imm probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_binop_immediate_' + label not in registered[0]:
            raise ValueError('missing original Binop Imm evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Binop Imm constructor statement/evidence PASS')
