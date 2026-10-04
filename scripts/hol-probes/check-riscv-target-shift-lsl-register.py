#!/usr/bin/env python3
"""Pinned full original ShiftLslRegister case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftLslRegister.lean': '819291c37d886305a4a0d106ebacaf6b5c26f6477fe7e5a7c8789ddb6b27ae4b', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_lsl_register_probeScript.sml': 'e4dd91200375f026e1ae50d8b19b3789f9db88afe5d22d3dba06764dabea7e76', 'scripts/hol-probes/riscv_target_shift_lsl_register_probe.out': 'a9f5b87e67b47cb871136cf0dca0d984cb63b264ff4d667020137eb101555c97'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftLslRegister.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftLslRegister', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftLslRegister original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_lsl_register_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftLslRegister probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftLslRegister_' + label not in registered[0]:
            raise ValueError('missing original ShiftLslRegister evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftLslRegister constructor statement/evidence PASS')
