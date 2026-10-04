#!/usr/bin/env python3
"""Pinned full original ShiftAsrRegister case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftAsrRegister.lean': '530dc0647c1a12b39615cec1b9acfe26425c6ddcc48af5f4eaeca2886c088eae', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_asr_register_probeScript.sml': '0b9e76a704ea0ea814d28edce6c3258268ee3efe95206f70c92fdd22592c8180', 'scripts/hol-probes/riscv_target_shift_asr_register_probe.out': '47ee8cfa15cdddb55691431adbcd30ec893dc012beb1f83e993fc9f2fbb6aaa6'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftAsrRegister.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftAsrRegister', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftAsrRegister original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_asr_register_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftAsrRegister probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftAsrRegister_' + label not in registered[0]:
            raise ValueError('missing original ShiftAsrRegister evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftAsrRegister constructor statement/evidence PASS')
