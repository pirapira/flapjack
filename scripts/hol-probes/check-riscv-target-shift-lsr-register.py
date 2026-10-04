#!/usr/bin/env python3
"""Pinned full original ShiftLsrRegister case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftLsrRegister.lean': '28853f88c7791509f254a40dc54acae26cd8ef1c58d7c5e0e2f695d2202ce951', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_lsr_register_probeScript.sml': '0dd2672d3f605d756ec9943c5e13f3c55581f49cc2d9de12990171ffe6e54244', 'scripts/hol-probes/riscv_target_shift_lsr_register_probe.out': '5d9e57be9e6103fb3ca98fe5a38e3a0c7fece2755dd69df874bb7246a8286e7c'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftLsrRegister.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftLsrRegister', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftLsrRegister original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_lsr_register_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftLsrRegister probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftLsrRegister_' + label not in registered[0]:
            raise ValueError('missing original ShiftLsrRegister evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftLsrRegister constructor statement/evidence PASS')
