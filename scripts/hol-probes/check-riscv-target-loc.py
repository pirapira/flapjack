#!/usr/bin/env python3
"""Pinned full original Loc case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Loc.lean': '9d400adc001638e15595fed631aeb0eb164d9f5da0815d13cee487ecf169ae35', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_loc_probeScript.sml': 'f8f50d0ce4c540ebe3501c484b63a021933e937cb45701b7b770a17e6bab922a', 'scripts/hol-probes/riscv_target_loc_probe.out': '61cd96ad66b8ba51922017a4b23df41a1f3263c6adf73413dbc3b38723fa9cab'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Loc.lean'):
            text = text.split('theorem riscv_encoder_correct_loc', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Loc original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_loc_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Loc probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_loc_' + label not in registered[0]:
            raise ValueError('missing original Loc evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Loc constructor statement/evidence PASS')
