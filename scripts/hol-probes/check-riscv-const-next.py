#!/usr/bin/env python3
"""Pinned unrestricted native Const Next composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ConstNext.lean': '938076e2f3ba7042ea63f43665c684357bb1dc866d19e142c601a289344ac9db', 'Flapjack/RiscV/CorrectnessEncoding/InstructionStep.lean': 'b588c9686bc3fdd8f983bf6cfcc5c7f69d9321fd3c2bdc62aa12695d1c4ae837', 'scripts/hol-probes/riscv_const_next_probeScript.sml': 'dd94eb741a8a56136a788d6dc65a59dd39e1963f87756e2f0efda36e37936425', 'scripts/hol-probes/riscv_const_next_probe.out': 'ade42c6fb84b72c53ba06fa2368cd8189115c18ff5df0b4ca31783a3763e9f57'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ConstNext.lean'):
            text = text.split('def encodedInstructionBytes', 1)[1].split('/-- Native', 1)[0] + '\n'.join(text.split('theorem ' + d, 1)[1].split(' := by', 1)[0] for d in ('next_encoded_lui', 'next_encoded_addi', 'next_encoded_ori', 'next_encoded_xori', 'next_encoded_slli', 'next_encoded_or', 'next_encoded_xor'))
        elif name.endswith('InstructionStep.lean'):
            text = text.split('def writePost', 1)[1].split('theorem aligned_add_four', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full native Const Next original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_const_next_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('native Const Next probe must have one full registration')
    for label in ('const_next_wrapper_type', 'const_next_fetch_type', 'const_next_lui_zero', 'const_next_lui_all_ones', 'const_next_addi_zero', 'const_next_addi_all_ones', 'const_next_ori_zero', 'const_next_ori_all_ones', 'const_next_xori_zero', 'const_next_xori_all_ones', 'const_next_slli_zero', 'const_next_slli_all_ones', 'const_next_or_zero', 'const_next_or_all_ones', 'const_next_xor_zero', 'const_next_xor_all_ones'):
        if label not in registered[0]:
            raise ValueError('missing original native Const Next evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native Const instruction Next signatures and scoped original evidence PASS')
