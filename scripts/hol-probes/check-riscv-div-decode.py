#!/usr/bin/env python3
"""Pin source-reviewed full native DIV composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeDiv.lean': '2d98d99a46416e861181c341f65fc5a6ab299e1fbf4be9dc6172da5fa5f889cf', 'scripts/hol-probes/riscv_div_decode_probeScript.sml': '16209f1c05020f5efa370c7924d6cfb3722bd0791ce0da366d9bc2ada4e8587c', 'scripts/hol-probes/riscv_div_decode_probe.out': '76b036821e668341a65af9d76a5551cdd664d7f3da621f0e9539429e71a52a03'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native DIV original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_div_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('DIV requires one complete original registration')
    for label in ('div_decode_zero','div_decode_all_ones','div_decode_mixed','div_encode_source_clause','div_encode_source_hypotheses','div_carrier_types'):
        if label not in rows[0]:
            raise ValueError('missing DIV original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native signed DIV unrestricted decode original evidence PASS')
