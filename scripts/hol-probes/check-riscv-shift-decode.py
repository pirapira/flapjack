#!/usr/bin/env python3
"""Pin source-reviewed full native Shift composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeShift.lean': 'a1b02a07630d408adfa8650dd51905336d8bf7edc74865a242aac4e5c4441221', 'scripts/hol-probes/riscv_shift_decode_probeScript.sml': '9ac5b37ab626b7fa1c823d2054841450d7bcd88e2db72e45fe05a67f78d0e731', 'scripts/hol-probes/riscv_shift_decode_probe.out': '3b0155108b5b14bf36fee4d177f8bacab34a0c0d44b09aa32eb4d14c7444fe8f'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native Shift original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_shift_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('Shift requires one complete original registration')
    for label in ('sll_decode_zero', 'sll_decode_all_ones', 'sll_decode_high_bit', 'sll_decode_alias', 'sll_encode_source_clause', 'sll_carrier_types', 'sll_symbolic_query', 'sll_source_hypotheses', 'srl_decode_zero', 'srl_decode_all_ones', 'srl_decode_high_bit', 'srl_decode_alias', 'srl_encode_source_clause', 'srl_carrier_types', 'srl_symbolic_query', 'srl_source_hypotheses', 'sra_decode_zero', 'sra_decode_all_ones', 'sra_decode_high_bit', 'sra_decode_alias', 'sra_encode_source_clause', 'sra_carrier_types', 'sra_symbolic_query', 'sra_source_hypotheses', 'srli_decode_zero', 'srli_decode_all_ones', 'srli_decode_high_bit', 'srli_decode_alias', 'srli_encode_source_clause', 'srli_carrier_types', 'srli_symbolic_query', 'srli_source_hypotheses', 'srai_decode_zero', 'srai_decode_all_ones', 'srai_decode_high_bit', 'srai_decode_alias', 'srai_encode_source_clause', 'srai_carrier_types', 'srai_symbolic_query', 'srai_source_hypotheses'):
        if label not in rows[0]:
            raise ValueError('missing Shift original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native Shift unrestricted decode original evidence PASS')
