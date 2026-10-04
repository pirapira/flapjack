#!/usr/bin/env python3
"""Pin source-reviewed complete Shift source/runtime composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftRun.lean': 'af4ebadfcccf69c69823f874a92ccf6abd934ba2ca5f326b1d30856f1a675c9f', 'scripts/hol-probes/riscv_shift_run_probeScript.sml': 'd282acb6f6431aa3a6f7076ef9e0c9428a159ba259476e03e5dcc86bc2b3d438', 'scripts/hol-probes/riscv_shift_run_probe.out': '108e1acc0d64c31465661dc68b0552aa22de5162b5409853a01ba49899b13e66'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native Shift original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_shift_run_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('Shift requires one complete original registration')
    for label in ('source_shift_clause', 'source_shift_types', 'source_shift_hypotheses', 'target_ok_clause', 'target_ok_types', 'target_ok_hypotheses', 'run_sll_clause', 'run_sll_types', 'run_sll_hypotheses', 'run_srl_clause', 'run_srl_types', 'run_srl_hypotheses', 'run_sra_clause', 'run_sra_types', 'run_sra_hypotheses', 'run_slli_clause', 'run_slli_types', 'run_slli_hypotheses', 'run_srli_clause', 'run_srli_types', 'run_srli_hypotheses', 'run_srai_clause', 'run_srai_types', 'run_srai_hypotheses'):
        if label not in rows[0]:
            raise ValueError('missing Shift original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native Shift source/runtime original evidence PASS')
