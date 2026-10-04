#!/usr/bin/env python3
"""Pin full original SLTI/SLTIU equations and both source hypotheses.
Syntactic regression guard; source comparison and kernel checking are required.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/L3/Step/ImmediateComparison.lean': '4960f7fd244d3704081871a77084876d8ef44603921bb23a9f3becd526f3421d', 'HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml': '40efdb718c87d4c87be4c377e6650cfffa11cd84be52518c8c90044219f97dac', 'scripts/hol-probes/l3_step_immediate_comparison_probeScript.sml': '845620412609ae8ba84312763404a3e6ecbc18f4c9b6fb0f5d488748c6828610', 'scripts/hol-probes/l3_step_immediate_comparison_probe.out': '1c78bc14b6c773c679d96e6d94580d796b9c9fc654ba473bd20b42b23a21d63c'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError('Original comparison equation/hypothesis/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    rows = [c for c in commands if c.startswith('run_probe l3_step_immediate_comparison_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('Original comparison probe requires one registration')
    for op in ['slti', 'sltiu']:
        for suffix in ['statement', 'types', 'source_hypotheses', 'proved']:
            if op + '_' + suffix not in rows[0]:
                raise ValueError('Missing original comparison evidence sentinel')
    return True
if __name__ == '__main__':
    check()
    print('Original SLTI/SLTIU full equations and BOTH original hypotheses PASS')
