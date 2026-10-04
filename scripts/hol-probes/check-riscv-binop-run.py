#!/usr/bin/env python3
"""Scoped original source/native Binop signature and evidence guard.
Syntactic regression only; Lean checks proofs, source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/BinopRun.lean': 'b75aaf879a15252bb8be289ca4bd2153de05f6caf3ca0270fd8acf0110d0d70d', 'scripts/hol-probes/riscv_binop_run_probeScript.sml': '35e3882322329db94b1b6607d69110db4439ed446a657494351b4a793087aa6d', 'scripts/hol-probes/riscv_binop_run_probe.out': '8ab35726f7516a78af2c1abbde37e671e3aca16b46a2c51472f9967edc7bc166'}
LABELS = ['source_reg_imm_clause', 'source_reg_imm_hypotheses', 'source_reg_imm_types', 'source_binop_upd_clause', 'source_binop_upd_hypotheses', 'source_binop_upd_types', 'source_arith_upd_clause', 'source_arith_upd_hypotheses', 'source_arith_upd_types', 'source_asm_step_clause', 'source_asm_step_hypotheses', 'source_asm_step_types', 'source_bop_r_clause', 'source_bop_r_hypotheses', 'source_bop_r_types', 'native_add_clause', 'native_add_hypotheses', 'native_add_types', 'native_sub_clause', 'native_sub_hypotheses', 'native_sub_types', 'native_and_clause', 'native_and_hypotheses', 'native_and_types', 'native_or_clause', 'native_or_hypotheses', 'native_or_types', 'native_xor_clause', 'native_xor_hypotheses', 'native_xor_types']
def material(s):
    return '\n'.join(s.split('theorem '+name,1)[1].split(' := by',1)[0] for name in ['binop_source_post','binop_register_run'])+'\n'+s.split('def binopValue',1)[1].split('/--',1)[0]
def check(root=ROOT):
    for path,expected in CHECKS.items():
        s=(root/path).read_text()
        if path.endswith('BinopRun.lean'): s=material(s)
        if hashlib.sha256(s.encode()).hexdigest()!=expected:
            raise ValueError('full source/native Binop drift: '+path)
    driver=(root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ')
    rows=[r for r in driver.splitlines() if r.startswith('run_probe riscv_binop_run_probeScript.sml ')]
    if len(rows)!=1: raise ValueError('one full source/native Binop registration required')
    for label in LABELS:
        if label not in rows[0].split(): raise ValueError('missing Binop source/native row: '+label)
    return True
if __name__=='__main__':
    check()
    print('Full source/native Binop composition signatures and original clauses PASS')
