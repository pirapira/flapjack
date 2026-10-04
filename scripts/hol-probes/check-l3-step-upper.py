"""Reject drift in original HOL upper-immediate evaluated instruction captures."""
from pathlib import Path

EXPECTED = [
    'lui_hypotheses=(rd :word5) ≠ (0w :word5)',
    "lui_statement=dfn'LUI ((rd :word5),(imm :word20)) (s :riscv_state) =",
    's with',
    'c_gpr :=',
    '  s.c_gpr⦇',
    '    s.procID ↦',
    '      (s.c_gpr s.procID)⦇',
    '        rd ↦ (sw2sw ((imm @@ (0w :word12)) :word32) :word64)',
    '      ⦈',
    '  ⦈',
    'lui_gen=∀(s :riscv_state) (rd :word5) (imm :word20).',
    '  rd ≠ (0w :word5) ⇒',
    "  dfn'LUI (rd,imm) s =",
    '  s with',
    '  c_gpr :=',
    '    s.c_gpr⦇',
    '      s.procID ↦',
    '        (s.c_gpr s.procID)⦇',
    '          rd ↦ (sw2sw ((imm @@ (0w :word12)) :word32) :word64)',
    '        ⦈',
    '    ⦈',
    'auipc_hypotheses=(rd :word5) ≠ (0w :word5)',
    "auipc_statement=dfn'AUIPC ((rd :word5),(imm :word20)) (s :riscv_state) =",
    's with',
    'c_gpr :=',
    '  s.c_gpr⦇',
    '    s.procID ↦',
    '      (s.c_gpr s.procID)⦇',
    '        rd ↦',
    '          s.c_PC s.procID + (sw2sw ((imm @@ (0w :word12)) :word32) :word64)',
    '      ⦈',
    '  ⦈',
    'auipc_gen=∀(s :riscv_state) (rd :word5) (imm :word20).',
    '  rd ≠ (0w :word5) ⇒',
    "  dfn'AUIPC (rd,imm) s =",
    '  s with',
    '  c_gpr :=',
    '    s.c_gpr⦇',
    '      s.procID ↦',
    '        (s.c_gpr s.procID)⦇',
    '          rd ↦',
    '            s.c_PC s.procID + (sw2sw ((imm @@ (0w :word12)) :word32) :word64)',
    '        ⦈',
    '    ⦈',
    'imm20_type=:word20',
    "source=HOL riscv_stepScript.sml:853-854 class_rd0 evaluator over dfn'LUI/AUIPC_def; per-theorem Thm.hyp captured above for BOTH LUI and AUIPC (each register ALU write theorem carries the sole hypothesis rd <> 0w), plus GEN_ALL(DISCH_ALL) typed statements",
]


def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL upper-immediate capture differs from reviewed statements")


if __name__ == "__main__":
    check(Path(__file__).with_name("l3_step_upper_probe.out").read_text())
    print("step_upper: exact original HOL statements, hypothesis and types PASS")
