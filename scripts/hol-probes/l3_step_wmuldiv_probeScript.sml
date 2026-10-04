loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
            (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;

val _ = Globals.show_types := true;

fun stmt label th =
  (print (label ^ "="); print_term (concl th); print "\n");

fun hyps label th =
  (print (label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));

val _ = hyps "mulw_hypotheses" MULW;
val _ = stmt "mulw_statement" MULW;
val _ = hyps "divw_hypotheses" DIVW;
val _ = stmt "divw_statement" DIVW;
val _ = hyps "divuw_hypotheses" DIVUW;
val _ = stmt "divuw_statement" DIVUW;
val _ = hyps "remw_hypotheses" REMW;
val _ = stmt "remw_statement" REMW;
val _ = hyps "remuw_hypotheses" REMUW;
val _ = stmt "remuw_statement" REMUW;
val _ = hyps "mulw_nop_hypotheses" MULW_NOP;
val _ = stmt "mulw_nop_statement" MULW_NOP;
val _ = hyps "divw_nop_hypotheses" DIVW_NOP;
val _ = stmt "divw_nop_statement" DIVW_NOP;
val _ = hyps "divuw_nop_hypotheses" DIVUW_NOP;
val _ = stmt "divuw_nop_statement" DIVUW_NOP;
val _ = hyps "remw_nop_hypotheses" REMW_NOP;
val _ = stmt "remw_nop_statement" REMW_NOP;
val _ = hyps "remuw_nop_hypotheses" REMUW_NOP;
val _ = stmt "remuw_nop_statement" REMUW_NOP;
val _ = print "source=HOL riscv_stepScript.sml W multiply/divide families via arithr [[ArchBase<>0]] over dfn'MULW/MULW_def and 874-886 DIVW/DIVUW/REMW/REMUW with the rd = 0w companions avoided; per-theorem Thm.hyp captured above; W forms keep the RV32-exclusion, invalid-selector and rd <> 0w hypotheses and signal Illegal_Instr on RV32\n";
