loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
            (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;

val _ = Globals.show_types := true;

fun stmt label th =
  (print (label ^ "="); print_term (concl th); print "\n");

fun hyps label th =
  (print (label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));

val _ = hyps "mulh_hypotheses" MULH;
val _ = stmt "mulh_statement" MULH;
val _ = hyps "mulhu_hypotheses" MULHU;
val _ = stmt "mulhu_statement" MULHU;
val _ = hyps "mulhsu_hypotheses" MULHSU;
val _ = stmt "mulhsu_statement" MULHSU;
val _ = hyps "mulh_nop_hypotheses" MULH_NOP;
val _ = stmt "mulh_nop_statement" MULH_NOP;
val _ = hyps "mulhu_nop_hypotheses" MULHU_NOP;
val _ = stmt "mulhu_nop_statement" MULHU_NOP;
val _ = hyps "mulhsu_nop_hypotheses" MULHSU_NOP;
val _ = stmt "mulhsu_nop_statement" MULHSU_NOP;
val _ = print "source=HOL riscv_stepScript.sml high-multiply families via arithr [] over dfn'MULH/MULHU/MULHSU_def with the rd = 0w companions avoided; per-theorem Thm.hyp captured above; three mode queries, 128-bit intermediate products and literal per-operand signedness retained\n";
