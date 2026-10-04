val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = hyps "slli_hypotheses" SLLI;
val _ = stmt "slli_statement" SLLI;
val _ = hyps "srli_hypotheses" SRLI;
val _ = stmt "srli_statement" SRLI;
val _ = hyps "srai_hypotheses" SRAI;
val _ = stmt "srai_statement" SRAI;
val _ = hyps "slli_nop_hypotheses" SLLI_NOP;
val _ = stmt "slli_nop_statement" SLLI_NOP;
val _ = hyps "srli_nop_hypotheses" SRLI_NOP;
val _ = stmt "srli_nop_statement" SRLI_NOP;
val _ = hyps "srai_nop_hypotheses" SRAI_NOP;
val _ = stmt "srai_nop_statement" SRAI_NOP;
val _ = print "source=HOL riscv_stepScript.sml:844-846 class evaluator over dfn'SLLI/SRLI/SRAI_def; per-theorem Thm.hyp captured above (each immediate-shift write theorem carries the legality, invalid-selector and rd <> 0w hypotheses), plus the rd = 0w companions\n";
