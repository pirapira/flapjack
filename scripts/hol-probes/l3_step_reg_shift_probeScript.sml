val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = hyps "sll_hypotheses" SLL;
val _ = stmt "sll_statement" SLL;
val _ = hyps "srl_hypotheses" SRL;
val _ = stmt "srl_statement" SRL;
val _ = hyps "sra_hypotheses" SRA;
val _ = stmt "sra_statement" SRA;
val _ = hyps "sll_nop_hypotheses" SLL_NOP;
val _ = stmt "sll_nop_statement" SLL_NOP;
val _ = hyps "srl_nop_hypotheses" SRL_NOP;
val _ = stmt "srl_nop_statement" SRL_NOP;
val _ = hyps "sra_nop_hypotheses" SRA_NOP;
val _ = stmt "sra_nop_statement" SRA_NOP;
val _ = print "source=HOL riscv_stepScript.sml:867-869 class evaluator over dfn'SLL/SRL/SRA_def; per-theorem Thm.hyp captured above (each register-shift write theorem carries the invalid-selector and rd <> 0w hypotheses), plus the rd = 0w companions\n";
