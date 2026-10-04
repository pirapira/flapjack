val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = hyps "beq_hypotheses" BEQ;
val _ = stmt "beq_statement" BEQ;
val _ = hyps "bne_hypotheses" BNE;
val _ = stmt "bne_statement" BNE;
val _ = hyps "blt_hypotheses" BLT;
val _ = stmt "blt_statement" BLT;
val _ = hyps "bltu_hypotheses" BLTU;
val _ = stmt "bltu_statement" BLTU;
val _ = hyps "bge_hypotheses" BGE;
val _ = stmt "bge_statement" BGE;
val _ = hyps "bgeu_hypotheses" BGEU;
val _ = stmt "bgeu_statement" BGEU;
val _ = print "source=HOL riscv_stepScript.sml:893-898 conditional branches BEQ/BNE/BLT/BLTU/BGE/BGEU = cbranch over dfn'BEQ/BNE/BLT/BLTU/BGE/BGEU_def with avoid []; the single per-theorem Thm.hyp is ArchBase <> 1w; every source branch is unconditional (no rd/alignment/run premise)\n";
