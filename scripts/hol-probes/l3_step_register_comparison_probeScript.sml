val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 1000000;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
fun gen label th =
  (print(label ^ "="); print_term(concl(GEN_ALL(DISCH_ALL th))); print "\n");
val _ = hyps "slt_hypotheses" SLT;
val _ = stmt "slt_statement" SLT;
val _ = gen "slt_gen" SLT;
val _ = print("slt_hypothesis_count=" ^ Int.toString(length(hyp SLT)) ^ "\n");
val _ = hyps "sltu_hypotheses" SLTU;
val _ = stmt "sltu_statement" SLTU;
val _ = gen "sltu_gen" SLTU;
val _ = print("sltu_hypothesis_count=" ^ Int.toString(length(hyp SLTU)) ^ "\n");
val _ = hyps "slt_nop_hypotheses" SLT_NOP;
val _ = stmt "slt_nop_statement" SLT_NOP;
val _ = gen "slt_nop_gen" SLT_NOP;
val _ = print("slt_nop_hypothesis_count=" ^ Int.toString(length(hyp SLT_NOP)) ^ "\n");
val _ = hyps "sltu_nop_hypotheses" SLTU_NOP;
val _ = stmt "sltu_nop_statement" SLTU_NOP;
val _ = gen "sltu_nop_gen" SLTU_NOP;
val _ = print("sltu_nop_hypothesis_count=" ^ Int.toString(length(hyp SLTU_NOP)) ^ "\n");
