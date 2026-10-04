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
val _ = hyps "jal_hypotheses" JAL;
val _ = stmt "jal_statement" JAL;
val _ = gen "jal_gen" JAL;
val _ = print("jal_hypothesis_count=" ^ Int.toString(length(hyp JAL)) ^ "\n");
val _ = hyps "jalr_hypotheses" JALR;
val _ = stmt "jalr_statement" JALR;
val _ = gen "jalr_gen" JALR;
val _ = print("jalr_hypothesis_count=" ^ Int.toString(length(hyp JALR)) ^ "\n");
val _ = hyps "jal_nop_hypotheses" JAL_NOP;
val _ = stmt "jal_nop_statement" JAL_NOP;
val _ = gen "jal_nop_gen" JAL_NOP;
val _ = print("jal_nop_hypothesis_count=" ^ Int.toString(length(hyp JAL_NOP)) ^ "\n");
val _ = hyps "jalr_nop_hypotheses" JALR_NOP;
val _ = stmt "jalr_nop_statement" JALR_NOP;
val _ = gen "jalr_nop_gen" JALR_NOP;
val _ = print("jalr_nop_hypothesis_count=" ^ Int.toString(length(hyp JALR_NOP)) ^ "\n");
