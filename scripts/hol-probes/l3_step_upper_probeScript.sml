val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
fun gen label th =
  (print(label ^ "="); print_term(concl(GEN_ALL(DISCH_ALL th))); print "\n");
fun typ label q = (print(label ^ "="); print_type(type_of q); print "\n");

val _ = hyps "lui_hypotheses" LUI;
val _ = stmt "lui_statement" LUI;
val _ = gen "lui_gen" LUI;
val _ = hyps "auipc_hypotheses" AUIPC;
val _ = stmt "auipc_statement" AUIPC;
val _ = gen "auipc_gen" AUIPC;
val _ = typ "imm20_type" ``(0w : word20)``;
val _ = print "source=HOL riscv_stepScript.sml:853-854 class_rd0 evaluator over dfn'LUI/AUIPC_def; per-theorem Thm.hyp captured above for BOTH LUI and AUIPC (each register ALU write theorem carries the sole hypothesis rd <> 0w), plus GEN_ALL(DISCH_ALL) typed statements\n";
