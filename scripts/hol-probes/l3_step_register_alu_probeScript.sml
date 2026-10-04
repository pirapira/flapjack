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

val _ = hyps "add_hypotheses" ADD;
val _ = stmt "add_statement" ADD;
val _ = gen "add_gen" ADD;
val _ = hyps "sub_hypotheses" SUB;
val _ = stmt "sub_statement" SUB;
val _ = gen "sub_gen" SUB;
val _ = hyps "and_hypotheses" AND;
val _ = stmt "and_statement" AND;
val _ = gen "and_gen" AND;
val _ = hyps "or_hypotheses" OR;
val _ = stmt "or_statement" OR;
val _ = gen "or_gen" OR;
val _ = hyps "xor_hypotheses" XOR;
val _ = stmt "xor_statement" XOR;
val _ = gen "xor_gen" XOR;
val _ = typ "gpr_op_type" ``(op : word64 -> word64 -> word64)``;
val _ = print "source=HOL riscv_stepScript.sml:858-866 class evaluator over dfn'ADD/SUB/AND/OR/XOR_def; per-theorem Thm.hyp captured above (each register ALU write theorem carries the sole hypothesis rd <> 0w), plus GEN_ALL(DISCH_ALL) typed statements\n";
