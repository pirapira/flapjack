val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));

val _ = stmt "add_nop_statement" ADD_NOP;
val _ = hyps "add_nop_hypotheses" ADD_NOP;
val _ = stmt "sub_nop_statement" SUB_NOP;
val _ = hyps "sub_nop_hypotheses" SUB_NOP;
val _ = stmt "and_nop_statement" AND_NOP;
val _ = hyps "and_nop_hypotheses" AND_NOP;
val _ = stmt "or_nop_statement" OR_NOP;
val _ = hyps "or_nop_hypotheses" OR_NOP;
val _ = stmt "xor_nop_statement" XOR_NOP;
val _ = hyps "xor_nop_hypotheses" XOR_NOP;
val _ = stmt "addi_nop_statement" ADDI_NOP;
val _ = hyps "addi_nop_hypotheses" ADDI_NOP;
val _ = stmt "andi_nop_statement" ANDI_NOP;
val _ = hyps "andi_nop_hypotheses" ANDI_NOP;
val _ = stmt "ori_nop_statement" ORI_NOP;
val _ = hyps "ori_nop_hypotheses" ORI_NOP;
val _ = stmt "xori_nop_statement" XORI_NOP;
val _ = hyps "xori_nop_hypotheses" XORI_NOP;
val _ = stmt "lui_nop_statement" LUI_NOP;
val _ = hyps "lui_nop_hypotheses" LUI_NOP;
val _ = stmt "auipc_nop_statement" AUIPC_NOP;
val _ = hyps "auipc_nop_hypotheses" AUIPC_NOP;
val _ = print "source=HOL riscv_stepScript.sml:807-833 class_rd0 factories arithi/arithr/load emit the NAME^\"_NOP\" companion through utilsLib.save_thms; sole hypothesis rd = 0w and the state is unchanged\n";
