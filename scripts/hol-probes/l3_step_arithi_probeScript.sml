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

val _ = hyps "addi_hypotheses" ADDI;
val _ = stmt "addi_statement" ADDI;
val _ = gen "addi_gen" ADDI;
val _ = hyps "slti_hypotheses" SLTI;
val _ = stmt "slti_statement" SLTI;
val _ = gen "slti_gen" SLTI;
val _ = hyps "sltiu_hypotheses" SLTIU;
val _ = stmt "sltiu_statement" SLTIU;
val _ = gen "sltiu_gen" SLTIU;
val _ = hyps "andi_hypotheses" ANDI;
val _ = stmt "andi_statement" ANDI;
val _ = gen "andi_gen" ANDI;
val _ = hyps "ori_hypotheses" ORI;
val _ = stmt "ori_statement" ORI;
val _ = gen "ori_gen" ORI;
val _ = hyps "xori_hypotheses" XORI;
val _ = stmt "xori_statement" XORI;
val _ = gen "xori_gen" XORI;
val _ = typ "imm12_type" ``(0w : word12)``;
val _ = print "source=HOL riscv_stepScript.sml:837-843 class evaluator over dfn'ADDI/SLTI/SLTIU/ANDI/ORI/XORI_def; per-theorem Thm.hyp captured above (ADDI/ANDI/ORI/XORI have rd <> 0w; SLTI/SLTIU additionally retain the ArchBase <> 1w mode hypothesis propagated by in32BitMode), plus GEN_ALL(DISCH_ALL) typed statements\n";
