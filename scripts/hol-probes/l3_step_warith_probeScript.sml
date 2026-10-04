val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = stmt "skip_statement" Skip;
val _ = hyps "addw_hypotheses" ADDW;
val _ = stmt "addw_statement" ADDW;
val _ = hyps "subw_hypotheses" SUBW;
val _ = stmt "subw_statement" SUBW;
val _ = hyps "addiw_hypotheses" ADDIW;
val _ = stmt "addiw_statement" ADDIW;
val _ = hyps "addw_nop_hypotheses" ADDW_NOP;
val _ = stmt "addw_nop_statement" ADDW_NOP;
val _ = hyps "subw_nop_hypotheses" SUBW_NOP;
val _ = stmt "subw_nop_statement" SUBW_NOP;
val _ = hyps "addiw_nop_hypotheses" ADDIW_NOP;
val _ = stmt "addiw_nop_statement" ADDIW_NOP;
val _ = print "source=HOL riscv_stepScript.sml:637 Skip = save_thm over Skip_def, and 838/859/861 ADDW/ADDIW/SUBW = arithr/arithi [] over dfn'ADDW/ADDIW/SUBW_def with the rd = 0w companion avoided; per-theorem Thm.hyp captured above; the word forms keep the RV32-exclusion, invalid-selector and rd <> 0w hypotheses, and the ADDW_NOP/ADDIW_NOP/SUBW_NOP companions add rd = 0w\n";
