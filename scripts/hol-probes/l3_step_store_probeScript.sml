val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = hyps "sd_hypotheses" SD;
val _ = stmt "sd_statement" SD;
val _ = hyps "sw_hypotheses" SW;
val _ = stmt "sw_statement" SW;
val _ = hyps "sh_hypotheses" SH;
val _ = stmt "sh_statement" SH;
val _ = hyps "sb_hypotheses" SB;
val _ = stmt "sb_statement" SB;
val _ = print "source=HOL riscv_stepScript.sml:908-915 store = class (rs1,rs2,offs) over dfn'SD/SW/SH/SB_def; SD carries archbase<>0w and aligned_d in its avoid list, SW/SH/SB carry none; per-theorem Thm.hyp captured above; the store factory generates no rd = 0w companion\n";
