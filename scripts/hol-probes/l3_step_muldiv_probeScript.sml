val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.show_types := true;
fun stmt label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th =
  (print(label ^ "="); List.app (fn h => (print_term h; print "\n")) (Thm.hyp th));
val _ = hyps "mul_hypotheses" MUL;
val _ = stmt "mul_statement" MUL;
val _ = hyps "div_hypotheses" DIV;
val _ = stmt "div_statement" DIV;
val _ = hyps "rem_hypotheses" REM;
val _ = stmt "rem_statement" REM;
val _ = hyps "remu_hypotheses" REMU;
val _ = stmt "remu_statement" REMU;
val _ = print "source=HOL riscv_stepScript.sml:874-886 mul/div/rem = arithr [] over dfn'MUL/DIV/REM/REMU_def with the rd = 0w companion avoided; per-theorem Thm.hyp captured above; DIVU (line 881) is unconditional with a double in32BitMode RV32 widening and is not ported here\n";
