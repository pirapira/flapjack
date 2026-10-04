val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
fun statement label th = (print(label ^ "="); print_term(concl th); print "\n");
fun typ label q = (print(label ^ "="); print_type(type_of q); print "\n");

val _ = statement "avoid_statement" avoid_signalAddressException;
val _ = typ "avoid_signalAddressException_type" ``signalAddressException``;
val _ = print "avoid_source=HOL riscv_stepScript.sml avoid_signalAddressException (l.553-557): ~b ==> ((if b then signalAddressException t u else s) = s)\n";

val _ = statement "update_pc_statement" update_pc;
val _ = typ "update_pc_def_type" ``update_pc``;
val _ = print "update_pc_source=HOL riscv_stepScript.sml update_pc (l.662-663): saved from update_pc_def and write'PC_def\n";
