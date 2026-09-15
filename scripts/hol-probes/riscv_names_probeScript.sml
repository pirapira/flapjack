(*
  Direct HOL-EVAL observations for the CakeML RISC-V register renaming
  `riscv_names` used as `reg_names` by the stack-to-lab configuration.

  Sources:
    cakeml/compiler/backend/riscv/riscv_configScript.sml: riscv_names_def (10)
      -- "0 must be mapped to link reg (1); 1-4 must be mapped to 1st-4th
          args (10-13)"
    cakeml/compiler/backend/riscv/riscv_configScript.sml: riscv_stack_conf (53)

  The source-facing Flapjack adapter `wordRiscVAbiSourceRegister`
  (Flapjack/RiscV/PipelineDiagnostics.lean) is supposed to encode exactly this
  map on the abstract register index of an even Word name.  The probe pins the
  Cake values so the parity test is oracle-backed rather than transcribed.
*)
load "bossLib";
load "preamble";
load "riscv_configTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open riscv_configTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val _ = print_eval "names_0" ``lookup (0:num) riscv_names``;
val _ = print_eval "names_1" ``lookup (1:num) riscv_names``;
val _ = print_eval "names_2" ``lookup (2:num) riscv_names``;
val _ = print_eval "names_3" ``lookup (3:num) riscv_names``;
val _ = print_eval "names_4" ``lookup (4:num) riscv_names``;
val _ = print_eval "names_5" ``lookup (5:num) riscv_names``;
val _ = print_eval "names_6" ``lookup (6:num) riscv_names``;
val _ = print_eval "names_7" ``lookup (7:num) riscv_names``;
val _ = print_eval "names_8" ``lookup (8:num) riscv_names``;
val _ = print_eval "names_9" ``lookup (9:num) riscv_names``;
val _ = print_eval "names_10" ``lookup (10:num) riscv_names``;
val _ = print_eval "names_11" ``lookup (11:num) riscv_names``;
val _ = print_eval "names_12" ``lookup (12:num) riscv_names``;
val _ = print_eval "names_13" ``lookup (13:num) riscv_names``;
val _ = print_eval "names_14" ``lookup (14:num) riscv_names``;
val _ = print_eval "names_15" ``lookup (15:num) riscv_names``;
val _ = print_eval "names_27" ``lookup (27:num) riscv_names``;
val _ = print_eval "names_28" ``lookup (28:num) riscv_names``;
val _ = print_eval "names_29" ``lookup (29:num) riscv_names``;
val _ = print_eval "names_30" ``lookup (30:num) riscv_names``;