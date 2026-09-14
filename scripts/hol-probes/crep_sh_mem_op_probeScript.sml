(*
  Direct HOL observations for crepSem$sh_mem_op_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:210-218.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "sh_mem_op_load"
  ``crepSem$sh_mem_op Load 1 (3w:8 word) ^s =
      crepSem$sh_mem_load 1 (3w:8 word) 0 ^s``;
val _ = print_eval "sh_mem_op_store"
  ``crepSem$sh_mem_op Store 1 (3w:8 word) ^s =
      crepSem$sh_mem_store 1 (3w:8 word) 0 ^s``;
val _ = print_eval "sh_mem_op_load8"
  ``crepSem$sh_mem_op Load8 1 (3w:8 word) ^s =
      crepSem$sh_mem_load 1 (3w:8 word) 1 ^s``;
val _ = print_eval "sh_mem_op_store8"
  ``crepSem$sh_mem_op Store8 1 (3w:8 word) ^s =
      crepSem$sh_mem_store 1 (3w:8 word) 1 ^s``;
val _ = print_eval "sh_mem_op_load16"
  ``crepSem$sh_mem_op Load16 1 (3w:8 word) ^s =
      crepSem$sh_mem_load 1 (3w:8 word) 2 ^s``;
val _ = print_eval "sh_mem_op_store16"
  ``crepSem$sh_mem_op Store16 1 (3w:8 word) ^s =
      crepSem$sh_mem_store 1 (3w:8 word) 2 ^s``;
val _ = print_eval "sh_mem_op_load32"
  ``crepSem$sh_mem_op Load32 1 (3w:8 word) ^s =
      crepSem$sh_mem_load 1 (3w:8 word) 4 ^s``;
val _ = print_eval "sh_mem_op_store32"
  ``crepSem$sh_mem_op Store32 1 (3w:8 word) ^s =
      crepSem$sh_mem_store 1 (3w:8 word) 4 ^s``;
