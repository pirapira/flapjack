(*
  Direct HOL observations for panSem$nb_op_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:549-553.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "op8" ``panSem$nb_op Op8``;
val _ = print_eval "op16" ``panSem$nb_op Op16``;
val _ = print_eval "opw" ``panSem$nb_op OpW``;
val _ = print_eval "op32" ``panSem$nb_op Op32``;
