(*
  Direct HOL-EVAL observations for Pancake panLang$load_op and panLang$store_op.
  Reference: cakeml/pancake/panLangScript.sml:300-313.
*)
load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "load_op8" ``load_op Op8``;
val _ = print_eval "load_op16" ``load_op Op16``;
val _ = print_eval "load_opw" ``load_op OpW``;
val _ = print_eval "load_op32" ``load_op Op32``;
val _ = print_eval "store_op8" ``store_op Op8``;
val _ = print_eval "store_op16" ``store_op Op16``;
val _ = print_eval "store_opw" ``store_op OpW``;
val _ = print_eval "store_op32" ``store_op Op32``;
