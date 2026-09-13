(*
  Direct HOL-EVAL probes for Pancake loop_call$is_load.
  Reference: cakeml/pancake/loop_callScript.sml:10-15.
*)
load "bossLib";
load "preamble";
load "../loop_callTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_callTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "load" ``is_load Load``
val _ = print_eval "load8" ``is_load Load8``
val _ = print_eval "load16" ``is_load Load16``
val _ = print_eval "load32" ``is_load Load32``
val _ = print_eval "store" ``is_load Store``
val _ = print_eval "store8" ``is_load Store8``
val _ = print_eval "store16" ``is_load Store16``
val _ = print_eval "store32" ``is_load Store32``
