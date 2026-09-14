(*
  Direct HOL-EVAL probes for Pancake loopLang$nested_seq.
  Reference: cakeml/pancake/loopLangScript.sml:72-75.
*)
load "bossLib";
load "preamble";
load "../loopLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "empty"
  ``nested_seq ([] : (32 word loopLang$prog) list)``
val _ = print_eval "one"
  ``nested_seq [Skip]``
val _ = print_eval "two"
  ``nested_seq [Tick; Skip]``
val _ = print_eval "assign_load"
  ``nested_seq [Assign 1 (Const (7w : 32 word)); Load32 0 2]``
