(* Direct HOL-EVAL probes for crepLang$assign_ret.
   Reference: cakeml/pancake/crepLangScript.sml:122-124. *)
load "bossLib";
load "preamble";
load "../crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "empty"
  ``crepLang$assign_ret ([] : num list)``;
val _ = print_eval "one"
  ``crepLang$assign_ret [1]``;
val _ = print_eval "two"
  ``crepLang$assign_ret [1; 2]``;
