(*
  Direct HOL observations for panSem$set_global_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:403-405.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(8,unit) panSem$state)``;
val base = ``(^s with globals := FEMPTY)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "set_global_insert"
  ``FLOOKUP (panSem$set_global (strlit "g") (ValWord (5w:8 word)) ^base).globals
      (strlit "g") = SOME (ValWord 5w)``;

val _ = print_eval "set_global_overwrite"
  ``FLOOKUP (panSem$set_global (strlit "g") (ValWord (5w:8 word))
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 1w))).globals
      (strlit "g") = SOME (ValWord 5w)``;

val _ = print_eval "set_global_sibling"
  ``FLOOKUP (panSem$set_global (strlit "h") (ValWord (7w:8 word))
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 1w))).globals
      (strlit "g") = SOME (ValWord 1w)``;

val _ = print_eval "set_global_locals"
  ``(panSem$set_global (strlit "g") (ValWord (5w:8 word))
      (^s with locals := FEMPTY)).locals = FEMPTY``;
