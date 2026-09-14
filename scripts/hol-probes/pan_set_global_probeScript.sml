(*
  Direct HOL observations for set_global_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:46-50.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
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
  ``FLOOKUP (set_global (strlit "g") (ValWord (5w:8 word)) ^base).globals
      (strlit "g") = SOME (ValWord 5w)``;

val _ = print_eval "set_global_overwrite"
  ``FLOOKUP (set_global (strlit "g") (ValWord (5w:8 word))
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 1w))).globals
      (strlit "g") = SOME (ValWord 5w)``;

val _ = print_eval "set_global_sibling"
  ``FLOOKUP (set_global (strlit "h") (ValWord (7w:8 word))
      (^s with globals := FEMPTY |+ (strlit "g", ValWord 1w))).globals
      (strlit "g") = SOME (ValWord 1w)``;

val _ = print_eval "set_global_locals"
  ``(set_global (strlit "g") (ValWord (5w:8 word))
      (^s with locals := FEMPTY)).locals = FEMPTY``;
