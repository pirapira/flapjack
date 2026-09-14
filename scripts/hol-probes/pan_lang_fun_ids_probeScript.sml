(*
  Direct HOL-EVAL observations for Pancake panLang$fun_ids.
  Reference: cakeml/pancake/panLangScript.sml:336-349.
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

val _ = print_eval "empty"
  ``fun_ids (Skip : (8 word) panLang$prog)``;
val _ = print_eval "call"
  ``fun_ids (Call NONE (strlit "f") [])``;
val _ = print_eval "handler"
  ``fun_ids
      (Call (SOME (NONE,
        SOME (strlit "E", strlit "h", Call NONE (strlit "g") [])))
        (strlit "f") [])``;
val _ = print_eval "dec_call"
  ``fun_ids
      (DecCall (strlit "x") One (strlit "d") []
        (Call NONE (strlit "g") []))``;
