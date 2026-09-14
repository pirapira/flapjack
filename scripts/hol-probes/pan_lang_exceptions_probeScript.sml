(*
  Direct HOL-EVAL observations for Pancake panLang$exceptions.
  Reference: cakeml/pancake/panLangScript.sml:328-337.
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

val exception_decl =
  ``(ExnDecl (strlit "E") (Comb [One; One]) : (8 word) panLang$decl)``;
val _ = print_eval "empty"
  ``exceptions ([] : (8 word) panLang$decl list)``;
val _ = print_eval "exception"
  ``exceptions [^exception_decl]``;
