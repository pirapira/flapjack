(*
  Direct HOL-EVAL observations for Pancake panLang$is_function.
  Reference: cakeml/pancake/panLangScript.sml:314-317.
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

val function_decl =
  ``Function <| name := strlit "f"; inline := T; export := F;
                 params := []; body := Skip; return := One |>``;
val global_decl = ``Decl One (strlit "g") (Const (7w : 8 word))``;

val _ = print_eval "function" ``is_function ^function_decl``;
val _ = print_eval "global" ``is_function ^global_decl``;
