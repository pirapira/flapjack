(*
  Direct HOL-EVAL observations for Pancake panLang$functions.
  Reference: cakeml/pancake/panLangScript.sml:319-328.
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
  ``(Function <| name := strlit "f"; inline := T; export := F;
                 params := [(strlit "x", One)]; body := Skip;
                 return := One |> : (8 word) panLang$decl)``;
val global_decl = ``Decl One (strlit "g") (Const (7w : 8 word))``;

val _ = print_eval "empty"
  ``functions ([] : (8 word) panLang$decl list)``;
val _ = print_eval "function" ``functions [^function_decl]``;
val _ = print_eval "global" ``functions [^global_decl]``;
