(* Direct HOL-EVAL observations for panLang$inlinable.
   Reference: cakeml/pancake/panLangScript.sml:389-391. *)
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

val _ = print_eval "inline_true"
  ``inlinable (Function <| name := strlit "f"; inline := T;
    export := F; params := []; body := Skip; return := One |>)``;
val _ = print_eval "inline_false"
  ``inlinable (Function <| name := strlit "f"; inline := F;
    export := T; params := []; body := Skip; return := One |>)``;
val _ = print_eval "non_function"
  ``inlinable (Decl One (strlit "x") (Const (0w:64 word)))``;
