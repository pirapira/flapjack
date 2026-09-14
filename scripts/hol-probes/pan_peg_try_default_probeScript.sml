(*
  Direct HOL observations for panPEG$try_default_def.
  Reference: cakeml/pancake/parser/panPEGScript.sml:124-125.
  The source-level parser examples exercise both the successful parser branch
  and the default leaf branch when optional function modifiers are absent.
*)
load "bossLib";
load "preamble";
load "panPEGTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panPEGTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "try_default_success"
  ``parse (pancake_lex "inline fun f() { skip; }")``;

val _ = print_eval "try_default_default"
  ``parse (pancake_lex "fun f() { skip; }")``;
