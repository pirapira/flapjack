(*
  Direct HOL observations for Pancake panLang$nested_seq.
  Reference: cakeml/pancake/panLangScript.sml:211-213.
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
  ``nested_seq ([] : (8 word panLang$prog) list)``
val _ = print_eval "one"
  ``nested_seq [Skip]``
val _ = print_eval "two"
  ``nested_seq [Tick; Skip]``
val _ = print_eval "assign_seq"
  ``nested_seq [Assign Local (strlit "x") (Const (7w : 8 word));
               Assign Local (strlit "y") (Const (9w : 8 word))]``
