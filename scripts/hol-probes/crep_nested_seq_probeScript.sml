(* Direct HOL-EVAL probes for crepLang$nested_seq.
   Reference: cakeml/pancake/crepLangScript.sml:89-92. *)
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
  ``crepLang$nested_seq ([] : (8 word crepLang$prog) list)``;
val _ = print_eval "one"
  ``crepLang$nested_seq [Skip : 8 word crepLang$prog]``;
val _ = print_eval "two"
  ``crepLang$nested_seq [Tick; Skip : 8 word crepLang$prog]``;
val _ = print_eval "assign_seq"
  ``crepLang$nested_seq [Assign 1 (Const (7w : 8 word));
                         Assign 2 (Const (9w : 8 word))]``;
