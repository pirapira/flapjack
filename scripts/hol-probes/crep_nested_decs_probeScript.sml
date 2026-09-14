(* Direct HOL-EVAL probes for crepLang$nested_decs.
   Reference: cakeml/pancake/crepLangScript.sml:102-107. *)
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
  ``crepLang$nested_decs [] [] (Tick : 8 crepLang$prog)``;
val _ = print_eval "paired"
  ``crepLang$nested_decs ([1; 2] : num list)
      ([crepLang$Const (7w : 8 word); crepLang$Const (9w : 8 word)]
        : (8 crepLang$exp) list)
      (Tick : 8 crepLang$prog)``;
val _ = print_eval "names_empty"
  ``crepLang$nested_decs ([] : num list)
      ([crepLang$Const (7w : 8 word)] : (8 crepLang$exp) list)
      (Tick : 8 crepLang$prog)``;
val _ = print_eval "values_empty"
  ``crepLang$nested_decs ([1] : num list)
      ([] : (8 crepLang$exp) list) (Tick : 8 crepLang$prog)``;
