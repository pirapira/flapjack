(* Direct HOL-EVAL probes for crepLang$store_globals.
   Reference: cakeml/pancake/crepLangScript.sml:109-113. *)
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
  ``crepLang$store_globals (3w : 5 word) []``;
val _ = print_eval "one"
  ``crepLang$store_globals (3w : 5 word)
      ([crepLang$Const (7w : 8 word)] : (8 crepLang$exp) list)``;
val _ = print_eval "two"
  ``crepLang$store_globals (3w : 5 word)
      ([crepLang$Const (7w : 8 word); crepLang$Const (9w : 8 word)]
        : (8 crepLang$exp) list)``;
