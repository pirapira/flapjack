(* Direct HOL-EVAL probes for crepLang$stores.
   Reference: cakeml/pancake/crepLangScript.sml:95-100. *)
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
  ``crepLang$stores (crepLang$Var 3) [] 0w``;
val _ = print_eval "zero_two"
  ``crepLang$stores (crepLang$Var 3)
      [crepLang$Const (7w : 32 word); crepLang$Const (9w : 32 word)] 0w``;
val _ = print_eval "nonzero_two"
  ``crepLang$stores (crepLang$Var 3)
      [crepLang$Const (7w : 32 word); crepLang$Const (9w : 32 word)] 4w``;
