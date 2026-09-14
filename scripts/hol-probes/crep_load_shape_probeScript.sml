(* Direct HOL-EVAL probes for crepLang$load_shape.
   Reference: cakeml/pancake/crepLangScript.sml:82-86. *)
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
  ``crepLang$load_shape (0w : 32 word) 0 (crepLang$Const (7w : 32 word))``;
val _ = print_eval "zero_one"
  ``crepLang$load_shape (0w : 32 word) 1 (crepLang$Const (7w : 32 word))``;
val _ = print_eval "zero_two"
  ``crepLang$load_shape (0w : 32 word) 2 (crepLang$Const (7w : 32 word))``;
val _ = print_eval "nonzero_two"
  ``crepLang$load_shape (4w : 32 word) 2 (crepLang$Const (7w : 32 word))``;
