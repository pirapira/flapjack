(* Direct HOL-EVAL probes for crepLang$load_shape at the RV64 word width.
   Reference: cakeml/pancake/crepLangScript.sml:82-86.
   For a 64-bit word byte$bytes_in_word = n2w (64 DIV 8) = 8w. *)
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

val _ = print_eval "empty64"
  ``crepLang$load_shape (0w : 64 word) 0 (crepLang$Const (7w : 64 word))``;
val _ = print_eval "zero_one64"
  ``crepLang$load_shape (0w : 64 word) 1 (crepLang$Const (7w : 64 word))``;
val _ = print_eval "zero_two64"
  ``crepLang$load_shape (0w : 64 word) 2 (crepLang$Const (7w : 64 word))``;
val _ = print_eval "nonzero_two64"
  ``crepLang$load_shape (8w : 64 word) 2 (crepLang$Const (7w : 64 word))``;