(* Direct HOL-EVAL fixture for parser$panPEG$pancake_peg_def. *)
load "bossLib";
load "preamble";
load "panPEGTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "exception"
  ``parse (pancake_lex "exception E : 1;")``;
