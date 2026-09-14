(* Direct HOL-EVAL fixture for parser$parse_statement_def. *)
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

val _ = print_eval "skip"
  ``parse_statement (pancake_lex "skip; }")``;
val _ = print_eval "return"
  ``parse_statement (pancake_lex "return 1; }")``;
