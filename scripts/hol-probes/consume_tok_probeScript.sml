(* Direct HOL-EVAL fixture for parser$consume_tok_def. *)
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
  end

val _ = print_eval "success"
  ``consume_tok (KeywordT SkipK)``;
val _ = print_eval "mismatch"
  ``consume_tok (KeywordT RetK)``;
