(* Direct HOL-EVAL fixture for parser$panPEG$mkleaf_def. *)
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

val _ = print_eval "keyword"
  ``mkleaf (KeywordT SkipK, unknown_loc)``;
val _ = print_eval "identifier"
  ``mkleaf (IdentT "name", unknown_loc)``;
