(* Direct HOL-EVAL fixture for parser$keep_kw_def. *)
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
  ``keep_kw SkipK``;
val _ = print_eval "ret"
  ``keep_kw RetK``;
