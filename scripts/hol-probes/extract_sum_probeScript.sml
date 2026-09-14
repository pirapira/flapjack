(* Direct HOL-EVAL fixture for parser$extract_sum_def. *)
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

val _ = print_eval "inl" ``extract_sum (INL 7 : num + num)``;
val _ = print_eval "inr" ``extract_sum (INR 9 : num + num)``;
