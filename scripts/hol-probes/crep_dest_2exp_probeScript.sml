(* Direct HOL-EVAL fixture for crep_arith$dest_2exp_def. *)
load "bossLib";
load "preamble";
load "crep_arithTheory";
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

val _ = print_eval "zero"
  ``crep_arith$dest_2exp 0 (0w : 8 word)``;
val _ = print_eval "one"
  ``crep_arith$dest_2exp 3 (1w : 8 word)``;
val _ = print_eval "two"
  ``crep_arith$dest_2exp 0 (2w : 8 word)``;
val _ = print_eval "four"
  ``crep_arith$dest_2exp 4 (4w : 8 word)``;
val _ = print_eval "eight"
  ``crep_arith$dest_2exp 0 (8w : 8 word)``;
val _ = print_eval "odd"
  ``crep_arith$dest_2exp 0 (3w : 8 word)``;
val _ = print_eval "even_odd"
  ``crep_arith$dest_2exp 0 (6w : 8 word)``;
