(* Direct HOL-EVAL fixture for crep_arith$mul_const_def. *)
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
  ``crep_arith$mul_const (Var 2) (0w : 8 word)``;
val _ = print_eval "one"
  ``crep_arith$mul_const (Var 2) (1w : 8 word)``;
val _ = print_eval "two"
  ``crep_arith$mul_const (Var 2) (2w : 8 word)``;
val _ = print_eval "three"
  ``crep_arith$mul_const (Var 2) (3w : 8 word)``;
val _ = print_eval "four"
  ``crep_arith$mul_const (Var 2) (4w : 8 word)``;
val _ = print_eval "eight"
  ``crep_arith$mul_const (Var 2) (8w : 8 word)``;
