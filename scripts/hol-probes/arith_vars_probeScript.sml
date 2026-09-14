(* Direct HOL-EVAL fixture for loop_live$arith_vars. *)
load "bossLib";
load "preamble";
load "loop_liveTheory";
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

val _ = print_eval "long_mul"
  ``loop_live$arith_vars
      (loopLang$LLongMul 1 2 3 4)
      (insert 6 () (insert 2 () (insert 1 () LN)))``
val _ = print_eval "div"
  ``loop_live$arith_vars
      (loopLang$LDiv 1 2 3)
      (insert 5 () (insert 1 () LN))``
val _ = print_eval "long_div"
  ``loop_live$arith_vars
      (loopLang$LLongDiv 1 2 3 4 5)
      (insert 8 () (insert 2 () (insert 1 () LN)))``
