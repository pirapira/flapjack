(* Direct HOL-EVAL probes for CakeML Pancake panSem$pan_op_def. *)
load "bossLib";
load "preamble";
load "panSemTheory";
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

val _ = print_eval "mul_two" ``pan_op Mul [3w; 5w]``
val _ = print_eval "mul_one" ``pan_op Mul [3w]``
val _ = print_eval "mul_three" ``pan_op Mul [3w; 5w; 7w]``
