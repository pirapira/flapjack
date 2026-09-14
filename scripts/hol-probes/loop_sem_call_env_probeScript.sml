(*
  Direct HOL-EVAL probes for Pancake loopSem$call_env.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:177-180.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(32,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "arg_zero"
  ``loopSem$get_var_imm (Reg 0 : 32 reg_imm)
      (loopSem$call_env [Word 5w; Word 7w] ^s)``
val _ = print_eval "arg_one"
  ``loopSem$get_var_imm (Reg 1 : 32 reg_imm)
      (loopSem$call_env [Word 5w; Word 7w] ^s)``
val _ = print_eval "arg_missing"
  ``loopSem$get_var_imm (Reg 2 : 32 reg_imm)
      (loopSem$call_env [Word 5w; Word 7w] ^s)``
