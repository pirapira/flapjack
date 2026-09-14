(*
  Direct HOL-EVAL fixture for Pancake loopSem semantics_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:508-532.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val simp = SIMP_CONV (srw_ss())
      [evaluate_def, eval_def, get_vars_def, call_env_def,
       dec_clock_def, fix_clock_def]
    val th0 = simp q
    val th1 = QCONV EVAL (rconc th0)
    val th2 = QCONV simp (rconc th1)
    val th = QCONV EVAL (rconc th2)
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "return_clock_zero"
  ``case evaluate (Call NONE (SOME 1) [] NONE,
      ^s with <|code := insert 1 ([],Return []) LN; clock := 0|>) of
      (res,s') => (res,s'.clock)``
val _ = print_eval "return_clock_one"
  ``case evaluate (Call NONE (SOME 1) [] NONE,
      ^s with <|code := insert 1 ([],Return []) LN; clock := 1|>) of
      (res,s') => (res,s'.clock)``
