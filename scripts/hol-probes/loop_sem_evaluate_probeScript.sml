(*
  Direct HOL-EVAL fixture for Pancake loopSem evaluate_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:278-360.
  The observations cover normal completion, an intermediate assignment,
  sequence return, break/continue result propagation, a tail call whose callee
  returns NONE, and timeout local clearing.
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
    fun simp_once t = QCONV (SIMP_CONV (srw_ss())
        [evaluate_def, eval_def, set_var_def, get_vars_def,
         call_env_def, dec_clock_def, fix_clock_def]) t
    fun eval_once t = QCONV EVAL t
    val th0 = SIMP_CONV (srw_ss())
      [evaluate_def, eval_def, set_var_def, get_vars_def,
       call_env_def, dec_clock_def, fix_clock_def] q
    val th1 = eval_once (rconc th0)
    val th2 = simp_once (rconc th1)
    val th = eval_once (rconc th2)
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "skip"
  ``loopSem$evaluate (Skip, ^s)``
val _ = print_eval "assign"
  ``case loopSem$evaluate (Assign 1 (Const (7w : 8 word)), ^s with clock := 5) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "seq_return"
  ``case loopSem$evaluate
      (Seq (Assign 1 (Const (7w : 8 word))) (Return [1]),
       ^s with <|locals := LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "break"
  ``case loopSem$evaluate
      (Break 3, ^s with <|locals := insert 1 (Word 7w) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "continue"
  ``case loopSem$evaluate
      (Continue 2, ^s with <|locals := insert 1 (Word 7w) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "tail_call_no_result"
  ``case loopSem$evaluate
      (Call NONE (SOME 1) [] NONE,
       ^s with <|locals := LN; code := insert 1 ([],Skip) LN; clock := 5|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
val _ = print_eval "tick_timeout"
  ``case loopSem$evaluate
      (Tick, ^s with <|locals := insert 1 (Word 7w) LN; clock := 0|>) of
      (res,s') => (res, lookup 1 s'.locals, s'.clock)``
