(*
  Probe outputs for the original CakeML Pancake loopSem control transition
  exit_loop.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:272-276 (exit_loop_def)
  and the result datatype at loopSemScript.sml:30-37.
*)
load "bossLib";
load "preamble";
load "semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "exit_loop_break"
  ``exit_loop (SOME (Break 3))``
val _ = print_eval "exit_loop_break_zero"
  ``exit_loop (SOME (Break 0))``
val _ = print_eval "exit_loop_continue"
  ``exit_loop (SOME (Continue 2))``
val _ = print_eval "exit_loop_other"
  ``exit_loop (SOME TimeOut)``
val _ = print_eval "exit_loop_none"
  ``exit_loop NONE``
val _ = print_eval "exit_loop_error"
  ``exit_loop (SOME Error)``
