(*
  Direct HOL observations for crepSem$exit_loop.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:234-237.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "exit_loop_break"
  ``exit_loop (SOME (Break 3))``;
val _ = print_eval "exit_loop_break_zero"
  ``exit_loop (SOME (Break 0))``;
val _ = print_eval "exit_loop_continue"
  ``exit_loop (SOME (Continue 2))``;
val _ = print_eval "exit_loop_other"
  ``exit_loop (SOME TimeOut)``;
val _ = print_eval "exit_loop_none"
  ``exit_loop NONE``;
val _ = print_eval "exit_loop_error"
  ``exit_loop (SOME Error)``;
