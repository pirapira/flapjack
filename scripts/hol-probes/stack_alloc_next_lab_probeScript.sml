(* Direct HOL-EVAL observations for stack_alloc$next_lab.
   Source: cakeml/compiler/backend/stack_allocScript.sml:649-662. *)
load "bossLib";
load "preamble";
load "stack_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_allocTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val handler_only =
  ``stackLang$Call NONE (INL 0) (SOME (stackLang$Skip, 0, 5))``;
val handler_twelve =
  ``stackLang$Call NONE (INL 0) (SOME (stackLang$Skip, 0, 12))``;
val handler_four =
  ``stackLang$Call NONE (INL 0) (SOME (stackLang$Skip, 0, 4))``;
val handler_eight =
  ``stackLang$Call NONE (INL 0) (SOME (stackLang$Skip, 0, 8))``;
val handler_not_recursed =
  ``stackLang$Call NONE (INL 0)
      (SOME (stackLang$Call NONE (INL 0)
        (SOME (stackLang$Skip, 0, 40)), 0, 6))``;
val seq_program = ``stackLang$Seq ^handler_only stackLang$Skip``;
val if_loop_program =
  ``stackLang$Loop
      (stackLang$If Equal 1 (Reg 2) ^handler_four ^handler_eight)``;
val return_program =
  ``stackLang$Call (SOME (^handler_twelve, 0, 3, 4)) (INL 0) NONE``;
val both_program =
  ``stackLang$Call (SOME (^handler_twelve, 0, 3, 4)) (INL 0)
      (SOME (stackLang$Call NONE (INL 0)
        (SOME (stackLang$Skip, 0, 15)), 1, 7))``;

val _ = print_eval "next_lab_skip" ``stack_alloc$next_lab stackLang$Skip 3``;
val _ = print_eval "next_lab_if_loop" ``stack_alloc$next_lab ^if_loop_program 0``;
val _ = print_eval "next_lab_seq_handler" ``stack_alloc$next_lab ^seq_program 1``;
val _ = print_eval "next_lab_call_none"
  ``stack_alloc$next_lab (stackLang$Call NONE (INL 0) NONE) 3``;
val _ = print_eval "next_lab_handler_not_recursed"
  ``stack_alloc$next_lab ^handler_not_recursed 2``;
val _ = print_eval "next_lab_return" ``stack_alloc$next_lab ^return_program 1``;
val _ = print_eval "next_lab_both_continuations"
  ``stack_alloc$next_lab ^both_program 1``;
