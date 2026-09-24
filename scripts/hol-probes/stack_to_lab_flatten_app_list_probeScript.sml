load "preamble"; load "stack_to_labTheory";
open bossLib; open HolKernel Parse; open preamble; open stack_to_labTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "flatten_app_tick"
  ``append (FST (stack_to_lab$flatten T stackLang$Tick 0 0 [] []))``;
val _ = print_eval "flatten_app_halt"
  ``append (FST (stack_to_lab$flatten T (stackLang$Halt 0) 0 0 [] []))``;
val _ = print_eval "flatten_app_inst"
  ``append (FST (stack_to_lab$flatten T (stackLang$Inst (asm$Skip : 8 asm$inst)) 0 0 [] []))``;
val _ = print_eval "flatten_app_seq"
  ``append (FST (stack_to_lab$flatten T
      (stackLang$Seq stackLang$Tick (stackLang$Halt 0)) 0 0 [] []))``;
val _ = print_eval "flatten_app_raise"
  ``append (FST (stack_to_lab$flatten T (stackLang$Raise 3) 0 0 [] []))``;