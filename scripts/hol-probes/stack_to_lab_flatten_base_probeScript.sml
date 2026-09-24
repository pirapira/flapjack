load "preamble";
load "stack_to_labTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_to_labTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "flatten_tick" ``flatten T (stackLang$Tick : 8 stackLang$prog) 0 0 ([]:num list) ([]:num list)``;
val _ = print_eval "flatten_inst_skip" ``flatten T (stackLang$Inst (asm$Skip : 8 asm$inst)) 0 0 ([]:num list) ([]:num list)``;
val _ = print_eval "flatten_halt" ``flatten T (stackLang$Halt 0) 0 0 ([]:num list) ([]:num list)``;
