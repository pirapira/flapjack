load "preamble";
load "loopLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "prog_skip" ``(Skip : 8 loopLang$prog)``;
val _ = print_eval "prog_assign" ``(Assign 1 (Const (7w:8 word)) : 8 loopLang$prog)``;
val _ = print_eval "prog_if" ``(If Equal 0 (Reg 1) Skip Tick (sptree$LN : num_set) : 8 loopLang$prog)``;
val _ = print_eval "prog_loop" ``(Loop (sptree$LN : num_set) Tick (sptree$LN : num_set) : 8 loopLang$prog)``;
val _ = print_eval "prog_return" ``(Return [1;2] : 8 loopLang$prog)``;
val _ = print_eval "prog_shmem" ``(ShMem Load 1 (Const (0w:8 word)) : 8 loopLang$prog)``;
val _ = print_eval "prog_call" ``(Call (SOME ([1], (sptree$LN : num_set))) NONE [] (SOME (2, Skip, Tick, (sptree$LN : num_set))) : 8 loopLang$prog)``;
val _ = print_eval "prog_ffi" ``(FFI (implode "f") 1 2 3 4 (sptree$LN : num_set) : 8 loopLang$prog)``;
