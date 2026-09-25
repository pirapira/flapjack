(* Direct HOL observations for loopLangScript exp and loop_arith constructors,
   used to check the faithful width-indexed Lean carriers HolLoopExp/LoopArith. *)
load "preamble";
load "loopLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "exp_const" ``(Const (7w:8 word) : 8 loopLang$exp)``;
val _ = print_eval "exp_var" ``(Var 3 : 8 loopLang$exp)``;
val _ = print_eval "exp_lookup" ``(Lookup (1w:5 word) : 8 loopLang$exp)``;
val _ = print_eval "exp_load" ``(Load (Var 3) : 8 loopLang$exp)``;
val _ = print_eval "exp_op" ``(Op asm$Add [Var 1; Const (2w:8 word)] : 8 loopLang$exp)``;
val _ = print_eval "exp_shift" ``(Shift ast$Lsl (Var 1) (Const (2w:8 word)) : 8 loopLang$exp)``;
val _ = print_eval "exp_base" ``(BaseAddr : 8 loopLang$exp)``;
val _ = print_eval "arith_longmul" ``(LLongMul 1 2 3 4 : loopLang$loop_arith)``;
val _ = print_eval "arith_longdiv" ``(LLongDiv 1 2 3 4 5 : loopLang$loop_arith)``;
val _ = print_eval "arith_div" ``(LDiv 1 2 3 : loopLang$loop_arith)``;