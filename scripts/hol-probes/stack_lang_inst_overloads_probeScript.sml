load "preamble";
load "stack_removeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_removeTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "left_shift_inst_2_3"
  ``(left_shift_inst 2 3 : 8 stackLang$prog) =
    (Inst (Arith (Shift Lsl 2 2 (Imm (3w:8 word)))) : 8 stackLang$prog)``;
val _ = print_eval "right_shift_inst_2_3"
  ``(right_shift_inst 2 3 : 8 stackLang$prog) =
    (Inst (Arith (Shift Lsr 2 2 (Imm (3w:8 word)))) : 8 stackLang$prog)``;
val _ = print_eval "const_inst_1_0"
  ``(const_inst 1 (0w:8 word) : 8 stackLang$prog) =
    (Inst (Const 1 0w) : 8 stackLang$prog)``;
val _ = print_eval "load_inst_2_3"
  ``(load_inst 2 3 : 8 stackLang$prog) =
    (Inst (Mem Load 2 (Addr 3 0w)) : 8 stackLang$prog)``;
val _ = print_eval "store_inst_2_3"
  ``(store_inst 2 3 : 8 stackLang$prog) =
    (Inst (Mem Store 2 (Addr 3 0w)) : 8 stackLang$prog)``;
val _ = print_eval "halt_inst_0"
  ``(halt_inst (0w:8 word) : 8 stackLang$prog) =
    (Seq (Inst (Const 1 0w)) (Halt 1) : 8 stackLang$prog)``;