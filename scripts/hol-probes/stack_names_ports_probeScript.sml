load "preamble";
load "stack_namesTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_namesTheory;


val names = ``sptree$insert 3 7 (sptree$LN) : num num_map``;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "ri_reg"     ``ri_find_name ^names (Reg 3)``;
val _ = print_eval "ri_imm"     ``ri_find_name ^names (Imm (0w:8 word))``;
val _ = print_eval "inst_const" ``inst_find_name ^names (Const 3 (0w:8 word))``;
val _ = print_eval "inst_div"   ``inst_find_name ^names (Arith (asm$Div 3 4 5))``;
val _ = print_eval "inst_fma"   ``inst_find_name ^names (FP (asm$FPFma 1 2 3))``;
val _ = print_eval "inst_mem"   ``inst_find_name ^names (Mem asm$Load 3 (asm$Addr 3 (8w:8 word)))``;
val _ = print_eval "dest_inr"   ``dest_find_name ^names (INR 3)``;
val _ = print_eval "dest_inl"   ``dest_find_name ^names (INL 2)``;
val _ = print_eval "comp_seq"   ``comp ^names (Seq (Inst (Const 3 (0w:8 word))) (Halt 3) : 8 stackLang$prog)``;
val _ = print_eval "comp_call"  ``comp ^names (Call (SOME (Raise 3, 4, 5, 6)) (INR 3) (SOME (Halt 4, 8, 9)) : 8 stackLang$prog)``;
val _ = print_eval "prog_comp_row" ``prog_comp ^names (1, Halt 3 : 8 stackLang$prog)``;
val _ = print_eval "compile_row"   ``compile ^names [(1, Halt 3 : 8 stackLang$prog); (2, Raise 4 : 8 stackLang$prog)]``;
val _ = print_eval "names_ok_bad"  ``names_ok ^names 4 [0;1]``;
val _ = print_eval "names_ok_ok"   ``names_ok (sptree$LN) 8 []``;
val _ = print_eval "names_ok_dup"  ``names_ok (sptree$insert 0 1 (sptree$insert 1 1 (sptree$LN))) 4 []``;