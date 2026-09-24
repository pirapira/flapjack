load "preamble";
load "wordLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val P = ``(\(n:num). n MOD 2 = 0)``;

(* every_var_exp *)
val _ = print_eval "evar_var" ``every_var_exp ^P (wordLang$Var 2 : 8 wordLang$exp)``;
val _ = print_eval "evar_var_odd" ``every_var_exp ^P (wordLang$Var 3 : 8 wordLang$exp)``;
val _ = print_eval "evar_const" ``every_var_exp ^P (wordLang$Const (0w:8 word))``;
val _ = print_eval "evar_load" ``every_var_exp ^P (wordLang$Load (wordLang$Var 4) : 8 wordLang$exp)``;
val _ = print_eval "evar_op_ok" ``every_var_exp ^P (wordLang$Op Add [wordLang$Var 2; wordLang$Var 4])``;
val _ = print_eval "evar_op_bad" ``every_var_exp ^P (wordLang$Op Add [wordLang$Var 2; wordLang$Var 3])``;
val _ = print_eval "evar_shift_bad" ``every_var_exp ^P (wordLang$Shift Lsl (wordLang$Var 2) (wordLang$Var 3))``;
val _ = print_eval "evar_lookup" ``every_var_exp ^P (wordLang$Lookup stackLang$NextFree : 8 wordLang$exp)``;

(* every_var_imm *)
val _ = print_eval "eimm_reg_ok" ``every_var_imm ^P (asm$Reg 4 : 8 asm$reg_imm)``;
val _ = print_eval "eimm_reg_bad" ``every_var_imm ^P (asm$Reg 3 : 8 asm$reg_imm)``;
val _ = print_eval "eimm_imm" ``every_var_imm ^P (asm$Imm (0w:8 word))``;

(* every_var_inst *)
val _ = print_eval "einst_const_ok" ``every_var_inst ^P (asm$Const 2 (0w:8 word))``;
val _ = print_eval "einst_binop_ok" ``every_var_inst ^P (asm$Arith (asm$Binop Add 2 4 (asm$Reg 4)))``;
val _ = print_eval "einst_binop_bad" ``every_var_inst ^P (asm$Arith (asm$Binop Add 2 3 (asm$Reg 4)))``;
val _ = print_eval "einst_shift_ok" ``every_var_inst ^P (asm$Arith (asm$Shift Lsl 2 4 (asm$Imm (0w:8 word))))``;
val _ = print_eval "einst_div_ok" ``every_var_inst ^P (asm$Arith (asm$Div 2 4 6))``;
val _ = print_eval "einst_addcarry_bad" ``every_var_inst ^P (asm$Arith (asm$AddCarry 2 4 6 3))``;
val _ = print_eval "einst_longdiv_ok" ``every_var_inst ^P (asm$Arith (asm$LongDiv 2 4 6 8 0))``;
val _ = print_eval "einst_mem_load_ok" ``every_var_inst ^P (asm$Mem asm$Load 2 (asm$Addr 4 (0w:8 word)))``;
val _ = print_eval "einst_mem_load_bad" ``every_var_inst ^P (asm$Mem asm$Load 3 (asm$Addr 4 (0w:8 word)))``;
val _ = print_eval "einst_mem_load8_ok" ``every_var_inst ^P (asm$Mem asm$Load8 2 (asm$Addr 4 (0w:8 word)))``;
val _ = print_eval "einst_mem_load16" ``every_var_inst ^P (asm$Mem asm$Load16 3 (asm$Addr 4 (0w:8 word)))``;
val _ = print_eval "einst_fpless_ok" ``every_var_inst ^P (asm$FP (asm$FPLess 2 0 1))``;
val _ = print_eval "einst_fpless_bad" ``every_var_inst ^P (asm$FP (asm$FPLess 3 0 1))``;
val _ = print_eval "einst_movtoreg_8_ok" ``every_var_inst ^P ((asm$FP (asm$FPMovToReg 2 4 0)) : 8 asm$inst)``;
val _ = print_eval "einst_movtoreg_8_bad" ``every_var_inst ^P ((asm$FP (asm$FPMovToReg 2 3 0)) : 8 asm$inst)``;
val _ = print_eval "einst_movtoreg_64_ok" ``every_var_inst ^P ((asm$FP (asm$FPMovToReg 2 3 0)) : 64 asm$inst)``;
val _ = print_eval "einst_skip" ``every_var_inst ^P (asm$Skip : 8 asm$inst)``;