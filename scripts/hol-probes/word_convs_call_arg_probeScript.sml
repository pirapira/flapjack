load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val print_eval = fn label => fn q => print_eval label q;

(* inst_arg_convention rows *)
print_eval "inst_addcarry_ok"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$AddCarry 1 2 3 0) : 8 asm$inst)``;
print_eval "inst_addcarry_bad"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$AddCarry 1 2 3 1) : 8 asm$inst)``;
print_eval "inst_shift_ok"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$Shift ast$Lsl 1 2 (asm$Reg 8)) : 8 asm$inst)``;
print_eval "inst_shift_bad"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$Shift ast$Lsl 1 2 (asm$Reg 7)) : 8 asm$inst)``;
print_eval "inst_longmul_ok"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$LongMul 6 0 0 4) : 8 asm$inst)``;
print_eval "inst_longdiv_ok"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$LongDiv 0 6 6 0 9) : 8 asm$inst)``;
print_eval "inst_addoverflow_ok"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$AddOverflow 1 2 3 0) : 8 asm$inst)``;
print_eval "inst_suboverflow_bad"
  ``wordConvs$inst_arg_convention
      (asm$Arith (asm$SubOverflow 1 2 3 1) : 8 asm$inst)``;
print_eval "inst_const"
  ``wordConvs$inst_arg_convention (asm$Const 1 (0w:8 word) : 8 asm$inst)``;

(* call_arg_convention rows *)
print_eval "call_return_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Return 1 [2;4] : 8 wordLang$prog)``;
print_eval "call_return_bad"
  ``wordConvs$call_arg_convention
      (wordLang$Return 1 [4;2] : 8 wordLang$prog)``;
print_eval "call_raise_ok"
  ``wordConvs$call_arg_convention (wordLang$Raise 2 : 8 wordLang$prog)``;
print_eval "call_raise_bad"
  ``wordConvs$call_arg_convention (wordLang$Raise 3 : 8 wordLang$prog)``;
print_eval "call_install_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Install 2 4 0 0 ((sptree$LN,sptree$LN) : unit spt # unit spt) : 8 wordLang$prog)``;
print_eval "call_install_bad"
  ``wordConvs$call_arg_convention
      (wordLang$Install 2 5 0 0 ((sptree$LN,sptree$LN) : unit spt # unit spt) : 8 wordLang$prog)``;
print_eval "call_alloc_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Alloc 2 ((sptree$LN):unit spt,(sptree$LN):unit spt) : 8 wordLang$prog)``;
print_eval "call_alloc_bad"
  ``wordConvs$call_arg_convention
      (wordLang$Alloc 3 ((sptree$LN):unit spt,(sptree$LN):unit spt) : 8 wordLang$prog)``;
print_eval "call_storeconsts_ok"
  ``wordConvs$call_arg_convention
      (wordLang$StoreConsts 0 2 4 6 ([] : (bool # 8 word) list) : 8 wordLang$prog)``;
print_eval "call_call_none_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Call NONE NONE [0;2;4] NONE : 8 wordLang$prog)``;
print_eval "call_call_none_bad"
  ``wordConvs$call_arg_convention
      (wordLang$Call NONE NONE [0;4] NONE : 8 wordLang$prog)``;
print_eval "call_call_some_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Call
        (SOME ([2;4],((sptree$LN):unit spt,(sptree$LN):unit spt),
               wordLang$Skip, 10, 11))
        NONE [2;4] NONE : 8 wordLang$prog)``;
print_eval "call_inst_ok"
  ``wordConvs$call_arg_convention
      (wordLang$Inst (asm$Arith (asm$AddCarry 1 2 3 0) : 8 asm$inst) : 8 wordLang$prog)``;
print_eval "call_seq_bad"
  ``wordConvs$call_arg_convention
      (wordLang$Seq (wordLang$Raise 2) (wordLang$Raise 3) : 8 wordLang$prog)``;
