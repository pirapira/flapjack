load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val cfg = ``<| ISA := RISC_V ;
              encode := (\x. ([] : word8 list)) ;
              big_endian := F ;
              code_alignment := 2 ;
              link_reg := NONE ;
              avoid_regs := [3] ;
              reg_count := 8 ;
              fp_reg_count := 4 ;
              two_reg_arith := T ;
              valid_imm := (\b (w:8 word). w = 1w) ;
              addr_offset := (0w, 100w) ;
              hw_offset := (0w, 100w) ;
              byte_offset := (0w, 100w) ;
              jump_offset := (0w, 100w) ;
              cjump_offset := (0w, 100w) ;
              loc_offset := (0w, 100w) |> : 8 asm_config``;

val iol_binop_imm = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Binop asm$Add 0 0 (asm$Imm (1w:8 word))))``;
val iol_binop_imm_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Binop asm$Add 0 0 (asm$Imm (2w:8 word))))``;
val iol_binop_reg = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Binop asm$Add 0 0 (asm$Reg 5)))``;
val iol_shift_zero_lsl = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Shift ast$Lsl 0 0 (asm$Imm (0w:8 word))))``;
val iol_shift_zero_lsr = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Shift ast$Lsr 0 0 (asm$Imm (0w:8 word))))``;
val iol_shift_width_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Shift ast$Lsl 0 0 (asm$Imm (8w:8 word))))``;
val iol_div_riscv = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$Div 0 1 2))``;
val iol_longmul_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$LongMul 0 1 0 2))``;
val iol_longdiv_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$LongDiv 0 1 2 3 4))``;
val iol_addcarry_ok = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$AddCarry 0 1 2 3))``;
val iol_addcarry_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$AddCarry 0 1 0 3))``;
val iol_addoverflow_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$AddOverflow 0 1 0 3))``;
val iol_suboverflow_bad = ``wordConvs$inst_ok_less ^cfg
  (asm$Arith (asm$SubOverflow 0 1 0 3))``;
val iol_mem_load = ``wordConvs$inst_ok_less ^cfg
  (asm$Mem asm$Load 0 (asm$Addr 0 (1w:8 word)))``;
val iol_mem_load8 = ``wordConvs$inst_ok_less ^cfg
  (asm$Mem asm$Load8 0 (asm$Addr 0 (1w:8 word)))``;
val iol_mem_load16 = ``wordConvs$inst_ok_less ^cfg
  (asm$Mem asm$Load16 0 (asm$Addr 0 (1w:8 word)))``;
val iol_skip = ``wordConvs$inst_ok_less ^cfg asm$Skip``;
val iol_const = ``wordConvs$inst_ok_less ^cfg (asm$Const 0 (0w:8 word))``;
val iol_fpless_ok = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPLess 0 1 2))``;
val iol_fpless_bad = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPLess 0 1 5))``;
val iol_fma_bad = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPFma 0 1 2))``;
val iol_movtoreg_ok = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPMovToReg 1 1 0))``;
val iol_movtoreg_fp_out_of_range = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPMovToReg 1 2 9))``;
val iol_movfromreg_fp_out_of_range = ``wordConvs$inst_ok_less ^cfg (asm$FP (asm$FPMovFromReg 9 1 2))``;

val _ = print_eval "iol_binop_imm" iol_binop_imm;
val _ = print_eval "iol_binop_imm_bad" iol_binop_imm_bad;
val _ = print_eval "iol_binop_reg" iol_binop_reg;
val _ = print_eval "iol_shift_zero_lsl" iol_shift_zero_lsl;
val _ = print_eval "iol_shift_zero_lsr" iol_shift_zero_lsr;
val _ = print_eval "iol_shift_width_bad" iol_shift_width_bad;
val _ = print_eval "iol_div_riscv" iol_div_riscv;
val _ = print_eval "iol_longmul_bad" iol_longmul_bad;
val _ = print_eval "iol_longdiv_bad" iol_longdiv_bad;
val _ = print_eval "iol_addcarry_ok" iol_addcarry_ok;
val _ = print_eval "iol_addcarry_bad" iol_addcarry_bad;
val _ = print_eval "iol_addoverflow_bad" iol_addoverflow_bad;
val _ = print_eval "iol_suboverflow_bad" iol_suboverflow_bad;
val _ = print_eval "iol_mem_load" iol_mem_load;
val _ = print_eval "iol_mem_load8" iol_mem_load8;
val _ = print_eval "iol_mem_load16" iol_mem_load16;
val _ = print_eval "iol_skip" iol_skip;
val _ = print_eval "iol_const" iol_const;
val _ = print_eval "iol_fpless_ok" iol_fpless_ok;
val _ = print_eval "iol_fpless_bad" iol_fpless_bad;
val _ = print_eval "iol_fma_bad" iol_fma_bad;
val _ = print_eval "iol_movtoreg_ok" iol_movtoreg_ok;
val _ = print_eval "iol_movtoreg_fp_out_of_range" iol_movtoreg_fp_out_of_range;
val _ = print_eval "iol_movfromreg_fp_out_of_range" iol_movfromreg_fp_out_of_range;
