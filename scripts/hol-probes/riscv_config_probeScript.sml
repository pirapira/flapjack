load "preamble";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open riscv_targetTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val cfg = ``(riscv_config : 64 asm_config)``;

val _ = print_eval "cfg_isa" ``^cfg.ISA``;
val _ = print_eval "cfg_reg_count" ``^cfg.reg_count``;
val _ = print_eval "cfg_avoid_regs" ``^cfg.avoid_regs``;
val _ = print_eval "cfg_fp_reg_count" ``^cfg.fp_reg_count``;
val _ = print_eval "cfg_link_reg" ``^cfg.link_reg``;
val _ = print_eval "cfg_two_reg_arith" ``^cfg.two_reg_arith``;
val _ = print_eval "cfg_big_endian" ``^cfg.big_endian``;
val _ = print_eval "cfg_code_alignment" ``^cfg.code_alignment``;
val _ = print_eval "cfg_addr_offset" ``^cfg.addr_offset``;
val _ = print_eval "cfg_hw_offset" ``^cfg.hw_offset``;
val _ = print_eval "cfg_byte_offset" ``^cfg.byte_offset``;
val _ = print_eval "cfg_jump_offset" ``^cfg.jump_offset``;
val _ = print_eval "cfg_cjump_offset" ``^cfg.cjump_offset``;
val _ = print_eval "cfg_loc_offset" ``^cfg.loc_offset``;

val subOp = ``(INL asm$Sub : asm$binop + asm$cmp)``;
val addOp = ``(INL asm$Add : asm$binop + asm$cmp)``;
val _ = print_eval "valid_imm_sub_min12" ``^cfg.valid_imm ^subOp (-2048w : 64 word)``;
val _ = print_eval "valid_imm_sub_min12p1" ``^cfg.valid_imm ^subOp (-2047w : 64 word)``;
val _ = print_eval "valid_imm_add_min12" ``^cfg.valid_imm ^addOp (-2048w : 64 word)``;
val _ = print_eval "valid_imm_add_max12" ``^cfg.valid_imm ^addOp (2047w : 64 word)``;
val _ = print_eval "valid_imm_add_max12p1" ``^cfg.valid_imm ^addOp (2048w : 64 word)``;