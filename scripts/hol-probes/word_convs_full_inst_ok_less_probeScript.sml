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

val goodInst  = ``wordLang$Inst (asm$Const 1 (0w:8 word)) : 8 wordLang$prog``;
val badInst   = ``wordLang$Inst (asm$Arith (asm$Binop asm$Add 1 2 (asm$Imm (2w:8 word)))) : 8 wordLang$prog``;
val immOkInst = ``wordLang$Inst (asm$Arith (asm$Binop asm$Add 1 2 (asm$Imm (1w:8 word)))) : 8 wordLang$prog``;

val _ = print_eval "eta_var" ``wordLang$exp_to_addr (wordLang$Var 3 : 8 wordLang$exp)``;
val _ = print_eval "eta_op" ``wordLang$exp_to_addr (wordLang$Op asm$Add [wordLang$Var 3; wordLang$Const (5w:8 word)])``;
val _ = print_eval "eta_op_swapped" ``wordLang$exp_to_addr (wordLang$Op asm$Add [wordLang$Const (5w:8 word); wordLang$Var 3])``;
val _ = print_eval "eta_const" ``wordLang$exp_to_addr (wordLang$Const (5w:8 word))``;

val _ = print_eval "fiol_inst_good" ``full_inst_ok_less ^cfg ^goodInst``;
val _ = print_eval "fiol_inst_imm_ok" ``full_inst_ok_less ^cfg ^immOkInst``;
val _ = print_eval "fiol_inst_imm_bad" ``full_inst_ok_less ^cfg ^badInst``;
val _ = print_eval "fiol_seq_bad" ``full_inst_ok_less ^cfg (wordLang$Seq ^goodInst ^badInst)``;
val _ = print_eval "fiol_loop" ``full_inst_ok_less ^cfg (wordLang$Loop (sptree$LN:num_set) ^goodInst (sptree$LN:num_set))``;
val _ = print_eval "fiol_if" ``full_inst_ok_less ^cfg (wordLang$If asm$Equal 1 (asm$Reg 2) ^goodInst ^goodInst)``;
val _ = print_eval "fiol_must_terminate" ``full_inst_ok_less ^cfg (wordLang$MustTerminate ^goodInst)``;
val _ = print_eval "fiol_call_ret_bad" ``full_inst_ok_less ^cfg (wordLang$Call (SOME ([1], (sptree$LN,sptree$LN), ^badInst, 10, 11)) NONE [] NONE)``;
val _ = print_eval "fiol_call_handler_bad" ``full_inst_ok_less ^cfg (wordLang$Call (SOME ([1], (sptree$LN,sptree$LN), ^goodInst, 10, 11)) NONE [] (SOME (2, ^badInst, 20, 21)))``;
val _ = print_eval "fiol_call_none_handler_bad" ``full_inst_ok_less ^cfg (wordLang$Call NONE NONE [] (SOME (2, ^badInst, 20, 21)))``;
val _ = print_eval "fiol_call_ok" ``full_inst_ok_less ^cfg (wordLang$Call NONE NONE [] NONE)``;
val _ = print_eval "fiol_share_load" ``full_inst_ok_less ^cfg (wordLang$ShareInst asm$Load 1 (wordLang$Var 3))``;
val _ = print_eval "fiol_share_load_big" ``full_inst_ok_less ^cfg (wordLang$ShareInst asm$Load 1 (wordLang$Op asm$Add [wordLang$Var 3; wordLang$Const (150w:8 word)]))``;
val _ = print_eval "fiol_share_load16" ``full_inst_ok_less ^cfg (wordLang$ShareInst asm$Load16 1 (wordLang$Var 3))``;
val _ = print_eval "fiol_share_store8" ``full_inst_ok_less ^cfg (wordLang$ShareInst asm$Store8 1 (wordLang$Var 3))``;
val _ = print_eval "fiol_share_const" ``full_inst_ok_less ^cfg (wordLang$ShareInst asm$Load 1 (wordLang$Const (5w:8 word)))``;
val _ = print_eval "fiol_assign" ``full_inst_ok_less ^cfg (wordLang$Assign 1 (wordLang$Const (0w:8 word)))``;
val _ = print_eval "fiol_alloc" ``full_inst_ok_less ^cfg (wordLang$Alloc 1 ((sptree$LN:num_set),(sptree$LN:num_set)))``;

