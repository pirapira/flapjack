load "preamble";
load "labPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open labPropsTheory;

fun print_eval label q =
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
              valid_imm := (K (K T)) ;
              addr_offset := (0w, 100w) ;
              hw_offset := (0w, 100w) ;
              byte_offset := (0w, 100w) ;
              jump_offset := (0w, 100w) ;
              cjump_offset := (0w, 100w) ;
              loc_offset := (0w, 100w) |> : 8 asm_config``;

val _ = print_eval "line_ok_asm_skip"
  ``line_ok_pre ^cfg (labLang$Asm (labLang$Asmi (asm$Inst (asm$Skip : 8 asm$inst))) [] 0)``;
val _ = print_eval "line_ok_asm_cbw"
  ``line_ok_pre ^cfg (labLang$Asm (labLang$Cbw 1 2) [] 0)``;
val _ = print_eval "line_ok_label"
  ``line_ok_pre ^cfg (labLang$Label 0 1 0)``;
val _ = print_eval "line_ok_labasm_halt"
  ``line_ok_pre ^cfg (labLang$LabAsm labLang$Halt (0w : 8 word) [] 0)``;
val _ = print_eval "line_ok_asm_badreg"
  ``line_ok_pre ^cfg (labLang$Asm (labLang$Asmi (asm$Inst (asm$Const 9 (0w : 8 word)))) [] 0)``;
val _ = print_eval "all_enc_ok_one_ok"
  ``all_enc_ok_pre ^cfg [labLang$Section 0 [labLang$Asm (labLang$Asmi (asm$Inst (asm$Skip : 8 asm$inst))) [] 0]]``;
val _ = print_eval "all_enc_ok_one_bad"
  ``all_enc_ok_pre ^cfg [labLang$Section 0 [labLang$Asm (labLang$Asmi (asm$Inst (asm$Const 9 (0w : 8 word)))) [] 0]]``;
val _ = print_eval "cbw_to_asm_store8"
  ``cbw_to_asm (labLang$Cbw 1 2) : 8 asm$asm``;
val _ = print_eval "cbw_to_asm_sharemem"
  ``cbw_to_asm (labLang$ShareMem asm$Load 4 (asm$Addr 5 (0w : 8 word))) : 8 asm$asm``;

val _ = print_eval "sec_ok_one_ok"
  ``sec_ok_pre ^cfg (labLang$Section 0 [labLang$Asm (labLang$Asmi (asm$Inst (asm$Skip : 8 asm$inst))) [] 0])``;
val _ = print_eval "sec_ok_one_bad"
  ``sec_ok_pre ^cfg (labLang$Section 0 [labLang$Asm (labLang$Asmi (asm$Inst (asm$Const 9 (0w : 8 word)))) [] 0])``;
val _ = print_eval "sec_ok_empty"
  ``sec_ok_pre ^cfg (labLang$Section 0 [])``;
val _ = print_eval "all_enc_ok_two_ok"
  ``all_enc_ok_pre ^cfg [labLang$Section 0 [labLang$Label 0 1 0];
      labLang$Section 1 [labLang$Asm (labLang$Asmi (asm$Inst (asm$Skip : 8 asm$inst))) [] 0]]``;
val _ = print_eval "all_enc_ok_empty"
  ``all_enc_ok_pre ^cfg ([] : 8 labLang$sec list)``;
