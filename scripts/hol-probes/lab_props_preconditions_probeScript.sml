(* Direct HOL-EVAL observations for labProps line_ok_pre/sec_ok_pre and the
   all_enc_ok_pre overload, plus lab_to_target cbw_to_asm. *)
load "bossLib";
load "preamble";
load "labPropsTheory";
load "lab_to_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open labPropsTheory;
open lab_to_targetTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val _ = print_eval "pre_label" ``line_ok_pre c (Label 3 1 99)``;
val _ = print_eval "pre_labasm" ``line_ok_pre c (LabAsm Halt 0w [] 77)``;
val _ = print_eval "pre_asmi_skip" ``line_ok_pre c (Asm (Asmi (Inst Skip)) [] 77)``;
val _ = print_eval "pre_cbw_to_asm" ``cbw_to_asm (Cbw 1 2)``;
val _ = print_eval "pre_share_to_asm" ``cbw_to_asm (ShareMem Load 2 (Addr 3 0w))``;
val _ = print_eval "pre_empty_sections" ``all_enc_ok_pre c []``;
val _ = print_eval "pre_label_section"
  ``all_enc_ok_pre c [Section 3 [Label 3 1 0; LabAsm Halt 0w [] 0]]``;
val _ = print_eval "pre_skip_asm_section"
  ``all_enc_ok_pre c [Section 4 [Asm (Asmi (Inst Skip)) [] 0]]``;
