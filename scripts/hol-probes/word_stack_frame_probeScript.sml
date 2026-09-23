(*
  Direct HOL-EVAL observations for the CakeML frame-occupancy boundary.
  Sources:
    cakeml/compiler/backend/word_to_stackScript.sml: wReg1/wReg2,
      format_var, stack_arg_count, stack_free, bits_to_word, word_list,
      write_bitmap
    cakeml/compiler/backend/word_allocScript.sml: limit_var
*)
load "bossLib";
load "preamble";
load "word_to_stackTheory";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "maxvar_skip" ``max_var (Skip:64 wordLang$prog)``
val _ = print_eval "maxvar_move"
  ``max_var (Move 0 [(0,0)]:64 wordLang$prog)``
val _ = print_eval "maxvar_seq"
  ``max_var (Seq (Assign 0 (Const (0w:64 word)))
    (Assign 26 (Const (0w:64 word))))``

val _ = print_eval "wreg1_4" ``wReg1 4 (12,20,19:num)``
val _ = print_eval "wreg1_24" ``wReg1 24 (12,20,19:num)``
val _ = print_eval "wreg1_25" ``wReg1 25 (12,20,19:num)``
val _ = print_eval "wreg1_26" ``wReg1 26 (12,20,19:num)``
val _ = print_eval "wreg2_4" ``wReg2 4 (12,20,19:num)``
val _ = print_eval "wreg2_26" ``wReg2 26 (12,20,19:num)``

val _ = print_eval "fmt_some_lo" ``format_var 12 (SOME 4:num option)``
val _ = print_eval "fmt_some_hi" ``format_var 12 (SOME 26:num option)``
val _ = print_eval "fmt_none" ``format_var 12 (NONE:num option)``

val _ = print_eval "argcount_inl" ``stack_arg_count (INL 3:num+num) 15 12``
val _ = print_eval "argcount_inr" ``stack_arg_count (INR 3:num+num) 15 12``
val _ = print_eval "stackfree_inl"
  ``stack_free (INL 3:num+num) 8 (12,20,19:num)``
val _ = print_eval "stackfree_inr"
  ``stack_free (INR 3:num+num) 15 (12,20,19:num)``

val _ = print_eval "bits_tft" ``(bits_to_word [T;F;T]:64 word)``
val _ = print_eval "bits_fff" ``(bits_to_word [F;F;F]:64 word)``
val _ = print_eval "wordlist_3"
  ``(word_list [T;F;T;F;T] 3:64 word list)``
val _ = print_eval "bitmap_empty"
  ``(write_bitmap (LN:unit spt) 12 3:64 word list)``
val _ = print_eval "bitmap_slot2"
  ``(write_bitmap (insert 24 () (LN:unit spt)) 12 3:64 word list)``
val _ = print_eval "bitmap_slots1_2"
  ``(write_bitmap (insert 25 () (insert 26 () (LN:unit spt)))
    12 3:64 word list)``

val _ = print_eval "limit_skip" ``limit_var (Skip:64 wordLang$prog)``
val _ = print_eval "limit_seq"
  ``limit_var (Seq (Assign 0 (Const (0w:64 word)))
    (Assign 26 (Const (0w:64 word))))``

(* Later-offset Stack Temp-region bound (bead flapjack-pxn.18.2.2.2).

   compile_prog at the production RISC-V shape (reg_count 32, avoid_regs
   [0;2;3;4;31] -> k = 22) picks stack_var_count = MAX(max_var DIV 2 + 1 - k,
   stack_arg_count) and frame f = stack_var_count + 1. A function taking its
   arguments in registers (arg_count = reg_count = 22) whose later variables
   44 and 46 are multiword/stack colours must place both slots strictly inside
   the frame: 44 DIV 2 = 22 -> slot f - 1 - 0, 46 DIV 2 = 23 -> slot
   f - 1 - 1, both < f. *)
val cp_config = ``(<| ISA := RISC_V; encode := ARB; big_endian := F;
   code_alignment := 0; link_reg := SOME 1; avoid_regs := [0;2;3;4;31];
   reg_count := 32; fp_reg_count := 0; two_reg_arith := F; valid_imm := ARB;
   addr_offset := ARB; hw_offset := ARB; byte_offset := ARB; jump_offset := ARB;
   cjump_offset := ARB; loc_offset := ARB |>) : 64 asm_config``
val cp_bitmaps = ``((List [4w],1n) : (64 word) app_list # num)``
val later_pair_prog =
  ``(Seq (Assign 44 (Const (0w:64 word)))
       (Seq (Assign 46 (Const (0w:64 word))) Skip)) : 64 wordLang$prog``

val _ = print_eval "later_pair_f"
  ``FST (SND (compile_prog ^cp_config F ^later_pair_prog 22 22 ^cp_bitmaps))``
val _ = print_eval "later_pair_alloc"
  ``FST (compile_prog ^cp_config F ^later_pair_prog 22 22 ^cp_bitmaps)``
val _ = print_eval "later_pair_slot_44"
  ``let f = FST (SND (compile_prog ^cp_config F ^later_pair_prog 22 22 ^cp_bitmaps))
   in SND (HD (FST (wReg1 44 (22,f,0:num))))``
val _ = print_eval "later_pair_slot_46"
  ``let f = FST (SND (compile_prog ^cp_config F ^later_pair_prog 22 22 ^cp_bitmaps))
   in SND (HD (FST (wReg1 46 (22,f,0:num))))``
val _ = print_eval "later_pair_bounded"
  ``let f = FST (SND (compile_prog ^cp_config F ^later_pair_prog 22 22 ^cp_bitmaps))
   in SND (HD (FST (wReg1 44 (22,f,0:num)))) < f /\
      SND (HD (FST (wReg1 46 (22,f,0:num)))) < f``
