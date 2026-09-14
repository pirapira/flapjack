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
