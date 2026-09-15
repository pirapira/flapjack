(*
  Direct HOL-EVAL observations for the CakeML word-to-stack frame and call
  boundary (GH #1047 / bead flapjack-2ib).

  Sources (cakeml/compiler/backend):
    word_to_stackScript.sml: call_dest, stack_arg_count, stack_free, StackArgs,
      StackHandlerArgs, SeqStackFree, copy_ret, num_stack_ret, compile_prog

  The probe evaluates the original definitions directly; the Lean test
  Flapjack/Test/WordStackCallParity.lean consumes the checked-in .out.
*)
load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

(* call_dest: the indirect-call target is the last argument. *)
val _ = print_eval "calldest_some"
  ``call_dest (SOME 7:num option) [4;6;8] (12:num,20:num,19:num)``
val _ = print_eval "calldest_none_last_phy"
  ``call_dest (NONE:num option) [4;6;8] (12:num,20:num,19:num)``
val _ = print_eval "calldest_none_last_stack"
  ``call_dest (NONE:num option) [4;6;26] (12:num,20:num,19:num)``
val _ = print_eval "calldest_none_empty"
  ``call_dest (NONE:num option) [] (12:num,20:num,19:num)``

(* stack_arg_count / stack_free: direct (INL) and indirect (INR) arities. *)
val _ = print_eval "argcount_inl_15_12" ``stack_arg_count (INL 0:num+num) 15 12``
val _ = print_eval "argcount_inr_15_12" ``stack_arg_count (INR 0:num+num) 15 12``
val _ = print_eval "argcount_inl_5_3" ``stack_arg_count (INL 0:num+num) 5 3``
val _ = print_eval "argcount_inr_5_3" ``stack_arg_count (INR 0:num+num) 5 3``
val _ = print_eval "stackfree_inl_15_12"
  ``stack_free (INL 0:num+num) 15 (12,20,19:num)``
val _ = print_eval "stackfree_inr_15_12"
  ``stack_free (INR 0:num+num) 15 (12,20,19:num)``
val _ = print_eval "stackfree_inl_5_3"
  ``stack_free (INL 0:num+num) 5 (3,6,5:num)``
val _ = print_eval "stackfree_inr_5_3"
  ``stack_free (INR 0:num+num) 5 (3,6,5:num)``

(* StackArgs / StackHandlerArgs shape (direct and indirect). *)
val _ = print_eval "stackargs_inl_3"
  ``StackArgs (INL 0:num+num) 3 (12,20,19:num)``
val _ = print_eval "stackargs_inr_3"
  ``StackArgs (INR 0:num+num) 3 (12,20,19:num)``
val _ = print_eval "stackargs_inl_5_3"
  ``StackArgs (INL 0:num+num) 5 (3,6,5:num)``
val _ = print_eval "stackargs_inr_5_3"
  ``StackArgs (INR 0:num+num) 5 (3,6,5:num)``
val _ = print_eval "handlerargs_inl_3"
  ``StackHandlerArgs F (INL 0:num+num) 3 (12,20,19:num)``

(* SeqStackFree elides a zero free count. *)
val _ = print_eval "seqstackfree_0"
  ``SeqStackFree 0 (Skip:64 stackLang$prog)``
val _ = print_eval "seqstackfree_2"
  ``SeqStackFree 2 (Skip:64 stackLang$prog)``

(* copy_ret / num_stack_ret. *)
val _ = print_eval "num_stack_ret_12_3" ``num_stack_ret 12 [4;6;8]``
val _ = print_eval "num_stack_ret_2_3" ``num_stack_ret 2 [4;6;8]``
val _ = print_eval "copy_ret_none_12"
  ``copy_ret F F (12,20,19:num) [4;6;8] (Skip:64 stackLang$prog)``
val _ = print_eval "copy_ret_handler_2"
  ``copy_ret F T (2,6,5:num) [4;6;8] (Skip:64 stackLang$prog)``
(* compile_prog: the frame size f and the entry StackAlloc (f - stack_arg_count),
   with the RISC-V asm_config (reg_count 32, avoid_regs [0;2;3;4;31]). *)
val cp_config = ``(<| ISA := RISC_V; encode := ARB; big_endian := F;
   code_alignment := 0; link_reg := SOME 1; avoid_regs := [0;2;3;4;31];
   reg_count := 32; fp_reg_count := 0; two_reg_arith := F; valid_imm := ARB;
   addr_offset := ARB; hw_offset := ARB; byte_offset := ARB; jump_offset := ARB;
   cjump_offset := ARB; loc_offset := ARB |>) : 64 asm_config``
val cp_bitmaps = ``((List [4w],1n) : (64 word) app_list # num)``

val _ = print_eval "compileprog_f_3_3"
  ``FST (SND (compile_prog ^cp_config F (Skip:64 wordLang$prog) 3 3 ^cp_bitmaps))``
val _ = print_eval "compileprog_alloc_3_3"
  ``FST (compile_prog ^cp_config F (Skip:64 wordLang$prog) 3 3 ^cp_bitmaps)``
val _ = print_eval "compileprog_f_assign_3_3"
  ``FST (SND (compile_prog ^cp_config F (Assign 26 (Const (0w:64 word))) 3 3 ^cp_bitmaps))``
val _ = print_eval "compileprog_f_15_12"
  ``FST (SND (compile_prog ^cp_config F (Skip:64 wordLang$prog) 15 12 ^cp_bitmaps))``
val _ = print_eval "compileprog_f_5_3"
  ``FST (SND (compile_prog ^cp_config F (Skip:64 wordLang$prog) 5 3 ^cp_bitmaps))``
