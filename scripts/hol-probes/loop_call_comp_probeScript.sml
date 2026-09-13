(*
  Direct HOL-EVAL probes for Pancake loop_call$comp.
  Reference: cakeml/pancake/loop_callScript.sml:18-92.
*)
load "bossLib";
load "preamble";
load "../loop_callTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_callTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "skip"
  ``FST (comp LN (Skip : 32 word loopLang$prog))``
val _ = print_eval "call_dest"
  ``FST (comp LN
      (Call NONE (SOME 3) [1;2] NONE : 32 word loopLang$prog))``
val _ = print_eval "call_last"
  ``FST (comp (insert 2 9 LN)
      (Call NONE NONE [1;2] NONE : 32 word loopLang$prog))``
val _ = print_eval "call_last_loc"
  ``lookup 2 (SND (comp (insert 2 9 LN)
      (Call NONE NONE [1;2] NONE : 32 word loopLang$prog)))``
val _ = print_eval "call_empty"
  ``FST (comp LN
      (Call NONE NONE [] NONE : 32 word loopLang$prog))``
val _ = print_eval "loc_value"
  ``lookup 1 (SND (comp LN
      (LocValue 1 7 : 32 word loopLang$prog)))``
val _ = print_eval "assign_var_copy"
  ``lookup 1 (SND (comp (insert 2 7 LN)
      (Assign 1 (Var 2) : 32 word loopLang$prog)))``
val _ = print_eval "assign_var_kill"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (Assign 1 (Var 2) : 32 word loopLang$prog)))``
val _ = print_eval "assign_expr_kill"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (Assign 1 (Const 9w) : 32 word loopLang$prog)))``
val _ = print_eval "shmem_clears"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (ShMem Load 1 (Const 0w) : 32 word loopLang$prog)))``
val _ = print_eval "load32_kill"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (Load32 0 1 : 32 word loopLang$prog)))``
val _ = print_eval "loadbyte_keep"
  ``lookup 1 (SND (comp LN
      (LoadByte 0 1 : 32 word loopLang$prog)))``
val _ = print_eval "seq_clears"
  ``FST (comp (insert 1 7 LN)
      (Seq (LocValue 2 8) (Assign 3 (Var 2)) : 32 word loopLang$prog))``
val _ = print_eval "if_clears"
  ``FST (comp (insert 1 7 LN)
      ((loopLang$If (Equal : asm$cmp) 0 (Reg 2 : 32 word asm$reg_imm)
        (LocValue 2 8) (Assign 3 (Var 2)) LN) :
        32 word loopLang$prog))``
val _ = print_eval "loop_clears"
  ``FST (comp (insert 1 7 LN)
      ((loopLang$Loop LN (LocValue 2 8) LN) : 32 word loopLang$prog))``
val _ = print_eval "mark_keeps"
  ``lookup 2 (SND (comp (insert 1 7 LN)
      (Mark (LocValue 2 8) : 32 word loopLang$prog)))``
val _ = print_eval "ffi_clears"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (FFI «host» 1 2 3 4 LN : 32 word loopLang$prog)))``
val _ = print_eval "primitive_deletes"
  ``lookup 1 (SND (comp (insert 1 7 (insert 2 8 LN))
      (Primitive [1] AddCarry [2;3] : 32 word loopLang$prog)))``
val _ = print_eval "longmul_deletes"
  ``lookup 1 (SND (comp (insert 1 7 (insert 2 8 LN))
      (Arith (LLongMul 1 2 3 4) : 32 word loopLang$prog)))``
val _ = print_eval "div_deletes"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (Arith (LDiv 1 2 3) : 32 word loopLang$prog)))``
val _ = print_eval "fallback_keeps"
  ``lookup 1 (SND (comp (insert 1 7 LN)
      (Store (Const 0w) 1 : 32 word loopLang$prog)))``
