load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the Word-to-Stack instruction helper used by `comp` and
   hence the `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709).
   Defined at cakeml/compiler/backend/word_to_stackScript.sml:88-175.

   HOL is polymorphic in the stack word type 'a; the results are compared
   structurally via boolean equality at a concrete word type (64) so EVAL can
   reduce.  `inst` is `asm$inst` (Const/Arith/Mem/FP/Skip) and the result is a
   `stackLang$prog`.  `Mem Load16`/`Mem Store16` are intentionally unhandled by
   HOL and fall to the `Skip` catch-all; the rows below pin that.

   Provenance (bead flapjack-pxn.18.5.15.3.23): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_winst_probeScript.sml \
       scripts/hol-probes/regenerate.sh </dev/null

   `word_to_stackTheory` is prebuilt in flapjack2/3/4/6 (not flapjack7).
   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f23338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "wi_const"
  ``(word_to_stack$wInst (asm$Const 7 (5w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$Inst (asm$Const 2 (5w : 64 word)))
        (stackLang$StackStore 2 5))``;
val _ = print_eval "wi_binop_imm"
  ``(word_to_stack$wInst (asm$Arith (asm$Binop asm$Add 4 3 (asm$Imm (9w : 64 word)))) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq
        (stackLang$Inst (asm$Arith (asm$Binop asm$Add 2 1 (asm$Imm (9w : 64 word)))))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "wi_binop_reg"
  ``(word_to_stack$wInst (asm$Arith (asm$Binop asm$Add 4 3 (asm$Reg 5))) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$Seq
          (stackLang$Inst (asm$Arith (asm$Binop asm$Add 2 1 (asm$Reg 3))))
          (stackLang$StackStore 2 6)))``;
val _ = print_eval "wi_div"
  ``(word_to_stack$wInst (asm$Arith (asm$Div 4 3 5)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$Seq (stackLang$Inst (asm$Arith (asm$Div 2 1 3)))
          (stackLang$StackStore 2 6)))``;
val _ = print_eval "wi_addcarry"
  ``(word_to_stack$wInst (asm$Arith (asm$AddCarry 4 3 5 6)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$Seq (stackLang$Inst (asm$Arith (asm$AddCarry 2 1 3 6)))
          (stackLang$StackStore 2 6)))``;
val _ = print_eval "wi_longmul"
  ``(word_to_stack$wInst (asm$Arith (asm$LongMul 1 2 3 4)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Inst (asm$Arith (asm$LongMul 3 0 0 2)))``;
val _ = print_eval "wi_longdiv"
  ``(word_to_stack$wInst (asm$Arith (asm$LongDiv 1 2 3 4 5)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 2 6)
        (stackLang$Inst (asm$Arith (asm$LongDiv 0 3 3 0 2))))``;
val _ = print_eval "wi_load16_skip"
  ``(word_to_stack$wInst (asm$Mem asm$Load16 4 (asm$Addr 3 (9w : 64 word))) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Inst asm$Skip)``;
val _ = print_eval "wi_store"
  ``(word_to_stack$wInst (asm$Mem asm$Store 4 (asm$Addr 3 (9w : 64 word))) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$Inst (asm$Mem asm$Store 3 (asm$Addr 1 (9w : 64 word)))))``;
val _ = print_eval "wi_fpless"
  ``(word_to_stack$wInst (asm$FP (asm$FPLess 4 1 2)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$Inst (asm$FP (asm$FPLess 2 1 2)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "wi_fpmovtoreg"
  ``(word_to_stack$wInst (asm$FP (asm$FPMovToReg 4 3 0)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$Inst (asm$FP (asm$FPMovToReg 2 0 0)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "wi_fpmovfromreg"
  ``(word_to_stack$wInst (asm$FP (asm$FPMovFromReg 0 4 3)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 2 6)
        (stackLang$Inst (asm$FP (asm$FPMovFromReg 0 2 0))))``;
val _ = print_eval "wi_fpadd"
  ``(word_to_stack$wInst (asm$FP (asm$FPAdd 1 2 3)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Inst (asm$FP (asm$FPAdd 1 2 3)))``;
val _ = print_eval "wi_skip"
  ``(word_to_stack$wInst asm$Skip (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Inst asm$Skip)``;
