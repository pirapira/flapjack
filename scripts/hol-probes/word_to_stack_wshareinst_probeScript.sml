load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the Word-to-Stack shared-memory instruction helper used by
   `comp` and hence the `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709).
   Defined at cakeml/compiler/backend/word_to_stackScript.sml:186-224:

     (wShareInst Load   v (Addr ad offset) kf =
        let (l,n2) = wReg1 ad kf in
          wStackLoad l (wRegWrite1 (\r. ShMemOp Load r (Addr n2 offset)) v kf)) /\
     ... Load8/Load16/Load32 likewise ...
     (wShareInst Store  v (Addr ad offset) kf =
        let (l1,n2) = wReg1 ad kf in
        let (l2,n1) = wReg2 v kf in
          wStackLoad (l1 ++ l2) (ShMemOp Store n1 (Addr n2 offset))) /\
     ... Store8/Store16/Store32 likewise ...

   HOL is polymorphic in the stack word type 'a; the results are compared
   structurally via boolean equality at a concrete word type (64) so EVAL can
   reduce (the address offset is a 64-bit word).

   Provenance (bead flapjack-pxn.18.5.15.3.22): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_wshareinst_probeScript.sml \
       scripts/hol-probes/regenerate.sh </dev/null

   `word_to_stackTheory` is prebuilt in flapjack2/3/4/6 (not flapjack7).
   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f23338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "ws_load"
  ``(word_to_stack$wShareInst asm$Load 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$ShMemOp asm$Load 2 (asm$Addr 1 (9w : 64 word)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "ws_load8"
  ``(word_to_stack$wShareInst asm$Load8 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$ShMemOp asm$Load8 2 (asm$Addr 1 (9w : 64 word)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "ws_load16"
  ``(word_to_stack$wShareInst asm$Load16 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$ShMemOp asm$Load16 2 (asm$Addr 1 (9w : 64 word)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "ws_load32"
  ``(word_to_stack$wShareInst asm$Load32 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$ShMemOp asm$Load32 2 (asm$Addr 1 (9w : 64 word)))
        (stackLang$StackStore 2 6))``;
val _ = print_eval "ws_store"
  ``(word_to_stack$wShareInst asm$Store 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$ShMemOp asm$Store 3 (asm$Addr 1 (9w : 64 word))))``;
val _ = print_eval "ws_store8"
  ``(word_to_stack$wShareInst asm$Store8 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$ShMemOp asm$Store8 3 (asm$Addr 1 (9w : 64 word))))``;
val _ = print_eval "ws_store16"
  ``(word_to_stack$wShareInst asm$Store16 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$ShMemOp asm$Store16 3 (asm$Addr 1 (9w : 64 word))))``;
val _ = print_eval "ws_store32"
  ``(word_to_stack$wShareInst asm$Store32 5 (asm$Addr 3 (9w : 64 word)) (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 3 6)
        (stackLang$ShMemOp asm$Store32 3 (asm$Addr 1 (9w : 64 word))))``;
