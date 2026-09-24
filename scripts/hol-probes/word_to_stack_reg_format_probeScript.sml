load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the Word-to-Stack register-format helpers used by the
   return/argument path of `comp`, a prerequisite of the `compile_semantics`
   theorem (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709),
   defined at cakeml/compiler/backend/word_to_stackScript.sml:

     wReg1 r (k,f,f') = let r = r DIV 2 in
       if r < k then ([],r) else ([(k,f-1 - (r-k))],k)            (:28-31)
     wReg2 r (k,f,f') = let r = r DIV 2 in
       if r < k then ([],r) else ([(k+1,f-1 - (r-k))],k+1)        (:34-37)
     format_var k NONE = INL (k+1) /\
     format_var k (SOME x) = if x < k then INL x else INR x       (:78-80)

   All three touch only num/bool/option/sum/list with no word operation and no
   `dimindex (:'a)`, so the faithful Lean ports are exactly tagged with no width
   index.

   Provenance (bead flapjack-pxn.18.5.15.3.13/.15): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_reg_format_probeScript.sml \
       scripts/hol-probes/regenerate.sh </dev/null

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "rf_reg1_high"
  ``(word_to_stack$wReg1 8 (3,10,12)) : (num # num) list # num``;
val _ = print_eval "rf_reg1_low"
  ``(word_to_stack$wReg1 2 (3,10,12)) : (num # num) list # num``;
val _ = print_eval "rf_reg2_high"
  ``(word_to_stack$wReg2 8 (3,10,12)) : (num # num) list # num``;
val _ = print_eval "rf_reg2_low"
  ``(word_to_stack$wReg2 4 (3,10,12)) : (num # num) list # num``;
val _ = print_eval "rf_format_var_none"
  ``(word_to_stack$format_var 5 NONE) : (num, num) sum``;
val _ = print_eval "rf_format_var_some_reg"
  ``(word_to_stack$format_var 5 (SOME 2)) : (num, num) sum``;
val _ = print_eval "rf_format_var_some_frame"
  ``(word_to_stack$format_var 5 (SOME 7)) : (num, num) sum``;

(* stack_move / StackArgs (word_to_stackScript.sml:288-297).  Both are
   polymorphic in the word type 'a and touch only Seq/StackLoad/StackStore/
   StackAlloc (num fields); the `prog` results are compared structurally via
   a boolean equality to avoid printing an unprintable word type.  Use
   `stackLang$prog` at a concrete word type (64) so EVAL can reduce. *)

val _ = print_eval "sm_zero"
  ``(word_to_stack$stack_move 0 0 5 3 (stackLang$Skip) : 64 stackLang$prog) =
      (stackLang$Skip)``;
val _ = print_eval "sm_one"
  ``(word_to_stack$stack_move 1 0 5 3 (stackLang$Skip) : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$Skip)
        (stackLang$Seq (stackLang$StackLoad 3 5) (stackLang$StackStore 3 0)))``;
val _ = print_eval "sm_two"
  ``(word_to_stack$stack_move 2 0 5 3 (stackLang$Skip) : 64 stackLang$prog) =
      (stackLang$Seq
        (stackLang$Seq (stackLang$Skip)
          (stackLang$Seq (stackLang$StackLoad 3 6) (stackLang$StackStore 3 1)))
        (stackLang$Seq (stackLang$StackLoad 3 5) (stackLang$StackStore 3 0)))``;
val _ = print_eval "sa_inr"
  ``(word_to_stack$StackArgs (INR 4) 3 (2,7,9) : 64 stackLang$prog) =
      (stackLang$StackAlloc 0)``;
val _ = print_eval "sa_inl"
  ``(word_to_stack$StackArgs (INL 4) 7 (2,7,9) : 64 stackLang$prog) =
      (word_to_stack$stack_move 5 0 7 2 (stackLang$StackAlloc 5))``;

(* wMoveSingle / wMoveAux (word_to_stackScript.sml:62-76).  Both are polymorphic
   in the word type 'a and use only Seq/StackLoad/StackStore plus
   Inst (Arith (Binop Or r1 r2 (Reg r2))) whose Or/Binop/Reg carry num fields;
   the `prog` results are compared structurally via a boolean equality at a
   concrete word type (64) so EVAL can reduce. *)

val _ = print_eval "wms_reg_reg"
  ``(word_to_stack$wMoveSingle (INL 3, INL 5) (2,7,9) : 64 stackLang$prog) =
      (stackLang$Inst (Arith (Binop Or 3 5 (Reg 5))))``;
val _ = print_eval "wms_reg_frame"
  ``(word_to_stack$wMoveSingle (INL 3, INR 5) (2,7,9) : 64 stackLang$prog) =
      (stackLang$StackLoad 3 3)``;
val _ = print_eval "wms_frame_reg"
  ``(word_to_stack$wMoveSingle (INR 3, INL 5) (2,7,9) : 64 stackLang$prog) =
      (stackLang$StackStore 5 5)``;
val _ = print_eval "wms_frame_frame"
  ``(word_to_stack$wMoveSingle (INR 3, INR 5) (2,7,9) : 64 stackLang$prog) =
      (stackLang$Seq (stackLang$StackLoad 2 3) (stackLang$StackStore 2 5))``;
val _ = print_eval "wma_empty"
  ``(word_to_stack$wMoveAux [] (2,7,9) : 64 stackLang$prog) =
      (stackLang$Skip)``;
val _ = print_eval "wma_two"
  ``(word_to_stack$wMoveAux [(INL 3, INL 5); (INR 4, INR 6)] (2,7,9)
      : 64 stackLang$prog) =
      (stackLang$Seq
        (stackLang$Inst (Arith (Binop Or 3 5 (Reg 5))))
        (stackLang$Seq (stackLang$StackLoad 2 2) (stackLang$StackStore 2 4)))``;

