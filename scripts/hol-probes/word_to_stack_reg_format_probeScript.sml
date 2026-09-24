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

   Provenance (bead flapjack-pxn.18.5.15.3.13): generated from the Flapjack
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
