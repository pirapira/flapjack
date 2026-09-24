load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the Word-to-Stack return-copy helpers `copy_ret_aux` and
   `copy_ret`, prerequisite of the `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709):

     (copy_ret_aux k f n =
        if n = 0 then Skip
        else let n' = n-1 in
          list_Seq [StackLoad k n'; StackStore k (n'+f); copy_ret_aux k f n'])
     copy_ret perf is_handle (k,f,f') vs kont =
       let n = num_stack_ret k vs in
       if n = 0 then kont
       else Seq (copy_ret_aux k (if is_handle then f + handler_slots perf else f) n)
                (SeqStackFree n kont)

   defined at cakeml/compiler/backend/word_to_stackScript.sml:429-451.  These
   touch only Seq/StackLoad/StackStore/StackFree/list_Seq with num fields, so
   they are word-independent and the faithful Lean ports are exact over the
   shared-word stackLang prog carrier.

   Provenance (bead flapjack-pxn.18.5.15.3.16): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_copy_ret_probeScript.sml \
       scripts/hol-probes/regenerate.sh </dev/null

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 prefix 3b487de8259affbf). *)

val _ = print_eval "cra_zero"
  ``(word_to_stack$copy_ret_aux 3 2 0 : 64 stackLang$prog) = (stackLang$Skip)``;
val _ = print_eval "cra_one"
  ``(word_to_stack$copy_ret_aux 3 2 1 : 64 stackLang$prog) =
      (stackLang$list_Seq
        [stackLang$StackLoad 3 0; stackLang$StackStore 3 2; stackLang$Skip])``;
val _ = print_eval "cra_two"
  ``(word_to_stack$copy_ret_aux 3 2 2 : 64 stackLang$prog) =
      (stackLang$list_Seq
        [stackLang$StackLoad 3 1; stackLang$StackStore 3 3;
         stackLang$list_Seq
           [stackLang$StackLoad 3 0; stackLang$StackStore 3 2; stackLang$Skip]])``;
val _ = print_eval "cr_zero"
  ``(word_to_stack$copy_ret F F (2,7,9) [] (stackLang$Skip) : 64 stackLang$prog) =
      (stackLang$Skip)``;
val _ = print_eval "cr_plain"
  ``(word_to_stack$copy_ret F F (2,7,9) [10;20;30] (stackLang$Skip)
      : 64 stackLang$prog) =
      (stackLang$Seq
        (stackLang$list_Seq
          [stackLang$StackLoad 2 1; stackLang$StackStore 2 8;
           stackLang$list_Seq
             [stackLang$StackLoad 2 0; stackLang$StackStore 2 7; stackLang$Skip]])
        (stackLang$Seq (stackLang$StackFree 2) (stackLang$Skip)))``;
val _ = print_eval "cr_handle"
  ``(word_to_stack$copy_ret F T (2,7,9) [10;20;30] (stackLang$Skip)
      : 64 stackLang$prog) =
      (stackLang$Seq
        (stackLang$list_Seq
          [stackLang$StackLoad 2 1; stackLang$StackStore 2 11;
           stackLang$list_Seq
             [stackLang$StackLoad 2 0; stackLang$StackStore 2 10; stackLang$Skip]])
        (stackLang$Seq (stackLang$StackFree 2) (stackLang$Skip)))``;