load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the pure stack-slot arithmetic helpers used by the
   Word-to-Stack `comp`/`StackArgs` path of the `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709),
   defined at cakeml/compiler/backend/word_to_stackScript.sml:

     num_stack_ret k vs       = LENGTH vs + 1 - k                       (:417)
     skip_free (k,f,f') vs    = f - num_stack_ret k vs                  (:423)
     stack_arg_count dest ac k = case dest of
                                   INL _ => ac - k
                                 | INR _ => (ac - 1) - k                (:274)
     stack_free dest ac (k,f,f') = f - stack_arg_count dest ac k        (:281)

   All four are pure `num`/`sum` arithmetic with no word operation and no
   `dimindex (:'a)`, so the faithful Lean ports are the generic bodies below
   with no width specialisation.  The rows cover both `sum` branches and the
   truncating `num` subtraction.

   Provenance (bead flapjack-pxn.18.5.15.3.7): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_stack_slots_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "ss_num_stack_ret_pair"
  ``(word_to_stack$num_stack_ret 1 [10;20]) : num``;
val _ = print_eval "ss_num_stack_ret_three"
  ``(word_to_stack$num_stack_ret 3 [10;20;30]) : num``;
val _ = print_eval "ss_skip_free_pair"
  ``(word_to_stack$skip_free (1,7,9) [10;20]) : num``;
val _ = print_eval "ss_arg_count_inl"
  ``(word_to_stack$stack_arg_count (INL 4 : (num, num) sum) 7 2) : num``;
val _ = print_eval "ss_arg_count_inr"
  ``(word_to_stack$stack_arg_count (INR 4 : (num, num) sum) 7 2) : num``;
val _ = print_eval "ss_stack_free_inr"
  ``(word_to_stack$stack_free (INR 4 : (num, num) sum) 7 (2,7,9)) : num``;
val _ = print_eval "ss_stack_free_inl"
  ``(word_to_stack$stack_free (INL 4 : (num, num) sum) 7 (2,7,9)) : num``;
