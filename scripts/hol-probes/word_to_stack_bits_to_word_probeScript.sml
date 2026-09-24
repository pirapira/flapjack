load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `bits_to_word_def`, the pure bitmap prerequisite of the
   Word-to-Stack `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709), defined
   at cakeml/compiler/backend/word_to_stackScript.sml:225-229.

   The last row re-checks the second defining equation on a small input.

   Provenance (bead flapjack-pxn.18.5.15.3.1): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_bits_to_word_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "bits_empty" ``(word_to_stack$bits_to_word ([] : bool list)) : word64``;
val _ = print_eval "bits_true" ``(word_to_stack$bits_to_word [T]) : word64``;
val _ = print_eval "bits_false" ``(word_to_stack$bits_to_word [F]) : word64``;
val _ = print_eval "bits_true_false_true" ``(word_to_stack$bits_to_word [T;F;T]) : word64``;
val _ = print_eval "bits_all_true_3" ``(word_to_stack$bits_to_word [T;T;T]) : word64``;
val _ = print_eval "bits_pattern" ``(word_to_stack$bits_to_word [F;T;F;F;T]) : word64``;
val _ = print_eval "bits_equation"
  ``word_to_stack$bits_to_word [T;F] = (word_to_stack$bits_to_word [F] << 1 || 1w)``;
