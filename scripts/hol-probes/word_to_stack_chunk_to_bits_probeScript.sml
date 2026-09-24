load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `chunk_to_bits_def`, the bitmap-builder prerequisite of the
   Word-to-Stack `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709), defined
   at cakeml/compiler/backend/word_to_stackScript.sml:386-391:

     chunk_to_bits ([] : (bool # 'a word) list) = 1w /\
     chunk_to_bits ((b,w)::ws) =
       let res = (chunk_to_bits ws) << 1 in if b then res + 1w else res

   Rows cover the empty list, single true/false tags, mixed tags, a three-bit
   chunk, and the fact that the word payload `w` is ignored.

   Provenance (bead flapjack-pxn.18.5.15.3.3): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_chunk_to_bits_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "cb_empty"
  ``(word_to_stack$chunk_to_bits ([] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_single_true"
  ``(word_to_stack$chunk_to_bits ([(T,0w)] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_single_false"
  ``(word_to_stack$chunk_to_bits ([(F,0w)] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_true_false"
  ``(word_to_stack$chunk_to_bits ([(T,0w);(F,0w)] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_false_true"
  ``(word_to_stack$chunk_to_bits ([(F,0w);(T,0w)] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_three"
  ``(word_to_stack$chunk_to_bits ([(T,0w);(T,0w);(F,0w)] : (bool # word64) list)) : word64``;
val _ = print_eval "cb_ignores_word"
  ``(word_to_stack$chunk_to_bits ([(T,0w);(F,9w)] : (bool # word64) list))
       = chunk_to_bits ([(T,0w);(F,0w)] : (bool # word64) list)``;
