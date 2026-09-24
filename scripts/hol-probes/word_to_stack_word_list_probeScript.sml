load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `word_list_def`, the bitmap-builder prerequisite of the
   Word-to-Stack `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709), defined
   at cakeml/compiler/backend/word_to_stackScript.sml:231-238:

     word_list (xs:bool list) d =
       if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs]
       else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d

   Rows cover the empty list at d>0 and d=0, the d=0 base case, the
   short-list (LENGTH <= d) case, and multi-step partitions.

   Provenance (bead flapjack-pxn.18.5.15.3.2): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_word_list_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "wl_empty_d3"
  ``(word_to_stack$word_list ([] : bool list) 3) : word64 list``;
val _ = print_eval "wl_empty_d0"
  ``(word_to_stack$word_list ([] : bool list) 0) : word64 list``;
val _ = print_eval "wl_d0"
  ``(word_to_stack$word_list [T;F;T] 0) : word64 list``;
val _ = print_eval "wl_short"
  ``(word_to_stack$word_list [T;F;T] 5) : word64 list``;
val _ = print_eval "wl_split"
  ``(word_to_stack$word_list [T;F;T;T] 2) : word64 list``;
val _ = print_eval "wl_twostep"
  ``(word_to_stack$word_list [T;T;T;T;T] 2) : word64 list``;
