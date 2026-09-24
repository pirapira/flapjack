load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `chunk_to_bitmap_def` and `const_words_to_bitmap_def`, the
   bitmap-construction prerequisites of the Word-to-Stack `compile_semantics`
   theorem (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709),
   defined at cakeml/compiler/backend/word_to_stackScript.sml:393-405 and used by
   `comp`'s StoreConsts clause:

     chunk_to_bitmap ws = chunk_to_bits ws :: MAP SND ws

     const_words_to_bitmap (ws:(bool # 'a word) list) (ws_len:num) =
       if ws_len < (dimindex (:'a) - 1) \/ (dimindex (:'a) - 1) = 0
       then chunk_to_bitmap ws
       else chunk_to_bitmap (TAKE (dimindex (:'a) - 1) ws) ++
            const_words_to_bitmap (DROP (dimindex (:'a) - 1) ws)
                                  (ws_len - (dimindex (:'a) - 1))

   Rows cover empty, short, the exact `ws_len = dimindex-1` boundary (strict `<`
   recurses), and a split for `word8` (`dimindex (:'a) = 8`).

   Provenance (bead flapjack-pxn.18.5.15.3.4): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_chunk_to_bitmap_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "cbm_empty"
  ``(word_to_stack$chunk_to_bitmap ([] : (bool # word64) list)) : word64 list``;
val _ = print_eval "cbm_two"
  ``(word_to_stack$chunk_to_bitmap ([(T,0w);(F,9w)] : (bool # word64) list))
       : word64 list``;
val _ = print_eval "cbm_payload"
  ``(word_to_stack$chunk_to_bitmap ([(T,7w)] : (bool # word64) list))
       : word64 list``;
val _ = print_eval "cwb_empty"
  ``(word_to_stack$const_words_to_bitmap ([] : (bool # word64) list) 0)
       : word64 list``;
val _ = print_eval "cwb_short"
  ``(word_to_stack$const_words_to_bitmap
        ([(T,0w);(F,9w)] : (bool # word64) list) 2) : word64 list``;
val _ = print_eval "cwb_boundary8"
  ``(word_to_stack$const_words_to_bitmap
        ([(T,1w);(F,2w);(T,3w);(F,4w);(T,5w);(F,6w);(T,7w)]
           : (bool # word8) list) 7) : word8 list``;
val _ = print_eval "cwb_split8"
  ``(word_to_stack$const_words_to_bitmap
        ([(T,1w);(F,2w);(T,3w);(F,4w);(T,5w);(F,6w);(T,7w);(F,8w)]
           : (bool # word8) list) 8) : word8 list``;
