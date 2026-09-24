load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `insert_bitmap_def`, a bitmap prerequisite of the
   Word-to-Stack `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709),
   defined at cakeml/compiler/backend/word_to_stackScript.sml:246-250:

     insert_bitmap ws (data,data_len) =
       let l = LENGTH ws in ((Append data (List ws), data_len + l), data_len)

   `insert_bitmap` threads the `app_list`/`num` pair built by `write_bitmap`
   into `wLive` (:256) and the `comp` `StoreConsts` clause (:532).  It is fully
   polymorphic in the word element type; here it is instantiated at `num` so the
   `app_list` constructor tree prints concretely.  The result of each row is a
   `(app_list # num) # num` pair; `ib_data_len` / `ib_new_len` project the two
   `num` components.

   Provenance (bead flapjack-pxn.18.5.15.3.6): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_insert_bitmap_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "ib_empty"
  ``(word_to_stack$insert_bitmap ([] : num list) ((misc$Nil : num app_list), 0))
       : (num app_list # num) # num``;
val _ = print_eval "ib_flat"
  ``(word_to_stack$insert_bitmap [1;2;3]
        (((misc$List [9;8]) : num app_list), 5)) : (num app_list # num) # num``;
val _ = print_eval "ib_nested"
  ``(word_to_stack$insert_bitmap [4]
        ((misc$Append (misc$List [1]) (misc$List [2]) : num app_list), 7))
       : (num app_list # num) # num``;
val _ = print_eval "ib_data_len"
  ``SND (word_to_stack$insert_bitmap [1;2;3]
        (((misc$List [9;8]) : num app_list), 5) : (num app_list # num) # num)``;
val _ = print_eval "ib_new_len"
  ``SND (FST (word_to_stack$insert_bitmap [1;2;3]
        (((misc$List [9;8]) : num app_list), 5) : (num app_list # num) # num))``;
