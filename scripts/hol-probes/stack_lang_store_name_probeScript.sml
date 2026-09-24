load "bossLib";
load "preamble";
load "stackLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `stackLang$store_name` datatype
   (cakeml/compiler/backend/stackLangScript.sml:18-25):

     store_name =
       NextFree | EndOfHeap | TriggerGC | HeapLength | ProgStart | BitmapBase |
       CurrHeap | OtherHeap | AllocSize | Globals | GlobReal | Handler | GenStart |
       CodeBuffer | CodeBufferEnd | BitmapBuffer | BitmapBufferEnd |
       Temp (5 word)

   `store_name` is monomorphic in HOL and its only payload is the fixed 5-bit
   `Temp` field, so the faithful Lean `StoreName` inductive is shape-exact
   (bead flapjack-pxn.18.5.15.3.10).  The rows below exercise every
   constructor name and pin the `Temp` field to a 5-bit word.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout.  `stackLangTheory` is prebuilt in flapjack2/3/4/6, so
   the oracle checkout is flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=stack_lang_store_name_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val all_store_names =
  ``[stackLang$NextFree; stackLang$EndOfHeap; stackLang$TriggerGC;
     stackLang$HeapLength; stackLang$ProgStart; stackLang$BitmapBase;
     stackLang$CurrHeap; stackLang$OtherHeap; stackLang$AllocSize;
     stackLang$Globals; stackLang$GlobReal; stackLang$Handler;
     stackLang$GenStart; stackLang$CodeBuffer; stackLang$CodeBufferEnd;
     stackLang$BitmapBuffer; stackLang$BitmapBufferEnd;
     stackLang$Temp (3w : 5 word)] : stackLang$store_name list``;

val _ = print_eval "sn_count" ``LENGTH ^all_store_names : num``;
val _ = print_eval "sn_temp_eq"
  ``((stackLang$Temp (3w : 5 word) : stackLang$store_name)
      = stackLang$Temp (3w : 5 word))``;
val _ = print_eval "sn_temp_ne"
  ``((stackLang$Temp (3w : 5 word) : stackLang$store_name)
      = stackLang$Temp (4w : 5 word))``;
val _ = print_eval "sn_find"
  ``MEM (stackLang$Temp (3w : 5 word) : stackLang$store_name)
       [stackLang$NextFree; stackLang$Temp (3w : 5 word); stackLang$Handler]``;
val _ = print_eval "sn_absent"
  ``MEM (stackLang$Temp (3w : 5 word) : stackLang$store_name)
       [stackLang$NextFree; stackLang$Temp (4w : 5 word); stackLang$Handler]``;
val _ = print_eval "sn_temp_w2n" ``w2n (3w : 5 word) : num``;
val _ = print_eval "sn_temp_word_bits" ``(w2n (31w : 5 word) : num)``;
