load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the perf-mode / handler-slot numeric constants used by the
   Word-to-Stack `raise_stub`/`PushHandler`/`copy_ret` sizing path of the
   `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709),
   defined at cakeml/compiler/backend/word_to_stackScript.sml:

     perf_rsp       = 14n                    (:310)
     perf_rbp       = 15n                    (:315)
     handler_slots perf = if perf then 5n else 3n   (:346)

   All three are pure `num`/`bool` with no word operation and no
   `dimindex (:'a)`, so the faithful Lean ports are monomorphic and exact.

   Provenance (bead flapjack-pxn.18.5.15.3.8): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `word_to_stackTheory`
   is prebuilt in flapjack2/3/4/6 (not flapjack7), so the oracle checkout is
   flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=word_to_stack_perf_slots_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/word_to_stackScript.sml are byte-identical
   (sha256 3b487de8259affbf...). *)

val _ = print_eval "ps_perf_rsp"
  ``(word_to_stack$perf_rsp) : num``;
val _ = print_eval "ps_perf_rbp"
  ``(word_to_stack$perf_rbp) : num``;
val _ = print_eval "ps_handler_slots_true"
  ``(word_to_stack$handler_slots T) : num``;
val _ = print_eval "ps_handler_slots_false"
  ``(word_to_stack$handler_slots F) : num``;
