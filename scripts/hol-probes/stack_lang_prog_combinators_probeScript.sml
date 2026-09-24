load "bossLib";
load "preamble";
load "stackLangTheory";
load "word_to_stackTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the word-independent stackLang / Word-to-Stack program
   combinators that build the exact `stackLang$prog` consumed by `wLive` and the
   later stubs of the `compile_semantics` theorem
   (cakeml/compiler/backend/proofs/word_to_stackProofScript.sml:10709):

     list_Seq_def     (cakeml/compiler/backend/stackLangScript.sml:86)
       (list_Seq [] = Skip) /\
       (list_Seq [x] = x) /\
       (list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))

     SeqStackFree_def (cakeml/compiler/backend/word_to_stackScript.sml:260)
       SeqStackFree n p = if n = 0 then p else Seq (StackFree n) p

     wStackLoad_def   (cakeml/compiler/backend/word_to_stackScript.sml:52)
       (wStackLoad [] x = x) /\
       (wStackLoad ((r,i)::ps) x = Seq (StackLoad r i) (wStackLoad ps x))

     wStackStore_def  (cakeml/compiler/backend/word_to_stackScript.sml:57)
       (wStackStore [] x = x) /\
       (wStackStore ((r,i)::ps) x = Seq (wStackStore ps x) (StackStore r i))

   All four are polymorphic in the word type `'a` and touch only the
   word-independent Skip/Seq/StackFree/StackLoad/StackStore constructors (whose
   fields are `num`), so the faithful Lean ports are polymorphic over the
   carrier's type parameters and exact.

   Provenance (bead flapjack-pxn.18.5.15.3.9): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout.  `stackLangTheory`
   and `word_to_stackTheory` are prebuilt in flapjack2/3/4/6 (not flapjack7), so
   the oracle checkout is flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=stack_lang_prog_combinators_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   compiler/backend/stackLangScript.sml and
   compiler/backend/word_to_stackScript.sml (sha256 3b487de8259affbf...) are
   byte-identical. *)

val _ = print_eval "lc_empty"
  ``(stackLang$list_Seq ([] : word64 stackLang$prog list)) : word64 stackLang$prog``;
val _ = print_eval "lc_one"
  ``(stackLang$list_Seq [stackLang$Skip]) : word64 stackLang$prog``;
val _ = print_eval "lc_two"
  ``(stackLang$list_Seq [stackLang$Skip; stackLang$StackFree 1]) : word64 stackLang$prog``;
val _ = print_eval "lc_three"
  ``(stackLang$list_Seq [stackLang$Skip; stackLang$StackFree 1; stackLang$Skip]) : word64 stackLang$prog``;
val _ = print_eval "ssf_zero"
  ``(word_to_stack$SeqStackFree 0 stackLang$Skip) : word64 stackLang$prog``;
val _ = print_eval "ssf_two"
  ``(word_to_stack$SeqStackFree 2 stackLang$Skip) : word64 stackLang$prog``;
val _ = print_eval "wsl_empty"
  ``(word_to_stack$wStackLoad ([] : (num # num) list) stackLang$Skip) : word64 stackLang$prog``;
val _ = print_eval "wsl_two"
  ``(word_to_stack$wStackLoad [(1,2);(3,4)] stackLang$Skip) : word64 stackLang$prog``;
val _ = print_eval "wss_two"
  ``(word_to_stack$wStackStore [(1,2);(3,4)] stackLang$Skip) : word64 stackLang$prog``;
