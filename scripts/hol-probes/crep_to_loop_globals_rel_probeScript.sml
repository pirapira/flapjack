(* Direct HOL observations for `crep_to_loopProofScript.sml`
   `wlab_wloc_def` (lines 45-47) and `globals_rel_def` (lines 54-58).

   `wlab_wloc (panSem$Word w) = wordLang$Word w` maps a source `word_lab` to a
   target `word_loc`; `globals_rel` states that every source global lookup is
   matched by the target's `wlab_wloc` image.  `globals_rel` itself is a
   universally quantified Prop over the infinite word type, so the rows below
   check its atomic lookup obligations on concrete finite maps instead.
*)
load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val sglobals = ``((FEMPTY : 5 word |-> 8 word_lab) |+ (4w, Word (7w : 8 word)))``;
val tglobals = ``((FEMPTY : 5 word |-> 8 word_loc) |+ (4w, Word (7w : 8 word)))``;
val tglobalsBad = ``((FEMPTY : 5 word |-> 8 word_loc) |+ (4w, Word (9w : 8 word)))``;

val _ = print_eval "wlab_wloc_word"
  ``wlab_wloc (Word (7w : 8 word)) = (Word (7w : 8 word) : 8 word_loc)``;
val _ = print_eval "globals_lookup_match"
  ``case FLOOKUP ^sglobals 4w of
      SOME v => FLOOKUP ^tglobals 4w = SOME (wlab_wloc v)
    | NONE => T``;
val _ = print_eval "globals_lookup_wrong"
  ``case FLOOKUP ^sglobals 4w of
      SOME v => FLOOKUP ^tglobalsBad 4w = SOME (wlab_wloc v)
    | NONE => T``;
val _ = print_eval "globals_lookup_absent"
  ``FLOOKUP ^sglobals 9w = NONE``;
