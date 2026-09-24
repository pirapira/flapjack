(* Direct HOL observations for `crep_to_loopProofScript.sml` `mem_rel_def`
   (lines 49-52): `mem_rel smem tmem dom <=> !ad. ad IN dom ==> wlab_wloc (smem ad) = tmem ad`.
   The relation is a universally quantified Prop over the infinite word type, so
   the rows below check its atomic pointwise obligation at a concrete domain
   element (both HOL `loopSem$state.memory` and `crepSem$state.memory` are
   total `'a word -> ...`), mirroring the style of the globals_rel probe.
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

val smem = ``(\ (ad : 8 word). Word (7w : 8 word)) (4w : 8 word)``;
val tmem = ``(\ (ad : 8 word). (Word (7w : 8 word) : 8 word_loc)) (4w : 8 word)``;
val tmemBad = ``(\ (ad : 8 word). (Word (9w : 8 word) : 8 word_loc)) (4w : 8 word)``;
val dom = ``\ (ad : 8 word). ad = (4w : 8 word)``;
val domEmpty = ``\ (ad : 8 word). F``;

val _ = print_eval "mem_rel_match"
  ``case (4w : 8 word) IN ^dom of
      T => (wlab_wloc ^smem = ^tmem)
    | F => T``;
val _ = print_eval "mem_rel_wrong"
  ``case (4w : 8 word) IN ^dom of
      T => (wlab_wloc ^smem = ^tmemBad)
    | F => T``;
val _ = print_eval "mem_rel_out_of_domain"
  ``case (4w : 8 word) IN ^domEmpty of
      T => (wlab_wloc ^smem = ^tmemBad)
    | F => T``;
val _ = print_eval "mem_rel_dom_present"
  ``(4w : 8 word) IN ^dom``;
val _ = print_eval "mem_rel_dom_absent"
  ``(4w : 8 word) IN ^domEmpty``;
