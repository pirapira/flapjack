(* Direct HOL observations for `crep_to_loopProofScript.sml` `ctxt_max_def`
   (lines 90-93):
     ctxt_max (n:num) fm <=> !v m. FLOOKUP fm v = SOME m ==> m <= n
   The relation is a universally quantified Prop over num keys, so the rows below
   evaluate its atomic pointwise obligation at a concrete key, in the same style
   as the distinct_funcs / distinct_vars probes.
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

(* key 1 carries slot 10; bound 20 admits it, bound 5 does not. *)
val vm = ``((FEMPTY |+ ((1:num), (10:num))) : (num, num) fmap)``;

val _ = print_eval "ctxt_max_within"
  ``case FLOOKUP ^vm (1:num) of
      SOME m => (m <= (20:num))
    | NONE => T``;
val _ = print_eval "ctxt_max_exceeds"
  ``case FLOOKUP ^vm (1:num) of
      SOME m => (m <= (5:num))
    | NONE => T``;
val _ = print_eval "ctxt_max_absent"
  ``case FLOOKUP ^vm (9:num) of
      SOME m => (m <= (5:num))
    | NONE => T``;