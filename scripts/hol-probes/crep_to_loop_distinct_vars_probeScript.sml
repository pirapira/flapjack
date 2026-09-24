(* Direct HOL observations for `crep_to_loopProofScript.sml` `distinct_vars_def`
   (lines 95-99):
     distinct_vars fm <=> !x y n m.
       FLOOKUP fm x = SOME n /\ FLOOKUP fm y = SOME m /\ n = m ==> x = y
   The relation is a universally quantified Prop over num keys, so the rows below
   evaluate its atomic pointwise obligation at concrete key pairs (the body at a
   fixed (x,y)), in the same style as the distinct_funcs / globals_rel probes.
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

(* keys 1 and 2 carry distinct slots 10 and 20; keys 1 and 3 collide on slot 10. *)
val vmSep = ``((FEMPTY |+ ((1:num), (10:num)) |+ ((2:num), (20:num)))
                : (num, num) fmap)``;
val vmCol = ``((FEMPTY |+ ((1:num), (10:num)) |+ ((3:num), (10:num)))
                : (num, num) fmap)``;

val _ = print_eval "distinct_vars_sep"
  ``case (FLOOKUP ^vmSep (1:num), FLOOKUP ^vmSep (2:num)) of
      (SOME n, SOME m) => (n = m ==> ((1:num) = (2:num)))
    | _ => T``;
val _ = print_eval "distinct_vars_collision"
  ``case (FLOOKUP ^vmCol (1:num), FLOOKUP ^vmCol (3:num)) of
      (SOME n, SOME m) => (n = m ==> ((1:num) = (3:num)))
    | _ => T``;
val _ = print_eval "distinct_vars_absent"
  ``case (FLOOKUP ^vmSep (1:num), FLOOKUP ^vmSep (9:num)) of
      (SOME n, SOME m) => (n = m ==> ((1:num) = (9:num)))
    | _ => T``;