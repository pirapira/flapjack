(* Direct HOL observations for `crep_to_loopProofScript.sml` `distinct_funcs_def`
   (lines 60-65):
     distinct_funcs fm <=> !x y n m rm rm'.
       FLOOKUP fm x = SOME (n,rm) /\ FLOOKUP fm y = SOME (m,rm') /\ n = m ==> x = y
   The relation is a universally quantified Prop over mlstring, so the rows below
   evaluate its atomic pointwise obligation at concrete key pairs (the body at a
   fixed (x,y)), in the same style as the globals_rel / mem_rel probes.
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

(* «a» and «b» carry distinct labels 1 and 2; «a» and «c» collide on label 1. *)
val fmSep = ``((FEMPTY |+ («a», ((1:num), (10:num))) |+ («b», ((2:num), (20:num))))
                : (mlstring, num # num) fmap)``;
val fmCol = ``((FEMPTY |+ («a», ((1:num), (10:num))) |+ («c», ((1:num), (30:num))))
                : (mlstring, num # num) fmap)``;

val _ = print_eval "distinct_funcs_sep"
  ``case (FLOOKUP ^fmSep «a», FLOOKUP ^fmSep «b») of
      (SOME (n, rm), SOME (m, rm')) => (n = m ==> («a» = «b»))
    | _ => T``;
val _ = print_eval "distinct_funcs_collision"
  ``case (FLOOKUP ^fmCol «a», FLOOKUP ^fmCol «c») of
      (SOME (n, rm), SOME (m, rm')) => (n = m ==> («a» = «c»))
    | _ => T``;
val _ = print_eval "distinct_funcs_absent"
  ``case (FLOOKUP ^fmSep «a», FLOOKUP ^fmSep «z») of
      (SOME (n, rm), SOME (m, rm')) => (n = m ==> («a» = «z»))
    | _ => T``;
