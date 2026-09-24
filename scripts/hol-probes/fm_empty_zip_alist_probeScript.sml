(* Direct HOL-EVAL observations for the `fm_empty_zip_alist` finite-map/list
   lemma that the Lean port in Flapjack/Pancake/Semantics/PanCommonProps.lean
   must match.

   Reference:
     cakeml/pancake/semantics/pan_commonPropsScript.sml:
       fm_empty_zip_alist (:426)
         !xs ys. LENGTH xs = LENGTH ys /\ ALL_DISTINCT xs ==>
                 FEMPTY |++ ZIP(xs,ys) = alist_to_fmap (ZIP(xs,ys))

   The rows pin the fold/fmap equality and first/absent lookups on concrete
   duplicate-free keys.
*)
load "bossLib";
load "preamble";
load "pan_commonPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open alistTheory;
open finite_mapTheory;
open pan_commonPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=" ^ term_to_string (rhs (concl th)) ^ "\n")
  end;

val xs = ``[1; 2; 3] : num list``;
val ys = ``[10; 20; 30] : num list``;

val _ = print_eval "fold_flookup_eq"
  (``FLOOKUP ((FEMPTY |++ ZIP(^xs, ^ys)) : (num, num) fmap) 2 =
      FLOOKUP (alist_to_fmap (ZIP(^xs, ^ys))) 2``);

val _ = print_eval "flookup_first"
  (``FLOOKUP ((FEMPTY |++ ZIP(^xs, ^ys)) : (num, num) fmap) 2``);

val _ = print_eval "flookup_absent"
  (``FLOOKUP ((FEMPTY |++ ZIP(^xs, ^ys)) : (num, num) fmap) 9``);

val _ = print_eval "zip_lookup_witness"
  (``case FLOOKUP ((FEMPTY |++ ZIP(^xs, ^ys)) : (num, num) fmap) 3 of
      SOME y => (EL 2 (ZIP(^xs,^ys)) = (3,y))
    | NONE => F``);
