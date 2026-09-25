(* Direct-HOL oracle for the exact pan_commonProps lemmas

     all_distinct_take_frop_disjoint  (pan_commonPropsScript.sml:534)
     disjoint_not_mem_el              (pan_commonPropsScript.sml:606)
     not_mem_fst_zip_flookup_empty    (pan_commonPropsScript.sml:575)

   reproduced in Flapjack/Test/PanCommonPropsZipDisjointParity.lean. *)
load "bossLib";
load "preamble";
load "pan_commonPropsTheory";

open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonPropsTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

val _ = print_eval "atdd_disjoint"
  ``DISJOINT (set (TAKE 2 [1; 2; 3; 4])) (set (DROP 2 [1; 2; 3; 4]))``;

val _ = print_eval "dne_hit" ``~MEM (EL 0 [1; 2]) [3; 4]``;
val _ = print_eval "dne_miss" ``~MEM (EL 1 [1; 2]) [2; 4]``;

val _ = print_eval "nmfz_absent"
  ``FLOOKUP ((FEMPTY |++ ZIP ([1; 2], [10; 20])) : (num, num) fmap) 9 = NONE``;
val _ = print_eval "nmfz_hit"
  ``FLOOKUP ((FEMPTY |++ ZIP ([1; 2], [10; 20])) : (num, num) fmap) 1``;
