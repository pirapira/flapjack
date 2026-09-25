load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* list_insert_insert (cakeml/pancake/proofs/crep_to_loopProofScript.sml:406):
   insert x () (list_insert xs l) = list_insert xs (insert x () l).  Observed
   both by direct tree equality (non-member and member key) and by lookup. *)
val _ = print_eval "lii_ty_nonmember"
  ``sptree$insert 5 () (sptree$list_insert [3;4] (LN : num_set)) =
    sptree$list_insert [3;4] (sptree$insert 5 () (LN : num_set))``;
val _ = print_eval "lii_ty_member"
  ``sptree$insert 3 () (sptree$list_insert [3;4] (LN : num_set)) =
    sptree$list_insert [3;4] (sptree$insert 3 () (LN : num_set))``;
val _ = print_eval "lii_lookup_new"
  ``sptree$lookup 5 (sptree$insert 5 () (sptree$list_insert [3;4] (LN : num_set))) = SOME ()``;
val _ = print_eval "lii_lookup_mem"
  ``sptree$lookup 4 (sptree$insert 5 () (sptree$list_insert [3;4] (LN : num_set))) = SOME ()``;
val _ = print_eval "lii_absent"
  ``sptree$lookup 7 (sptree$insert 5 () (sptree$list_insert [3;4] (LN : num_set))) = NONE``;

(* list_insert_append (cakeml/pancake/proofs/crep_to_loopProofScript.sml:414):
   list_insert (xs ++ ys) l = list_insert xs (list_insert ys l).  Observed by
   direct tree equality and by lookup at member and absent keys. *)
val _ = print_eval "lia_ty"
  ``sptree$list_insert ([3;4] ++ [5;6]) (LN : num_set) =
    sptree$list_insert [3;4] (sptree$list_insert [5;6] (LN : num_set))``;
val _ = print_eval "lia_lookup_new"
  ``sptree$lookup 6 (sptree$list_insert ([3;4] ++ [5;6]) (LN : num_set)) = SOME ()``;
val _ = print_eval "lia_lookup_first"
  ``sptree$lookup 3 (sptree$list_insert ([3;4] ++ [5;6]) (LN : num_set)) = SOME ()``;
val _ = print_eval "lia_absent"
  ``sptree$lookup 7 (sptree$list_insert ([3;4] ++ [5;6]) (LN : num_set)) = NONE``;
