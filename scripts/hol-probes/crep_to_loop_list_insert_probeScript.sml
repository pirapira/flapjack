load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* list_insert_SNOC (cakeml/pancake/proofs/crep_to_loopProofScript.sml:386):
   list_insert (SNOC x y) l = insert x () (list_insert y l).  Membership is
   observed through lookup at reflexive numeral keys. *)
val _ = print_eval "li_mem_3"
  ``sptree$lookup 3 (sptree$list_insert [3;4] (LN : num_set)) = SOME ()``;
val _ = print_eval "li_mem_4"
  ``sptree$lookup 4 (sptree$list_insert [3;4] (LN : num_set)) = SOME ()``;
val _ = print_eval "li_absent_5"
  ``sptree$lookup 5 (sptree$list_insert [3;4] (LN : num_set)) = NONE``;
val _ = print_eval "li_snoc_mem_5"
  ``sptree$lookup 5 (sptree$list_insert (SNOC 5 [3;4]) (LN : num_set)) = SOME ()``;
val _ = print_eval "li_snoc_agrees"
  ``sptree$lookup 9
      (sptree$list_insert (SNOC 5 [3;4]) (LN : num_set)) =
    sptree$lookup 9
      (sptree$insert 5 () (sptree$list_insert [3;4] (LN : num_set)))``;
