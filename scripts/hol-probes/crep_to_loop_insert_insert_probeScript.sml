load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* insert_insert_eq (cakeml/pancake/proofs/crep_to_loopProofScript.sml:380):
   insert a b (insert a b c) = insert a b c.  Observed by lookup at the
   inserted key (empty and non-empty trees), at a neighbouring key, and by
   agreement with the single insert. *)
val _ = print_eval "iie_hit"
  ``sptree$lookup 5 (sptree$insert 5 7 (sptree$insert 5 7 (LN : num spt))) = SOME 7``;
val _ = print_eval "iie_hit_deep"
  ``sptree$lookup 11
      (sptree$insert 11 7 (sptree$insert 11 7 (sptree$insert 5 3 (LN : num spt)))) = SOME 7``;
val _ = print_eval "iie_other"
  ``sptree$lookup 5
      (sptree$insert 11 7 (sptree$insert 11 7 (sptree$insert 5 1 (LN : num spt)))) = SOME 1``;
val _ = print_eval "iie_absent"
  ``sptree$lookup 4 (sptree$insert 5 7 (sptree$insert 5 7 (LN : num spt))) = NONE``;
val _ = print_eval "iie_agrees_empty"
  ``sptree$lookup 5 (sptree$insert 5 7 (sptree$insert 5 7 (LN : num spt))) =
    sptree$lookup 5 (sptree$insert 5 7 (LN : num spt))``;
val _ = print_eval "iie_agrees_deep"
  ``sptree$lookup 11
      (sptree$insert 11 7 (sptree$insert 11 7 (sptree$insert 5 3 (LN : num spt)))) =
    sptree$lookup 11
      (sptree$insert 11 7 (sptree$insert 5 3 (LN : num spt)))``;
