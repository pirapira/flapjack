(* Audit of HOL num_set (misc$num_set = unit spt) and sptree$toAList
   enumeration/duplicate/wf behaviour, versus the Flapjack carrier
   WordLangNumSet = FiniteMap Nat Unit (Nat -> Option Unit).

   Used by bead flapjack-pxn.18.5.15.1.5 (num_set carrier audit). *)
load "preamble";
load "miscTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open miscTheory;

val print_eval = fn label => fn q =>
  (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");

(* toAList enumeration: empty, single, insertion-order dependence *)
val _ = print_eval "ns_empty" ``sptree$toAList (LN : unit spt)``;
val _ = print_eval "ns_single" ``sptree$toAList (sptree$insert 0 () (LN : unit spt))``;
val _ = print_eval "ns_three_fwd"
  ``sptree$toAList (sptree$insert 2 () (sptree$insert 1 () (sptree$insert 0 () (LN : unit spt))))``;
val _ = print_eval "ns_three_rev"
  ``sptree$toAList (sptree$insert 0 () (sptree$insert 1 () (sptree$insert 2 () (LN : unit spt))))``;

(* duplicates: insert twice and union of the same singleton *)
val _ = print_eval "ns_insert_dup"
  ``sptree$toAList (sptree$insert 0 () (sptree$insert 0 () (LN : unit spt)))``;
val _ = print_eval "ns_union_dup"
  ``sptree$toAList (sptree$union (sptree$insert 0 () (LN : unit spt))
                                 (sptree$insert 0 () (LN : unit spt)))``;

(* membership and well-formedness *)
val _ = print_eval "ns_mem_yes"
  ``MEM 0 (MAP FST (sptree$toAList (sptree$insert 0 () (LN : unit spt))))``;
val _ = print_eval "ns_mem_no"
  ``MEM 1 (MAP FST (sptree$toAList (sptree$insert 0 () (LN : unit spt))))``;
val _ = print_eval "ns_wf_empty" ``sptree$wf (LN : unit spt)``;
val _ = print_eval "ns_wf_insert"
  ``sptree$wf (sptree$insert 0 () (LN : unit spt))``;
val _ = print_eval "ns_wf_union"
  ``sptree$wf (sptree$union (sptree$insert 0 () (LN : unit spt))
                            (sptree$insert 1 () (LN : unit spt)))``;

(* every_name-shaped: EVERY P (MAP FST (toAList t)) is order-insensitive *)
val _ = print_eval "ns_name_even_ok"
  ``EVERY EVEN (MAP FST (sptree$toAList (sptree$insert 2 () (sptree$insert 4 () (LN : unit spt)))))``;
val _ = print_eval "ns_name_even_bad"
  ``EVERY EVEN (MAP FST (sptree$toAList (sptree$insert 3 () (LN : unit spt))))``;

(* domain length equals number of distinct keys *)
val _ = print_eval "ns_len_two"
  ``LENGTH (sptree$toAList (sptree$insert 1 () (sptree$insert 0 () (LN : unit spt))))``;

(* non-unit maps: duplicate key value resolution (left-bias of union, last of insert) *)
val _ = print_eval "nsmap_union_left"
  ``ALOOKUP (sptree$toAList (sptree$union (sptree$insert 0 (5:num) (LN : num spt))
                                          (sptree$insert 0 (7:num) (LN : num spt)))) 0``;
val _ = print_eval "nsmap_insert_last"
  ``ALOOKUP (sptree$toAList (sptree$insert 0 (9:num) (sptree$insert 0 (5:num) (LN : num spt)))) 0``;