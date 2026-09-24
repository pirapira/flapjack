(* Direct HOL observations for HOL `locals_rel_insert_gt_vmax`
   (`crep_to_loopProofScript.sml:228-238`): the relation is a universally
   quantified Prop, so the rows below evaluate the `sptree$insert` semantics it
   relies on at a concrete `num_map`: a fresh binding is visible at its own key,
   existing lookups are unchanged, and a `vmax`-bounded lookup survives the
   insert. *)
load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* t : num_map with 0 |-> Word 9w and 2 |-> Word 7w. *)
val t = ``(sptree$fromAList
             [(0:num, Word (9w:8 word)); (2:num, Word (7w:8 word))]
             : 8 word_loc sptree$num_map)``;

val _ = print_eval "insert_same"
  (``sptree$lookup (3:num) (sptree$insert (3:num) (Word (5w:8 word)) ^t) =
      SOME (Word (5w:8 word))``);
val _ = print_eval "insert_other_unchanged"
  (``sptree$lookup (2:num) (sptree$insert (3:num) (Word (5w:8 word)) ^t) =
      SOME (Word (7w:8 word))``);
val _ = print_eval "gt_vmax_bounded_survives"
  (``sptree$lookup (0:num) ^t = SOME (Word (9w:8 word)) ==>
      sptree$lookup (0:num) (sptree$insert (5:num) (Word (5w:8 word)) ^t) =
        SOME (Word (9w:8 word))``);
val _ = print_eval "subset_preserved"
  (``(sptree$lookup (2:num) ^t <> NONE) ==>
      sptree$lookup (2:num) (sptree$insert (5:num) (Word (5w:8 word)) ^t) <> NONE``);