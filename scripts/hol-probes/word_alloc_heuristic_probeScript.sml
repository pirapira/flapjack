(* Direct Cake oracle for the source word_alloc heuristic map merges. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val left = ``sptree$fromAList [(1n,(1n,0n,0n,0n,0n));
                               (4n,(0n,2n,0n,0n,0n));
                               (6n,(0n,0n,3n,0n,0n))]``;
val right = ``sptree$fromAList [(4n,(0n,0n,4n,0n,0n));
                                (7n,(0n,0n,0n,5n,0n));
                                (12n,(0n,0n,0n,0n,6n))]``;

val _ = print_eval "max_all_left_right"
  ``sptree$toAList (heu_max_all ^left ^right)``;
val _ = print_eval "merge_calls"
  ``sptree$toAList (heu_merge_call
      (sptree$fromAList [(1n,());(4n,());(6n,())])
      (sptree$fromAList [(4n,());(7n,());(12n,())]))``;
val _ = print_eval "max_all_disjoint"
  ``sptree$toAList (heu_max_all
      (sptree$fromAList [(0n,(1n,0n,0n,0n,0n));(8n,(0n,1n,0n,0n,0n))])
      (sptree$fromAList [(2n,(0n,0n,1n,0n,0n));(10n,(0n,0n,0n,1n,0n))]))``;
