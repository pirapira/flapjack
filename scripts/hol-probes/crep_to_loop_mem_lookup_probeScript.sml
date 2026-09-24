load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val al = ``[(1:num,7:num);(2:num,9:num)]``;

(* mem_lookup_fromalist_some: a duplicate-free association list member is
   returned by fromAList/lookup. *)
val _ = print_eval "ml_hit"
  ``sptree$lookup 2 (sptree$fromAList ^al) = SOME 9``;
val _ = print_eval "ml_miss"
  ``sptree$lookup 3 (sptree$fromAList ^al) = NONE``;
val _ = print_eval "ml_distinct"
  ``ALL_DISTINCT (MAP FST ^al)``;