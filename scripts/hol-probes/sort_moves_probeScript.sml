(* Direct HOL-EVAL fixture for reg_alloc$sort_moves (QSORT tie order) and a
   Stemp-preference reg_alloc case exercising neg_first_match_col.
   Reference: cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:343-346,
   1420-1436, 1452-1470. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val _ = print_eval "sm_ties_two"
  ``reg_alloc$sort_moves
      [(1:num,(13:num,5:num));(1,(5,9))]``;
val _ = print_eval "sm_ties_three"
  ``reg_alloc$sort_moves
      [(3:num,(1:num,2:num));(1,(9,9));(3,(7,8))]``;
val _ = print_eval "sm_desc"
  ``reg_alloc$sort_moves
      [(1:num,(13:num,5:num));(3,(5,9));(2,(7,8))]``;
(* A stack temp neighbour of a coalesced move: exercises assign_Stemps'
   neg_biased_pref / neg_first_match_col node-tag projection. *)
val _ = print_eval "ra_moves_stemp"
  ``reg_alloc$reg_alloc IRC NONE 4
      [(1:num,(3:num,9:num))]
      (reg_alloc$Delta [9] [13;3]) [] LN``;
val _ = print_eval "ra_moves_stemp_hi"
  ``reg_alloc$reg_alloc IRC NONE 4
      [(5:num,(3:num,9:num))]
      (reg_alloc$Delta [9] [13;3]) [] LN``;
