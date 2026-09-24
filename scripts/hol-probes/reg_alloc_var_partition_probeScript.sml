load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open reg_allocTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val print_eval = fn label => fn q => print_eval label q;

(* is_phy_var / is_stack_var / is_alloc_var rows *)
print_eval "is_phy_6" ``reg_alloc$is_phy_var 6``;
print_eval "is_phy_7" ``reg_alloc$is_phy_var 7``;
print_eval "is_stack_7" ``reg_alloc$is_stack_var 7``;
print_eval "is_stack_6" ``reg_alloc$is_stack_var 6``;
print_eval "is_alloc_5" ``reg_alloc$is_alloc_var 5``;
print_eval "is_alloc_4" ``reg_alloc$is_alloc_var 4``;

(* convention_partitions instances *)
print_eval "part_stack_3"
  ``(reg_alloc$is_stack_var 3 <=> ~reg_alloc$is_phy_var 3 /\ ~reg_alloc$is_alloc_var 3) /\
    (reg_alloc$is_phy_var 3 <=> ~reg_alloc$is_stack_var 3 /\ ~reg_alloc$is_alloc_var 3) /\
    (reg_alloc$is_alloc_var 3 <=> ~reg_alloc$is_phy_var 3 /\ ~reg_alloc$is_stack_var 3)``;
print_eval "part_phy_2"
  ``(reg_alloc$is_stack_var 2 <=> ~reg_alloc$is_phy_var 2 /\ ~reg_alloc$is_alloc_var 2) /\
    (reg_alloc$is_phy_var 2 <=> ~reg_alloc$is_stack_var 2 /\ ~reg_alloc$is_alloc_var 2) /\
    (reg_alloc$is_alloc_var 2 <=> ~reg_alloc$is_phy_var 2 /\ ~reg_alloc$is_stack_var 2)``;
print_eval "part_alloc_1"
  ``(reg_alloc$is_stack_var 1 <=> ~reg_alloc$is_phy_var 1 /\ ~reg_alloc$is_alloc_var 1) /\
    (reg_alloc$is_phy_var 1 <=> ~reg_alloc$is_stack_var 1 /\ ~reg_alloc$is_alloc_var 1) /\
    (reg_alloc$is_alloc_var 1 <=> ~reg_alloc$is_phy_var 1 /\ ~reg_alloc$is_stack_var 1)``;
print_eval "part_none_0"
  ``(reg_alloc$is_stack_var 0 <=> ~reg_alloc$is_phy_var 0 /\ ~reg_alloc$is_alloc_var 0) /\
    (reg_alloc$is_phy_var 0 <=> ~reg_alloc$is_stack_var 0 /\ ~reg_alloc$is_alloc_var 0) /\
    (reg_alloc$is_alloc_var 0 <=> ~reg_alloc$is_phy_var 0 /\ ~reg_alloc$is_stack_var 0)``;