(*
  Direct HOL-EVAL observations for CakeML's Patricia-tree enumeration order
  (`sptree$toAList`), used by the word allocator at its three SSA boundaries:
  `fix_inconsistencies`, `ssa_reconcile` and `loop_setup`
  (cakeml/compiler/backend/word_allocScript.sml:116, 318, 329).

  Theory: sptreeTheory (HOL/src/finite_maps/sptreeScript.sml).  The probe
  evaluates `MAP FST (toAList (fromAList ...))` directly; the Lean test
  Flapjack/Test/SptreeOrderParity.lean consumes the checked-in .out.
*)
load "bossLib";
load "preamble";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory;

fun pe label q = let val th = EVAL q in print (label ^ "="); print_term (rconc th); print "\n" end;

pe "alist_0_4_6_12" ``MAP FST (toAList (fromAList [(0:num,()); (4,()); (6,()); (12,())]))``;
pe "alist_0_4_8_12_16" ``MAP FST (toAList (fromAList [(0:num,()); (4,()); (8,()); (12,()); (16,())]))``;
pe "alist_1_2_3_4_5" ``MAP FST (toAList (fromAList [(1:num,()); (2,()); (3,()); (4,()); (5,())]))``;
pe "alist_range13" ``MAP FST (toAList (fromAList [(0:num,()); (1,()); (2,()); (3,()); (4,()); (5,()); (6,()); (7,()); (8,()); (9,()); (10,()); (11,()); (12,())]))``;
