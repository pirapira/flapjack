(*
  Direct HOL-EVAL probes for the CakeML allocator spill/coalesce priority
  functions used by the frame-occupancy slice.

  Source: cakeml/compiler/backend/word_allocScript.sml
    get_spillcost     lines 1666-1670
    get_coalescecost  lines 1676-1681

  These decide which values the IRC allocator spills, hence which values
  occupy frame slots.  The outputs let the port's `getSpillCost` /
  `getCoalesceCost` unit tests be checked against the original instead of
  hand-entered expectations.
*)
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

(* get_spillcost: (c,lr,lm,rr,rm) -> weighted uses, x5 for tail calls. *)
val _ = print_eval "spill_zero" ``get_spillcost (0,0,0,0,0) F``
val _ = print_eval "spill_c1" ``get_spillcost (1,0,0,0,0) F``
val _ = print_eval "spill_lr1" ``get_spillcost (0,1,0,0,0) F``
val _ = print_eval "spill_lm1" ``get_spillcost (0,0,1,0,0) F``
val _ = print_eval "spill_rr1" ``get_spillcost (0,0,0,1,0) F``
val _ = print_eval "spill_rm1" ``get_spillcost (0,0,0,0,1) F``
val _ = print_eval "spill_all1" ``get_spillcost (1,1,1,1,1) F``
val _ = print_eval "spill_all1_tail" ``get_spillcost (1,1,1,1,1) T``

(* get_coalescecost: n*(10*(p+1) + xcost + ycost), where the endpoint
   costs are 1 when the endpoint appears in the spill-cost table. *)
val _ = print_eval "coal_empty" ``get_coalescecost (LN:num spt) (3,0,(1,2))``
val _ = print_eval "coal_x_in"
  ``get_coalescecost (insert 1 7 (LN:num spt)) (3,0,(1,2))``
val _ = print_eval "coal_y_in"
  ``get_coalescecost (insert 2 9 (LN:num spt)) (3,0,(1,2))``
val _ = print_eval "coal_both_in"
  ``get_coalescecost (insert 1 7 (insert 2 9 (LN:num spt))) (3,0,(1,2))``
val _ = print_eval "coal_pri2_both_in"
  ``get_coalescecost (insert 1 7 (insert 2 9 (LN:num spt))) (3,2,(1,2))``