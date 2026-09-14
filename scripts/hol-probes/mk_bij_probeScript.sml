(* Direct HOL-EVAL probes for reg_alloc$mk_bij / list_remap, the clash-tree
   to allocator-node bijection.
   Reference: cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1096-1130. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open reg_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

(* Reads are remapped before writes inside a Delta. *)
val _ = print_eval "delta_basic"
  ``reg_alloc$mk_bij (reg_alloc$Delta [1] [2; 3])``;

(* Already-mapped variables are skipped. *)
val _ = print_eval "delta_dedup"
  ``reg_alloc$mk_bij (reg_alloc$Delta [2] [2; 3])``;

(* Seq remaps the right subtree first. *)
val _ = print_eval "seq_order"
  ``reg_alloc$mk_bij (reg_alloc$Seq (reg_alloc$Delta [] [5]) (reg_alloc$Delta [] [7]))``;

(* Branch remaps t1, then t2, then the optional live set. *)
val _ = print_eval "branch_order"
  ``reg_alloc$mk_bij (reg_alloc$Branch NONE (reg_alloc$Delta [] [9]) (reg_alloc$Delta [] [11]))``;

val _ = print_eval "branch_live"
  ``reg_alloc$mk_bij (reg_alloc$Branch (SOME (insert 13 () LN))
      (reg_alloc$Delta [] [9]) (reg_alloc$Delta [] [11]))``;

(* Set remaps the fixed set in ascending sptree order. *)
val _ = print_eval "set_case"
  ``reg_alloc$mk_bij (reg_alloc$Set (insert 4 () (insert 3 () LN)))``;

(* A small composite tree: seq of delta and branch-with-live. *)
val _ = print_eval "composite"
  ``reg_alloc$mk_bij (reg_alloc$Seq (reg_alloc$Delta [1] [2])
      (reg_alloc$Branch (SOME (insert 6 () LN))
         (reg_alloc$Delta [] [4]) (reg_alloc$Delta [] [5])))``;
