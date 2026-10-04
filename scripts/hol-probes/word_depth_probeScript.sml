(*
  Direct HOL-EVAL observations for CakeML `word_depth` call-tree max-depth.

  Source:
    cakeml/compiler/backend/word_depthScript.sml
      call_tree (lines 14-20), max_depth (lines 24-33)

  `max_depth` reads frame sizes by `lookup` on a `num_map` (`num spt`). The
  rows below vary the tree shape (Leaf/Unknown/Const/Branch/Call), the frame
  lookup hit/miss, and nesting. A missing frame stays NONE (the original never
  invents a bound for unknown/cyclic calls).
*)
load "bossLib";
load "preamble";
load "word_depthTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_depthTheory;

val _ = show_types := true;
fun emit label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = print "max_depth_type=";
val _ = print (type_to_string (type_of ``word_depth$max_depth``));
val _ = print "\n";
val _ = emit "max_depth_def_typed" (DB.fetch "word_depth" "max_depth_def");

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val fs10 = ``insert 1 10 (insert 2 20 (LN:num num_map))``;

val _ = print_eval "leaf" ``max_depth (LN:num num_map) Leaf``
val _ = print_eval "unknown" ``max_depth (LN:num num_map) Unknown``
val _ = print_eval "const_leaf" ``max_depth (LN:num num_map) (Const 5 Leaf)``
val _ = print_eval "nested_const" ``max_depth (LN:num num_map) (Const 3 (Const 4 Leaf))``
val _ = print_eval "branch_max"
  ``max_depth (LN:num num_map) (Branch (Const 3 Leaf) (Const 5 Leaf))``
val _ = print_eval "branch_unknown"
  ``max_depth (LN:num num_map) (Branch (Const 3 Leaf) Unknown)``
val _ = print_eval "call_hit" ``max_depth ^fs10 (Call 1 Leaf)``
val _ = print_eval "call_miss" ``max_depth ^fs10 (Call 7 Leaf)``
val _ = print_eval "call_hit_nested" ``max_depth ^fs10 (Call 1 (Const 4 Leaf))``
val _ = print_eval "deep_calls"
  ``max_depth ^fs10 (Call 1 (Call 2 (Const 3 Leaf)))``
val _ = print_eval "branch_call"
  ``max_depth ^fs10 (Branch (Call 1 Leaf) (Const 2 Leaf))``
val _ = print_eval "unknown_deep"
  ``max_depth ^fs10 (Branch Unknown (Call 1 (Const 9 Leaf)))``
