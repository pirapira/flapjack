load "bossLib";
load "preamble";
load "pan_commonTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of `distinct_lists_def` at
   cakeml/pancake/pan_commonScript.sml:8-11.  The last row checks the
   definitional agreement with `EVERY (\x. ~MEM x ys) xs` used in the proofs;
   the final row records the proven `distinct_lists_eq_disjoint` boundary. *)
val _ = print_eval "distinct_true" ``pan_common$distinct_lists [1;2] [3;4]``;
val _ = print_eval "distinct_false_right_hit" ``pan_common$distinct_lists [1;2] [2;4]``;
val _ = print_eval "distinct_false_middle_hit" ``pan_common$distinct_lists [5;1;2] [4;5]``;
val _ = print_eval "distinct_empty_left" ``pan_common$distinct_lists [] [1;2]``;
val _ = print_eval "distinct_empty_right" ``pan_common$distinct_lists [1;2] []``;
val _ = print_eval "distinct_eq_every_mem"
  ``pan_common$distinct_lists [1;2;3] [4;5] = EVERY (\x. ~MEM x [4;5]) [1;2;3]``;
val _ = print_eval "distinct_eq_disjoint"
  ``pan_common$distinct_lists [1;2;3] [4;5] = DISJOINT (set [1;2;3]) (set [4;5])``;
