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
   the final row records the proven `distinct_lists_eq_disjoint` boundary.

   Provenance (bead flapjack-pxn.18.4.3.78.1): generated from the Flapjack
   checkout with the coordinator-approved read-only prebuilt CakeML/HOL object
   directory as oracle input, without editing that checkout:

     CAKEML=/home/zksecurity/flapjack7/cakeml \
       HOL_PROBE_ONLY=pan_common_distinct_lists_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede, and their
   pancake/pan_commonScript.sml are byte-identical
   (sha256 569dafb0a2182549a1de3491a4472a22338cd93c87fe6b6c193f902cbfb1e759). *)

(* The `genlist_vmax_*` rows additionally exercise the left-operand shape of
   HOL `genlist_vmax_distinct_lists_compiled_exps`, the source of the
   width-indexed Lean statement
   `Flapjack.genlistVmaxDistinctListsCompiledExpsW`
   (bead flapjack-pxn.18.4.3.78.3). *)
val _ = print_eval "distinct_true" ``pan_common$distinct_lists [1;2] [3;4]``;
val _ = print_eval "distinct_false_right_hit" ``pan_common$distinct_lists [1;2] [2;4]``;
val _ = print_eval "distinct_false_middle_hit" ``pan_common$distinct_lists [5;1;2] [4;5]``;
val _ = print_eval "distinct_empty_left" ``pan_common$distinct_lists [] [1;2]``;
val _ = print_eval "distinct_empty_right" ``pan_common$distinct_lists [1;2] []``;
val _ = print_eval "distinct_eq_every_mem"
  ``pan_common$distinct_lists [1;2;3] [4;5] = EVERY (\x. ~MEM x [4;5]) [1;2;3]``;
val _ = print_eval "distinct_eq_disjoint"
  ``pan_common$distinct_lists [1;2;3] [4;5] = DISJOINT (set [1;2;3]) (set [4;5])``;

(* Width-indexed genlist oracle (bead flapjack-pxn.18.4.3.78.3): the left
   operand of HOL `genlist_vmax_distinct_lists_compiled_exps`
   (cakeml/pancake/proofs/pan_to_crepProofScript.sml:3094) is
   `GENLIST (\x. SUC x + ctxt.vmax) n`.  These rows evaluate that shape
   directly for `ctxt.vmax = 3`, `n = 3` (so the left list is `[4;5;6]`),
   against right lists that are bounded by `vmax` (`T`) or hit it (`F`). *)
val _ = print_eval "genlist_vmax_bound"
  ``pan_common$distinct_lists (GENLIST (\x. SUC x + 3) 3) [0;1;2;3]``;
val _ = print_eval "genlist_vmax_hit"
  ``pan_common$distinct_lists (GENLIST (\x. SUC x + 3) 3) [4;7]``;
val _ = print_eval "genlist_vmax_disjoint"
  ``pan_common$distinct_lists (GENLIST (\x. SUC x + 3) 3) [7;8]``;
