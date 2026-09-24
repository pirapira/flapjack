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
val _ = print_eval "distinct_true" ``pan_common$distinct_lists [1;2] [3;4]``;
val _ = print_eval "distinct_false_right_hit" ``pan_common$distinct_lists [1;2] [2;4]``;
val _ = print_eval "distinct_false_middle_hit" ``pan_common$distinct_lists [5;1;2] [4;5]``;
val _ = print_eval "distinct_empty_left" ``pan_common$distinct_lists [] [1;2]``;
val _ = print_eval "distinct_empty_right" ``pan_common$distinct_lists [1;2] []``;
val _ = print_eval "distinct_eq_every_mem"
  ``pan_common$distinct_lists [1;2;3] [4;5] = EVERY (\x. ~MEM x [4;5]) [1;2;3]``;
val _ = print_eval "distinct_eq_disjoint"
  ``pan_common$distinct_lists [1;2;3] [4;5] = DISJOINT (set [1;2;3]) (set [4;5])``;
