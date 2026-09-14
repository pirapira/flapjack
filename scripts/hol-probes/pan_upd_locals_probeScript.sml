(* Direct HOL-EVAL probes for CakeML Pancake panSem upd_locals_def. *)
(* Reference: cakeml/pancake/semantics/panSemScript.sml:431-434. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val s = ``(s:(8,'ffi) panSem$state)``;
val args = ``[(strlit "x", ValWord (3w : 8 word));
              (strlit "x", ValWord (7w : 8 word))]``;

val _ = print_eval "pan_upd_locals_hit"
  ``OPTION_MAP (\v. case v of ValWord w => w2n w | _ => 0)
      (FLOOKUP (upd_locals ^args ^s).locals (strlit "x"))``;
val _ = print_eval "pan_upd_locals_empty"
  ``FLOOKUP (upd_locals [] ^s).locals (strlit "x")``;
