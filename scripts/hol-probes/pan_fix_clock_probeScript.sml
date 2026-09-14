(* Direct HOL-EVAL probes for CakeML Pancake panSem fix_clock_def. *)
(* Reference: cakeml/pancake/semantics/panSemScript.sml:446-448. *)
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

val _ = print_eval "pan_fix_clock_clamps"
  ``(SND (fix_clock (^s with clock := 5)
      (NONE, (^s with clock := 7)))).clock``;
val _ = print_eval "pan_fix_clock_keeps_lower"
  ``(SND (fix_clock (^s with clock := 5)
      (NONE, (^s with clock := 3)))).clock``;
