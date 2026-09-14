(* Direct HOL-EVAL probes for CakeML Pancake panSem dec_clock_def. *)
(* Reference: cakeml/pancake/semantics/panSemScript.sml:441-443. *)
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

val _ = print_eval "pan_dec_clock_five"
  ``(dec_clock (^s with clock := 5)).clock``;
val _ = print_eval "pan_dec_clock_zero"
  ``(dec_clock (^s with clock := 0)).clock``;
