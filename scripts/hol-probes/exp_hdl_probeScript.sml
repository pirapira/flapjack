(* Direct HOL-EVAL probes for pan_to_crep$exp_hdl.
   Reference: cakeml/pancake/pan_to_crepScript.sml:106-112. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val vars = ``(FEMPTY |+ («x», (One, [(3:num); 4])))``;
val _ = print_eval "missing"
  ``pan_to_crep$exp_hdl ^vars «missing»``;
val _ = print_eval "known"
  ``pan_to_crep$exp_hdl ^vars «x»``;
