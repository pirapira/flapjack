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

(* Duplicate updates: the last update wins, so only the final binding's
   flattened list is lowered. *)
val dup_update =
  ``((FEMPTY |+ («x», (One, [(3:num); 4]))) |+ («x», (One, [(7:num)])))``;
val _ = print_eval "dup_update"
  ``pan_to_crep$exp_hdl ^dup_update «x»``;

val dup_list =
  ``FUPDATE_LIST FEMPTY [(«x», (One, [(3:num); 4])); («x», (One, [(7:num)]))]``;
val _ = print_eval "dup_list"
  ``pan_to_crep$exp_hdl ^dup_list «x»``;
