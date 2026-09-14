(* Direct HOL-EVAL probes for pan_to_crep$ret_hdl.
   Reference: cakeml/pancake/pan_to_crepScript.sml:122-127. *)
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

val _ = print_eval "one"
  ``pan_to_crep$ret_hdl One []``;
val _ = print_eval "comb_empty"
  ``pan_to_crep$ret_hdl (Comb []) []``;
val _ = print_eval "comb_one"
  ``pan_to_crep$ret_hdl (Comb [One]) [(1:num)]``;
val _ = print_eval "comb_two"
  ``pan_to_crep$ret_hdl (Comb [One; One]) [(1:num); 2]``;
val _ = print_eval "named"
  ``pan_to_crep$ret_hdl (Named «S») [(1:num)]``;
