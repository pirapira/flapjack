(* Direct HOL-EVAL probes for pan_to_crep$ret_var.
   Reference: cakeml/pancake/pan_to_crepScript.sml:114-119. *)
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

val _ = print_eval "one_empty"
  ``pan_to_crep$ret_var One []``;
val _ = print_eval "one_nonempty"
  ``pan_to_crep$ret_var One [(3:num); 4]``;
val _ = print_eval "comb_one"
  ``pan_to_crep$ret_var (Comb [One]) [(5:num)]``;
val _ = print_eval "comb_many"
  ``pan_to_crep$ret_var (Comb [One; One]) [(6:num)]``;
val _ = print_eval "named"
  ``pan_to_crep$ret_var (Named «S») [(7:num)]``;
