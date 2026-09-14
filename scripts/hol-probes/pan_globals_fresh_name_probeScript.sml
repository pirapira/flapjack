(* Direct HOL-EVAL fixture for pan_globals$fresh_name_def. *)
load "bossLib";
load "preamble";
load "pan_globalsTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "empty"
  ``pan_globals$fresh_name «x» []``;
val _ = print_eval "one_collision"
  ``pan_globals$fresh_name «x» [«x»]``;
val _ = print_eval "three_collisions"
  ``pan_globals$fresh_name «x» [«x»; «x'»; «x''»]``;
val _ = print_eval "quoted_name"
  ``pan_globals$fresh_name «x'» [«x'»; «x''»]``;
val _ = print_eval "absent"
  ``pan_globals$fresh_name «main» [«worker»; «helper»]``;
