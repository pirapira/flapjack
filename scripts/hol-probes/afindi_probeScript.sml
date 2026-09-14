(* Direct HOL-EVAL fixture for pan_structs$afindi_def. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
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
  ``pan_structs$afindi «a» []``;
val _ = print_eval "first"
  ``pan_structs$afindi «a» [(«a», 10); («b», 20)]``;
val _ = print_eval "middle"
  ``pan_structs$afindi «b» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "last"
  ``pan_structs$afindi «c» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "missing"
  ``pan_structs$afindi «z» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "duplicate_first"
  ``pan_structs$afindi «a» [(«a», 10); («b», 20); («a», 30)]``;
