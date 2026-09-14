(* Direct HOL-EVAL fixture for pan_structs$compile_shape_def. *)
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

val forward_context =
  ``[(«outer», [(«field», Named «inner»)]);
      («inner», [(«value», One)])]``;
val backward_context =
  ``[(«inner», [(«value», One)]);
      («outer», [(«field», Named «inner»)])]``;

val _ = print_eval "one"
  ``pan_structs$compile_shape ^forward_context One``;
val _ = print_eval "comb"
  ``pan_structs$compile_shape ^forward_context (Comb [One; One])``;
val _ = print_eval "forward_nested"
  ``pan_structs$compile_shape ^forward_context (Named «outer»)``;
val _ = print_eval "backward_suffix"
  ``pan_structs$compile_shape ^backward_context (Named «outer»)``;
val _ = print_eval "missing"
  ``pan_structs$compile_shape ^forward_context (Named «missing»)``;
