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
val wf_drop_context =
  ``[(«prefix», []); («s», [(«field», panLang$One)])]``;
val _ = print_eval "wf_shape_drop"
  ``panLang$is_wf_shape (DROP 1 ^wf_drop_context) (panLang$Named «s») ==>
    panLang$is_wf_shape ^wf_drop_context (panLang$Named «s»)``;
val dropwhile_source = ``[0; 1; 2; 3]``;
val _ = print_eval "dropWhile_MAP_helper"
  ``dropWhile (\n:num. n < 3) (MAP SUC ^dropwhile_source) =
    MAP SUC (dropWhile (\n:num. n < 2) ^dropwhile_source)``;
val _ = print_eval "UNCURRY_EQ_o_SND_pair"
  ``UNCURRY (\x. SUC) (0, 4) = SUC 4``;
