(* Direct HOL-EVAL fixture for pan_globals$fperm_name_def. *)
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

val _ = print_eval "source_collision"
  ``pan_globals$fperm_name «foo» «bar» «foo»``;
val _ = print_eval "target_collision"
  ``pan_globals$fperm_name «foo» «bar» «bar»``;
val _ = print_eval "unchanged"
  ``pan_globals$fperm_name «foo» «bar» «worker»``;
val _ = print_eval "same_names"
  ``pan_globals$fperm_name «foo» «foo» «foo»``;
val _ = print_eval "quoted_source"
  ``pan_globals$fperm_name «foo'» «bar'» «foo'»``;
