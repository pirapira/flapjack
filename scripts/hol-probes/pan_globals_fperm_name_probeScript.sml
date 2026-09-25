(* Direct HOL-EVAL fixture for pan_globals$fperm_name_def
   (pan_globalsScript.sml:185-188), for flapjack-6nn.1.1.

   Edge cases: an unchanged (missing) key, a source-collision key, a
   target-collision key, identical names, and names carrying apostrophes
   (the character produced by the fresh-name machinery). *)
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
val _ = print_eval "quoted_target"
  ``pan_globals$fperm_name «foo'» «bar'» «bar'»``;
val _ = print_eval "quoted_unchanged"
  ``pan_globals$fperm_name «a'» «b'» «c'»``;
val _ = print_eval "fperm_name_done" ``0n``;
