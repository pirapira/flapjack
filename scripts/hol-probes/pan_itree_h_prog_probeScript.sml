(*
  Direct HOL observations for h_prog_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:555-577.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "h_prog_skip"
  ``h_prog (panLang$Skip,^s)``;

val _ = print_eval "h_prog_break"
  ``h_prog (panLang$Break,^s)``;

val _ = print_eval "h_prog_continue"
  ``h_prog (panLang$Continue,^s)``;

val _ = print_eval "h_prog_tick"
  ``h_prog (panLang$Tick,^s)``;
