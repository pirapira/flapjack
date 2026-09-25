(*
  Direct HOL observations for empty_locals_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:436.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:((8),unit) panSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "empty_locals" ``(panSem$empty_locals ^s).locals = FEMPTY``;
val _ = print_eval "empty_locals_globals"
  ``(panSem$empty_locals ^s).globals = ^s.globals``;
val _ = print_eval "empty_locals_clock"
  ``(panSem$empty_locals ^s).clock = ^s.clock``;
