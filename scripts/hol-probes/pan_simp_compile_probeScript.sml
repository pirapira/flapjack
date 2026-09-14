(* Direct HOL-EVAL probes for pan_simp$compile.
   Reference: cakeml/pancake/pan_simpScript.sml:68-72. *)
load "bossLib";
load "preamble";
load "../pan_simpTheory";
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
  end;

val _ = print_eval "skip"
  ``pan_simp$compile panLang$Skip``;

val _ = print_eval "seq_skip_tick"
  ``pan_simp$compile (panLang$Seq panLang$Skip panLang$Tick)``;

val _ = print_eval "tail_call"
  ``pan_simp$compile
      (panLang$Seq
        (panLang$Call
          (SOME (SOME (panLang$Local, strlit "r"), NONE))
          (strlit "f") [])
        (panLang$Return
          (panLang$Var panLang$Local (strlit "r"))))``;
