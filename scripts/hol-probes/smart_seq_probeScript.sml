(* Direct HOL-EVAL probes for pan_simp$SmartSeq.
   Reference: cakeml/pancake/pan_simpScript.sml:13-16. *)
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

val _ = print_eval "skip_skip"
  ``pan_simp$SmartSeq panLang$Skip panLang$Skip``;

val _ = print_eval "skip_tick"
  ``pan_simp$SmartSeq panLang$Skip panLang$Tick``;

val _ = print_eval "tick_skip"
  ``pan_simp$SmartSeq panLang$Tick panLang$Skip``;

val _ = print_eval "tick_tick"
  ``pan_simp$SmartSeq panLang$Tick panLang$Tick``;
