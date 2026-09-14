(* Direct HOL-EVAL probes for pan_simp$seq_assoc.
   Reference: cakeml/pancake/pan_simpScript.sml:18-40. *)
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
  ``pan_simp$seq_assoc panLang$Skip panLang$Skip``;

val _ = print_eval "tick_skip"
  ``pan_simp$seq_assoc panLang$Tick panLang$Skip``;

val _ = print_eval "tick_seq_skip_tick"
  ``pan_simp$seq_assoc panLang$Tick
      (panLang$Seq panLang$Skip panLang$Tick)``;

val _ = print_eval "tick_return"
  ``pan_simp$seq_assoc panLang$Tick
      (panLang$Return (panLang$Const (7w : 8 word)))``;
