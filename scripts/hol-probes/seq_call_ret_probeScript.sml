(* Direct HOL-EVAL probes for pan_simp$seq_call_ret.
   Reference: cakeml/pancake/pan_simpScript.sml:42-49. *)
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

val _ = print_eval "matching_return"
  ``pan_simp$seq_call_ret
      (panLang$Seq
        (panLang$Call
          (SOME (SOME (panLang$Local, strlit "r"), NONE))
          (strlit "f") [])
        (panLang$Return
          (panLang$Var panLang$Local (strlit "r"))))``;

val _ = print_eval "mismatching_return"
  ``pan_simp$seq_call_ret
      (panLang$Seq
        (panLang$Call
          (SOME (SOME (panLang$Local, strlit "r"), NONE))
          (strlit "f") [])
        (panLang$Return
          (panLang$Var panLang$Local (strlit "s"))))``;

val _ = print_eval "fallback"
  ``pan_simp$seq_call_ret panLang$Tick``;
