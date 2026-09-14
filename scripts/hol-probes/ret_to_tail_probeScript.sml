(* Direct HOL-EVAL probes for pan_simp$ret_to_tail.
   Reference: cakeml/pancake/pan_simpScript.sml:50-66. *)
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
  ``pan_simp$ret_to_tail panLang$Skip``;

val _ = print_eval "tail_call"
  ``pan_simp$ret_to_tail
      (panLang$Seq
        (panLang$Call
          (SOME (SOME (panLang$Local, strlit "r"), NONE))
          (strlit "f") [])
        (panLang$Return
          (panLang$Var panLang$Local (strlit "r"))))``;

val _ = print_eval "mismatching_return"
  ``pan_simp$ret_to_tail
      (panLang$Seq
        (panLang$Call
          (SOME (SOME (panLang$Local, strlit "r"), NONE))
          (strlit "f") [])
        (panLang$Return
          (panLang$Var panLang$Local (strlit "s"))))``;

val _ = print_eval "handler_seq"
  ``pan_simp$ret_to_tail
      (panLang$Call
        (SOME
          (SOME (panLang$Local, strlit "r"),
           SOME (0, strlit "h",
             panLang$Seq panLang$Tick panLang$Tick)))
        (strlit "f") [])``;
