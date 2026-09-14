(* Direct HOL-EVAL fixture for loop_live$mark_all. *)
load "bossLib";
load "preamble";
load "loop_liveTheory";
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

val _ = print_eval "seq_mark"
  ``loop_live$mark_all
      (loopLang$Seq loopLang$Skip loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "seq_not_mark"
  ``loop_live$mark_all
      (loopLang$Seq loopLang$Fail loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "seq_loop_not_mark"
  ``loop_live$mark_all
      (loopLang$Seq
        (loopLang$Loop LN loopLang$Skip LN)
        loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "loop"
  ``loop_live$mark_all
      (loopLang$Loop LN loopLang$Skip LN : 8 word loopLang$prog)``;
val _ = print_eval "mark_unwrapped"
  ``loop_live$mark_all
      (loopLang$Mark loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "call_no_handler"
  ``loop_live$mark_all
      (loopLang$Call NONE NONE [] NONE : 8 word loopLang$prog)``;
val _ = print_eval "call_handler"
  ``loop_live$mark_all
      (loopLang$Call (SOME ([1],LN)) NONE [2]
        (SOME (3,loopLang$Skip,loopLang$Fail,LN)) : 8 word loopLang$prog)``;
