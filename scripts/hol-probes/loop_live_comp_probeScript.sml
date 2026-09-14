(* Direct HOL-EVAL fixture for loop_live$comp. *)
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

val _ = print_eval "skip"
  ``loop_live$comp
      (loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "dead_assign"
  ``loop_live$comp
      (loopLang$Assign 1 (loopLang$Const (7w : 8 word)))``;
val _ = print_eval "seq"
  ``loop_live$comp
      (loopLang$Seq loopLang$Skip loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "arith"
  ``loop_live$comp
      (loopLang$Arith (loopLang$LDiv 1 2 3) : 8 word loopLang$prog)``;
val _ = print_eval "return"
  ``loop_live$comp
      (loopLang$Return [7] : 8 word loopLang$prog)``;
