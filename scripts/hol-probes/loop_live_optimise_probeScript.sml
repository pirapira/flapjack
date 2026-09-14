(* Direct HOL-EVAL fixture for loop_live$optimise. *)
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
  ``loop_live$optimise
      (loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "loc_value"
  ``loop_live$optimise
      (loopLang$LocValue 3 7 : 8 word loopLang$prog)``;
val _ = print_eval "seq"
  ``loop_live$optimise
      (loopLang$Seq loopLang$Skip loopLang$Skip : 8 word loopLang$prog)``;
val _ = print_eval "ffi"
  ``loop_live$optimise
      (loopLang$FFI «f» 1 2 3 4 LN : 8 word loopLang$prog)``;
