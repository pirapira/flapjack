(*
  Direct HOL-EVAL probes for Pancake loopLang$assigned_vars.
  Reference: cakeml/pancake/loopLangScript.sml:94-115.
*)
load "bossLib";
load "preamble";
load "../loopLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "skip"
  ``assigned_vars (Skip : 32 word loopLang$prog)``
val _ = print_eval "assign"
  ``assigned_vars (Assign 7 (Const (1w : 32 word)))``
val _ = print_eval "sequence"
  ``assigned_vars (Seq (Assign 7 (Const (1w : 32 word))) (Load32 0 8))``
val _ = print_eval "long_div"
  ``assigned_vars (Arith (LLongDiv 1 2 3 4 5) : 32 word loopLang$prog)``
val _ = print_eval "load_byte"
  ``assigned_vars (LoadByte 4 9 : 32 word loopLang$prog)``
