(*
  Direct HOL-EVAL probes for Pancake loopLang$acc_vars.
  Reference: cakeml/pancake/loopLangScript.sml:117-158.
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
  ``acc_vars (Skip : 32 word loopLang$prog) []``
val _ = print_eval "assign"
  ``acc_vars (Assign 7 (Const (1w : 32 word))) []``
val _ = print_eval "return"
  ``acc_vars (Return [7; 8] : 32 word loopLang$prog) []``
val _ = print_eval "store"
  ``acc_vars (Store (Var 4) 7 : 32 word loopLang$prog) []``
val _ = print_eval "long_div"
  ``acc_vars (Arith (LLongDiv 1 2 3 4 5) : 32 word loopLang$prog) []``
val _ = print_eval "call_none"
  ``acc_vars (Call NONE (SOME 3) [4; 5] NONE : 32 word loopLang$prog) []``
