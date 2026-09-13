(*
  Minimal function-call source-execution probe for the original CakeML
  Pancake semantics.  The code table is populated with the same one-word
  identity function as the source fixture; this is the independent expected
  observation for the linked Lean RISC-V execution.

  Reference: cakeml/pancake/semantics/panSemScript.sml:657-693
  (Call evaluation and return handling).
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "call_id_7"
  ``FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One)))))``
