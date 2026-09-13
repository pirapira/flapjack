(*
  Minimal arithmetic source-execution probe for the original CakeML Pancake
  semantics.  This is the independent expected observation for the linked
  Lean RISC-V execution fixture, not a second Lean evaluator.

  Reference: cakeml/pancake/semantics/panSemScript.sml:638-643
  (Return evaluation) and :787-809 (bounded observational execution).
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

val _ = print_eval "return_add_6_7"
  ``FST (panSem$evaluate
      (panLang$Return
        (panLang$Op (asm$Add)
          [panLang$Const (6w:8 word); panLang$Const (7w:8 word)]),
       (ARB:((8),unit) panSem$state)))``
