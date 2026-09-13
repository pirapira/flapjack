(*
  Minimal source-execution probe for the original CakeML Pancake semantics.
  This is the authoritative expected result for the checked-in Lean
  source-to-RISC-V execution fixture, not a second Lean oracle.

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

val _ = print_eval "return_41"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Const (41w:8 word)),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "return_mul_42"
  ``FST (panSem$evaluate
      (panLang$Return
        (panLang$Panop panLang$Mul
          [panLang$Const (6w:8 word); panLang$Const (7w:8 word)]),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "return_if_13"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word))
        (panLang$Return (panLang$Const (13w:8 word)))
        (panLang$Return (panLang$Const (99w:8 word))),
       (ARB:((8),unit) panSem$state)))``
