(*
  Direct HOL observations for crep_primop_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:221-232.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val toNum = ``(λ(x:8 word_lab). case x of Word w => w2n w)``;

fun print_primop label args =
  print_eval label
    ``(case crepSem$crep_primop panLang$AddCarry ^args of
        | NONE => NONE
        | SOME values => SOME (MAP ^toNum values))``;

val _ = print_primop "crep_basic"
  ``[Word (40w:8 word); Word (50w:8 word); Word (0w:8 word)]``;
val _ = print_primop "crep_overflow"
  ``[Word (200w:8 word); Word (100w:8 word); Word (0w:8 word)]``;
val _ = print_primop "crep_carry_is_bit"
  ``[Word (5w:8 word); Word (7w:8 word); Word (2w:8 word)]``;
val _ = print_primop "crep_wrong_length"
  ``[Word (5w:8 word); Word (7w:8 word)]``;
