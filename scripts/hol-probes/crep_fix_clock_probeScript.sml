(*
  Direct HOL observations for crepSem$fix_clock_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:150-152.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "fix_clock_clamps"
  ``(case crepSem$fix_clock (^s with clock := 5)
      (Return [Word (7w:8 word)],
       ^s with <|locals := FEMPTY |+ (1, Word (7w:8 word)); clock := 9|>) of
      (res,s') => (res, FLOOKUP s'.locals 1, s'.clock))``;

val _ = print_eval "fix_clock_keeps_lower"
  ``(case crepSem$fix_clock (^s with clock := 5)
      (Return [Word (7w:8 word)],
       ^s with <|locals := FEMPTY |+ (1, Word (7w:8 word)); clock := 3|>) of
      (res,s') => (res, FLOOKUP s'.locals 1, s'.clock))``;
