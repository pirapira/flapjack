(* Direct HOL-EVAL fixture for crep_arithProof$lookup_code. *)
(* Reference: cakeml/pancake/proofs/crep_arithProofScript.sml:162-170. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
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
  end;

val code =
  ``FEMPTY |+ (strlit "f",
      ([1], crepLang$Assign 2
        (crepLang$Crepop crepLang$Mul
          [crepLang$Const (2w : 8 word); crepLang$Const (4w : 8 word)])))``;
val _ = print_eval "simp_prog_after_lookup"
  ``OPTION_MAP (crep_arith$simp_prog ## I)
      (crepSem$lookup_code ^code (strlit "f") [Word (9w : 8 word)] 1)``;
