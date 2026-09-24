(*
  Direct HOL observations for crepSem$crep_op_def
  (cakeml/pancake/semantics/crepSemScript.sml:85-88):
    crep_op Mul [w1;w2] = SOME (w1 * w2)  and  crep_op _ _ = NONE.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

val _ = print_eval "op_mul_two"
  ``(crep_op crepLang$Mul [(7w:64 word); (3w:64 word)])``;
val _ = print_eval "op_mul_one"
  ``(crep_op crepLang$Mul [(7w:64 word)])``;
val _ = print_eval "op_mul_three"
  ``(crep_op crepLang$Mul [(7w:64 word); (3w:64 word); (1w:64 word)])``;
val _ = print_eval "op_mul_empty"
  ``(crep_op crepLang$Mul ([] : 64 word list))``;
