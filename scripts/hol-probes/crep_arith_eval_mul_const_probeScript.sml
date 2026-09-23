(* Direct HOL-EVAL observations for crep_arithProof$eval_mul_const. *)
load "bossLib";
load "preamble";
load "crep_arithTheory";
load "crepSemTheory";
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

val s = ``(s:(64,unit) crepSem$state)``;
val state = ``^s with locals := FEMPTY |+ (2, Word (7w:64 word))``;
val expression = ``crepLang$Var 2 : 64 crepLang$exp``;

val _ = print_eval "input_word"
  ``crepSem$eval ^state ^expression``;
val _ = print_eval "multiply_zero"
  ``crepSem$eval ^state
      (crep_arith$mul_const ^expression (0w:64 word))``;
val _ = print_eval "multiply_one"
  ``crepSem$eval ^state
      (crep_arith$mul_const ^expression (1w:64 word))``;
val _ = print_eval "multiply_power_of_two"
  ``crepSem$eval ^state
      (crep_arith$mul_const ^expression (8w:64 word))``;
val _ = print_eval "multiply_general"
  ``crepSem$eval ^state
      (crep_arith$mul_const ^expression (3w:64 word))``;
