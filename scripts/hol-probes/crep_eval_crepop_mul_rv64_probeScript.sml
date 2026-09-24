(*
  Direct HOL observations for the crepSem Crepop Mul evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:119-124 (`eval_def`:
  `eval s (Crepop op es) = case (OPT_MMAP (eval s) es) of
     SOME ws => if EVERY is-word ws then OPTION_MAP Word (crep_op op (MAP unword ws))
                else NONE
   | _ => NONE`) and
  cakeml/pancake/semantics/crepSemScript.sml:85-88 (`crep_op_def`:
  `crep_op Mul [w1;w2] = SOME (w1 * w2)` and `crep_op _ _ = NONE`).
  Constant operands reduce to the product; wrong arity fails.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(64,unit) crepSem$state)``;
val s0 = ``(^s with <|
    memory := (\(_ : 64 word). Word (0w:64 word));
    memaddrs := {} |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "eval_crepop_mul_const"
  ``crepSem$eval ^s0
      (crepLang$Crepop crepLang$Mul
        [crepLang$Const (6w:64 word); crepLang$Const (7w:64 word)])``;

val _ = print_eval "eval_crepop_mul_other"
  ``crepSem$eval ^s0
      (crepLang$Crepop crepLang$Mul
        [crepLang$Const (5w:64 word); crepLang$Const (6w:64 word)])``;

val _ = print_eval "eval_crepop_mul_three"
  ``crepSem$eval ^s0
      (crepLang$Crepop crepLang$Mul
        [crepLang$Const (2w:64 word); crepLang$Const (3w:64 word);
         crepLang$Const (4w:64 word)])``;

val _ = print_eval "eval_crepop_mul_one"
  ``crepSem$eval ^s0
      (crepLang$Crepop crepLang$Mul [crepLang$Const (2w:64 word)])``;

val _ = print_eval "eval_crepop_mul_empty"
  ``crepSem$eval ^s0 (crepLang$Crepop crepLang$Mul [])``;