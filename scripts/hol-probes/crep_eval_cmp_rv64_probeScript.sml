(*
  Direct HOL observations for the crepSem Cmp evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-137 (`eval_def`:
  `eval s (Cmp op e1 e2) = case (eval s e1, eval s e2) of
     (SOME (Word a), SOME (Word b)) => SOME (Word (word_cmp op a b))
   | _ => NONE`) and cakeml/compiler/encoders/asm/asmScript.sml:83
  (`cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest`).
  Constant operands reduce to the comparison word (1 for true, 0 for false).
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

val _ = print_eval "eval_cmp_equal_true"
  ``crepSem$eval ^s0
      (crepLang$Cmp asm$Equal (crepLang$Const (5w:64 word))
        (crepLang$Const (5w:64 word)))``;

val _ = print_eval "eval_cmp_equal_false"
  ``crepSem$eval ^s0
      (crepLang$Cmp asm$Equal (crepLang$Const (5w:64 word))
        (crepLang$Const (6w:64 word)))``;

val _ = print_eval "eval_cmp_lower_true"
  ``crepSem$eval ^s0
      (crepLang$Cmp asm$Lower (crepLang$Const (3w:64 word))
        (crepLang$Const (5w:64 word)))``;

val _ = print_eval "eval_cmp_test_zero"
  ``crepSem$eval ^s0
      (crepLang$Cmp asm$Test (crepLang$Const (0xF0w:64 word))
        (crepLang$Const (0x10w:64 word)))``;

val _ = print_eval "eval_cmp_test_disjoint"
  ``crepSem$eval ^s0
      (crepLang$Cmp asm$Test (crepLang$Const (0xF0w:64 word))
        (crepLang$Const (0x0Fw:64 word)))``;