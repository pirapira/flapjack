(*
  Direct HOL observations for the crepSem Op evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-137 (`eval_def`:
  `eval s (Op op args) = case OPT_MMAP (eval s) args of
     SOME vs => word_op op vs | _ => NONE`) and
  cakeml/compiler/backend/wordLangScript.sml:302-311 (`word_op_def`: Add, And,
  Or, and Xor fold over all operands; Sub is defined for exactly two operands).
  Constant operands reduce to the folded word.
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

val _ = print_eval "eval_op_add_const"
  ``crepSem$eval ^s0
      (crepLang$Op asm$Add
        [crepLang$Const (3w:64 word); crepLang$Const (4w:64 word)])``;

val _ = print_eval "eval_op_sub_const"
  ``crepSem$eval ^s0
      (crepLang$Op asm$Sub
        [crepLang$Const (7w:64 word); crepLang$Const (2w:64 word)])``;

val _ = print_eval "eval_op_and_const"
  ``crepSem$eval ^s0
      (crepLang$Op asm$And
        [crepLang$Const (0xF0w:64 word); crepLang$Const (0x3Cw:64 word)])``;

val _ = print_eval "eval_op_add_empty"
  ``crepSem$eval ^s0 (crepLang$Op asm$Add [])``;

val _ = print_eval "eval_op_sub_arity"
  ``crepSem$eval ^s0
      (crepLang$Op asm$Sub [crepLang$Const (7w:64 word)])``;