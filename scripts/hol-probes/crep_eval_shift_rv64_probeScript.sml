(*
  Direct HOL observations for the crepSem Shift evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:131-133 (`eval_def`:
  `eval s (Shift sh e1 e2) = case (eval s e1, eval s e2) of
     (SOME (Word w1), SOME (Word w2)) => OPTION_MAP Word (word_sh sh w1 (w2n w2))
   | _ => NONE`) and
  cakeml/compiler/backend/wordLangScript.sml:313-321 (`word_sh_def`: an amount
  equal to the word width is invalid, amount zero stays valid; Lsl/Lsr/Asr/Ror).
  Constant operands reduce to the shifted word.
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

val _ = print_eval "eval_shift_lsl_const"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Lsl
        (crepLang$Const (1w:64 word)) (crepLang$Const (3w:64 word)))``;

val _ = print_eval "eval_shift_lsr_const"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Lsr
        (crepLang$Const (16w:64 word)) (crepLang$Const (2w:64 word)))``;

val _ = print_eval "eval_shift_asr_const"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Asr
        (crepLang$Const (0x8000000000000000w:64 word)) (crepLang$Const (4w:64 word)))``;

val _ = print_eval "eval_shift_ror_const"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Ror
        (crepLang$Const (1w:64 word)) (crepLang$Const (1w:64 word)))``;

val _ = print_eval "eval_shift_amount_zero"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Lsl
        (crepLang$Const (7w:64 word)) (crepLang$Const (0w:64 word)))``;

val _ = print_eval "eval_shift_amount_width"
  ``crepSem$eval ^s0
      (crepLang$Shift ast$Lsl
        (crepLang$Const (7w:64 word)) (crepLang$Const (64w:64 word)))``;