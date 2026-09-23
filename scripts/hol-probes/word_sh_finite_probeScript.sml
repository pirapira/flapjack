(* Direct HOL4 probe for wordLang's shift operation and width guard. *)
load "bossLib";
load "wordsTheory";
load "wordLangTheory";
open bossLib;
open HolKernel Parse;
open wordsTheory;
open wordLangTheory;

fun print_thm label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  )

fun print_conv label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  )

val _ = print_thm "word_sh_definition" wordLangTheory.word_sh_def;
val _ = print_thm "dimindex8" wordsTheory.dimindex_8;
val _ = print_conv "lsl_zero"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Lsl (3w : 8 word) 0``);
val _ = print_conv "lsl_one"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Lsl (3w : 8 word) 1``);
val _ = print_conv "lsr_max_valid"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Lsr (128w : 8 word) 7``);
val _ = print_conv "asr_one"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Asr (128w : 8 word) 1``);
val _ = print_conv "ror_one"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Ror (3w : 8 word) 1``);
val _ = print_conv "lsl_width"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Lsl (3w : 8 word) 8``);
val _ = print_conv "lsl_above_width"
  (SIMP_CONV (srw_ss()) [wordLangTheory.word_sh_def, wordsTheory.dimindex_8]
    ``word_sh Lsl (3w : 8 word) 9``);
