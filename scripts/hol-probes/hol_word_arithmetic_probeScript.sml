(* Direct source and EVAL probe for HOL4's polymorphic word arithmetic. *)
load "bossLib";
load "wordsTheory";
open bossLib;
open HolKernel Parse;
open wordsTheory;

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

val _ = print_thm "word_add_definition" word_add_def;
val _ = print_thm "word_mul_definition" word_mul_def;
val _ = print_thm "word_sub_definition" word_sub_def;
val _ = print_thm "word_add_n2w" word_add_n2w;
val _ = print_thm "word_mul_n2w" word_mul_n2w;
val _ = print_thm "word_2comp_n2w" word_2comp_n2w;
val _ = print_conv "add_3_5_8"
  (SIMP_CONV (srw_ss()) [word_add_n2w] ``(n2w 3 + n2w 5 : 8 word)``);
val _ = print_conv "mul_3_5_8"
  (SIMP_CONV (srw_ss()) [word_mul_n2w] ``(n2w 3 * n2w 5 : 8 word)``);
val _ = print_conv "sub_3_5_8"
  (SIMP_CONV (srw_ss() ++ ARITH_ss)
    [word_sub_def, word_2comp_n2w, word_add_n2w, dimword_def,
      dimindex_8, w2n_n2w]
    ``(n2w 3 - n2w 5 : 8 word)``);
