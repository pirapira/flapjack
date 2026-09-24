(* Direct HOL4 probe for the wordLang word_op list-fold definition. *)
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

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  end

val _ = print_thm "word_op_definition" wordLangTheory.word_op_def;
val _ = print_eval "add_pair" ``word_op Add ([3w; 5w] : 8 word list)``;
val _ = print_eval "add_empty" ``word_op Add ([] : 8 word list)``;
val _ = print_eval "and_empty" ``word_op And ([] : 8 word list)``;
val _ = print_eval "or_empty" ``word_op Or ([] : 8 word list)``;
val _ = print_eval "xor_empty" ``word_op Xor ([] : 8 word list)``;
val _ = print_eval "sub_pair" ``word_op Sub ([3w; 5w] : 8 word list)``;
val _ = print_eval "sub_one" ``word_op Sub ([3w] : 8 word list)``;
val _ = print_eval "sub_three" ``word_op Sub ([1w; 2w; 3w] : 8 word list)``;
