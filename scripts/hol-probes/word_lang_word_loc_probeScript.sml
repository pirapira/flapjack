load "preamble";
load "wordLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

(* word_loc: Word ('a word) | Loc num num  (wordLangScript.sml:331-333) *)
val _ = print_eval "wl_word" ``(Word (7w:8 word) : 8 wordLang$word_loc)``;
val _ = print_eval "wl_loc" ``(Loc 3 4 : 8 wordLang$word_loc)``;
val _ = print_eval "wl_distinct" ``((Word (0w:8 word) : 8 wordLang$word_loc) = Loc 0 0)``;
val _ = print_eval "wl_match" ``((case (Loc 3 4 : 8 wordLang$word_loc) of Word v => 1n | Loc blk off => 2n))``;