load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val badHandler = ``(SOME (2, wordLang$Skip, 6, 9) : (num # 8 wordLang$prog # num # num) option)``;
val okHandler  = ``(SOME (2, wordLang$Skip, 5, 9) : (num # 8 wordLang$prog # num # num) option)``;
val ret        = ``(SOME ([1], (sptree$LN, sptree$LN), wordLang$Skip, 10, 11)
                       : (num list # (unit spt # unit spt) # 8 wordLang$prog # num # num) option)``;
val innerBad   = ``(wordLang$Call ^ret NONE [] ^badHandler : 8 wordLang$prog)``;

val _ = print_eval "gh_call_none"
  ``good_handlers 5 (wordLang$Call NONE NONE [] NONE : 8 wordLang$prog)``;
val _ = print_eval "gh_call_ret_ok"
  ``good_handlers 5 (wordLang$Call ^ret (SOME 7) [] NONE : 8 wordLang$prog)``;
val _ = print_eval "gh_handler_ok"
  ``good_handlers 5 (wordLang$Call ^ret NONE [] ^okHandler : 8 wordLang$prog)``;
val _ = print_eval "gh_handler_bad"
  ``good_handlers 5 (wordLang$Call ^ret NONE [] ^badHandler : 8 wordLang$prog)``;
val _ = print_eval "gh_handler_body_bad"
  ``good_handlers 5 (wordLang$Call ^ret NONE []
        (SOME (2, ^innerBad, 5, 9)
           : (num # 8 wordLang$prog # num # num) option) : 8 wordLang$prog)``;
val _ = print_eval "gh_ret_body_bad"
  ``good_handlers 5 (wordLang$Call
        (SOME ([1], (sptree$LN, sptree$LN),
               ^innerBad, 10, 11)
           : (num list # (unit spt # unit spt) # 8 wordLang$prog # num # num) option)
        NONE [] NONE : 8 wordLang$prog)``;
val _ = print_eval "gh_seq_ok"
  ``good_handlers 5 (wordLang$Seq wordLang$Skip wordLang$Skip : 8 wordLang$prog)``;
val _ = print_eval "gh_seq_bad"
  ``good_handlers 5 (wordLang$Seq wordLang$Skip
        (wordLang$Loop sptree$LN ^innerBad sptree$LN)
        : 8 wordLang$prog)``;
val _ = print_eval "gh_loop_bad"
  ``good_handlers 5
        (wordLang$Loop sptree$LN ^innerBad sptree$LN
           : 8 wordLang$prog)``;
val _ = print_eval "gh_if_bad"
  ``good_handlers 5
        (wordLang$If asm$Equal 0 (asm$Reg 1) wordLang$Skip
           ^innerBad : 8 wordLang$prog)``;
val _ = print_eval "gh_mt_bad"
  ``good_handlers 5
        (wordLang$MustTerminate ^innerBad
           : 8 wordLang$prog)``;
val _ = print_eval "gh_other"
  ``good_handlers 5 (wordLang$LocValue 1 7 : 8 wordLang$prog)``;
