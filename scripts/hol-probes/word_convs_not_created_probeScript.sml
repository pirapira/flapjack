load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val empty = ``(sptree$LN : unit spt)``;
val skipP = ``(wordLang$Skip : 8 wordLang$prog)``;

val _ = print_eval "nac_skip" ``wordConvs$no_alloc ^skipP``;
val _ = print_eval "nac_alloc_empty"
  ``wordConvs$no_alloc (wordLang$Alloc 0 (^empty,^empty) : 8 wordLang$prog)``;
val _ = print_eval "nac_alloc_other"
  ``wordConvs$no_alloc (wordLang$Alloc 1 (^empty,^empty) : 8 wordLang$prog)``;
val _ = print_eval "nac_seq_alloc"
  ``wordConvs$no_alloc
      (wordLang$Seq ^skipP (wordLang$Alloc 0 (^empty,^empty)) : 8 wordLang$prog)``;
val _ = print_eval "nac_mt_skip"
  ``wordConvs$no_alloc (wordLang$MustTerminate ^skipP : 8 wordLang$prog)``;
val _ = print_eval "nins_install_empty"
  ``wordConvs$no_install
      (wordLang$Install 0 0 0 0 (^empty,^empty) : 8 wordLang$prog)``;
val _ = print_eval "nmt_mt_skip"
  ``wordConvs$no_mt (wordLang$MustTerminate ^skipP : 8 wordLang$prog)``;
val _ = print_eval "nsi_skip" ``wordConvs$no_share_inst ^skipP``;
val _ = print_eval "nsi_share_arb"
  ``wordConvs$no_share_inst
      (wordLang$ShareInst ARB 0 (wordLang$Var 0) : 8 wordLang$prog)``;
val _ = print_eval "nsi_share_load"
  ``wordConvs$no_share_inst
      (wordLang$ShareInst asm$Load 0 (wordLang$Var 0) : 8 wordLang$prog)``;
val _ = print_eval "nsi_seq_share"
  ``wordConvs$no_share_inst
      (wordLang$Seq ^skipP
        (wordLang$ShareInst ARB 0 (wordLang$Var 0)) : 8 wordLang$prog)``;
val _ = print_eval "nsi_call_none"
  ``wordConvs$no_share_inst
      (wordLang$Call NONE NONE [] NONE : 8 wordLang$prog)``;
val _ = print_eval "nsi_call_handler_mt"
  ``wordConvs$no_share_inst
      (wordLang$Call NONE NONE []
        (SOME (0, wordLang$MustTerminate ^skipP, 0, 0)) : 8 wordLang$prog)``;
val _ = print_eval "nmt_call_handler_mt"
  ``wordConvs$no_mt
      (wordLang$Call NONE NONE []
        (SOME (0, wordLang$MustTerminate ^skipP, 0, 0)) : 8 wordLang$prog)``;
val _ = print_eval "nac_install_empty"
  ``wordConvs$no_alloc
      (wordLang$Install 0 0 0 0 (^empty,^empty) : 8 wordLang$prog)``;