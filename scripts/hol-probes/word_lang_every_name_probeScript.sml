load "preamble"; load "wordLangTheory";
open bossLib; open HolKernel Parse; open preamble; open wordLangTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val Peven = ``\(n:num). n MOD 2 = 0``;
val Podd  = ``\(n:num). n MOD 2 = 1``;

val nsEven = ``sptree$insert (2:num) ()
               (sptree$insert (0:num) () sptree$LN)``;
val nsMixed = ``sptree$insert (2:num) ()
                (sptree$insert (1:num) ()
                  (sptree$insert (0:num) () sptree$LN))``;
val emptyCut = ``(sptree$LN, sptree$LN) : unit spt # unit spt``;
val cutEven  = ``(^nsEven, ^nsEven) : unit spt # unit spt``;
val cutMixed = ``(^nsMixed, ^nsEven) : unit spt # unit spt``;

val _ = print_eval "en_empty" ``every_name ^Peven ^emptyCut``;
val _ = print_eval "en_even" ``every_name ^Peven ^cutEven``;
val _ = print_eval "en_mixed_bad" ``every_name ^Peven ^cutMixed``;
val _ = print_eval "en_empty_odd" ``every_name ^Podd ^emptyCut``;

val assignOk = ``wordLang$Assign (2:num) (wordLang$Const (0w:8 word)) : 8 wordLang$prog``;
val assignBad = ``wordLang$Assign (3:num) (wordLang$Const (0w:8 word)) : 8 wordLang$prog``;
val moveOk = ``wordLang$Move (0:num) ([(2:num,4:num)] : (num # num) list) : 8 wordLang$prog``;
val moveBad = ``wordLang$Move (0:num) ([(2:num,3:num)] : (num # num) list) : 8 wordLang$prog``;
val _ = print_eval "ev_assign_ok" ``every_var ^Peven ^assignOk``;
val _ = print_eval "ev_assign_bad" ``every_var ^Peven ^assignBad``;
val _ = print_eval "ev_move_ok" ``every_var ^Peven ^moveOk``;
val _ = print_eval "ev_move_bad" ``every_var ^Peven ^moveBad``;
val _ = print_eval "ev_skip" ``every_var ^Podd (wordLang$Skip : 8 wordLang$prog)``;
val _ = print_eval "ev_seq_bad" ``every_var ^Peven
  (wordLang$Seq ^assignOk ^assignBad : 8 wordLang$prog)``;
val _ = print_eval "ev_call_none" ``every_var ^Peven
  (wordLang$Call NONE NONE [(2:num)] NONE : 8 wordLang$prog)``;
val _ = print_eval "ev_alloc_ok" ``every_var ^Peven
  (wordLang$Alloc (2:num) ^cutEven : 8 wordLang$prog)``;
val _ = print_eval "ev_alloc_bad" ``every_var ^Peven
  (wordLang$Alloc (2:num) ^cutMixed : 8 wordLang$prog)``;

val _ = print_eval "esv_alloc_ok" ``every_stack_var ^Peven
  (wordLang$Alloc (2:num) ^cutEven : 8 wordLang$prog)``;
val _ = print_eval "esv_alloc_bad" ``every_stack_var ^Peven
  (wordLang$Alloc (2:num) ^cutMixed : 8 wordLang$prog)``;
val _ = print_eval "esv_call_none" ``every_stack_var ^Podd
  (wordLang$Call NONE NONE [] NONE : 8 wordLang$prog)``;
val _ = print_eval "esv_ffi_ok" ``every_stack_var ^Peven
  (wordLang$FFI (strlit "x") (2:num) (4:num) (6:num) (8:num) ^cutEven : 8 wordLang$prog)``;
val _ = print_eval "esv_ffi_regs_ignored" ``every_stack_var ^Peven
  (wordLang$FFI (strlit "x") (2:num) (4:num) (6:num) (9:num) ^cutEven : 8 wordLang$prog)``;
val _ = print_eval "esv_seq_bad" ``every_stack_var ^Podd
  (wordLang$Seq (wordLang$Skip : 8 wordLang$prog) (wordLang$Alloc (2:num) ^cutMixed) :
    8 wordLang$prog)``;
