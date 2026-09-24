load "preamble"; load "wordConvsTheory";
open bossLib; open HolKernel Parse; open preamble; open wordConvsTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val cut3 = ``(sptree$insert 3 () sptree$LN, sptree$LN) : unit spt # unit spt``;
val cut4 = ``(sptree$insert 4 () sptree$LN, sptree$LN) : unit spt # unit spt``;
val cut2 = ``(sptree$insert 2 () sptree$LN, sptree$LN) : unit spt # unit spt``;

val pre_ok_ffi      = ``pre_alloc_conventions ((wordLang$FFI (strlit "f") 2 4 6 8 ^cut3) : 8 wordLang$prog)``;
val pre_bad_scalar  = ``pre_alloc_conventions ((wordLang$FFI (strlit "f") 3 4 6 8 ^cut3) : 8 wordLang$prog)``;
val pre_bad_cutset  = ``pre_alloc_conventions ((wordLang$FFI (strlit "f") 2 4 6 8 ^cut4) : 8 wordLang$prog)``;
val pre_bad_argconv = ``pre_alloc_conventions ((wordLang$FFI (strlit "f") 2 4 6 9 ^cut3) : 8 wordLang$prog)``;
val post_ok_move    = ``post_alloc_conventions 2 ((wordLang$Move 0 [(2,6)]) : 8 wordLang$prog)``;
val post_bad_move   = ``post_alloc_conventions 2 ((wordLang$Move 0 [(3,4)]) : 8 wordLang$prog)``;
val post_bad_bound  = ``post_alloc_conventions 2 ((wordLang$Alloc 2 ^cut2) : 8 wordLang$prog)``;
val post_ok_ret     = ``post_alloc_conventions 2 ((wordLang$Return 4 [2]) : 8 wordLang$prog)``;

val _ = print_eval "pre_ok_ffi" pre_ok_ffi;
val _ = print_eval "pre_bad_scalar" pre_bad_scalar;
val _ = print_eval "pre_bad_cutset" pre_bad_cutset;
val _ = print_eval "pre_bad_argconv" pre_bad_argconv;
val _ = print_eval "post_ok_move" post_ok_move;
val _ = print_eval "post_bad_move" post_bad_move;
val _ = print_eval "post_bad_bound" post_bad_bound;
val _ = print_eval "post_ok_ret" post_ok_ret;
