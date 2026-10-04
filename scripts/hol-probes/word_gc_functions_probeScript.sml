load "preamble"; load "word_gcFunctionsTheory"; load "word_simpProofTheory"; load "gc_sharedTheory";
open bossLib; open HolKernel Parse; open preamble; open word_gcFunctionsTheory; open gc_sharedTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;

val mem = ``(\a:64 word. if a = 1008w then Word 0x1000000000002w
                          else (Word a : 64 word_loc))``;
val fwd = ``(\a:64 word. if a = 1008w then Word 0x40w else (Word a : 64 word_loc))``;

val _ = print_eval "gc_ptr_to_addr" ``ptr_to_addr ^conf (1000w:64 word) 0x1234w``;
val _ = print_eval "gc_update_addr" ``update_addr ^conf (5w:64 word) 0x1237w``;
val _ = print_eval "gc_decode_length" ``decode_length ^conf (0x3000000000002w:64 word)``;
val _ = print_eval "gc_is_ref_header_8" ``is_ref_header (8w:64 word)``;
val _ = print_eval "gc_is_ref_header_c" ``is_ref_header (12w:64 word)``;
val _ = print_eval "gc_memcpy"
  ``let (b,m1,c) = memcpy (2w:64 word) (100w:64 word) (200w:64 word) (\a. Word a) UNIV in
      (b, m1 200w, m1 208w, m1 216w, c)``;
val _ = print_eval "gc_memcpy_dom"
  ``let (b,m1,c) = memcpy (2w:64 word) (100w:64 word) (200w:64 word) (\a. Word a) {100w:64 word; 200w; 108w} in c``;
val _ = print_eval "gc_move_loc"
  ``let (w1,i1,pa1,m1,c) = word_gc_move ^conf (Loc 3 0, 7w:64 word, 2000w, 1000w,
      (\a. Word a), UNIV) in (w1, i1, pa1, c)``;
val _ = print_eval "gc_move_loc_nonzero"
  ``let (w1,i1,pa1,m1,c) = word_gc_move ^conf (Loc 3 4, 7w:64 word, 2000w, 1000w,
      (\a. Word a), UNIV) in (w1, i1, pa1, c)``;
val _ = print_eval "gc_move_small"
  ``let (w1,i1,pa1,m1,c) = word_gc_move ^conf (Word 4w, 7w:64 word, 2000w, 1000w,
      (\a. Word a), UNIV) in (w1, i1, pa1, c)``;
val _ = print_eval "gc_move_copy"
  ``let (w1,i1,pa1,m1,c) = word_gc_move ^conf (Word 0x101w, 7w:64 word, 2000w, 1000w,
      ^mem, UNIV) in (w1, i1, pa1, m1 1008w, m1 2000w, m1 2008w, c)``;
val _ = print_eval "gc_move_fwd"
  ``let (w1,i1,pa1,m1,c) = word_gc_move ^conf (Word 0x101w, 7w:64 word, 2000w, 1000w,
      ^fwd, UNIV) in (w1, i1, pa1, m1 1008w, c)``;
val _ = print_eval "gc_gen_move_copy"
  ``let (w1,i1,pa1,ib1,pb1,m1,c) = word_gen_gc_move ^conf (Word 0x101w, 7w:64 word, 2000w,
      50w, 3000w, 1000w, ^mem, UNIV) in (w1, i1, pa1, ib1, pb1, m1 1008w, m1 2000w, c)``;
val _ = print_eval "gc_gen_move_ref"
  ``let (w1,i1,pa1,ib1,pb1,m1,c) = word_gen_gc_move ^conf (Word 0x101w, 7w:64 word, 2000w,
      50w, 3000w, 1000w,
      (\a:64 word. if a = 1008w then Word 0x100000000000Aw else (Word a : 64 word_loc)),
      UNIV) in (w1, i1, pa1, ib1, pb1, m1 1008w, m1 2984w, m1 2992w, c)``;
val _ = print_eval "gc_partial_move_outside"
  ``let (w1,i1,pa1,m1,c) = word_gen_gc_partial_move ^conf (Word 0x101w, 7w:64 word, 2000w,
      1000w, ^mem, UNIV, 16w, 32w) in (w1, i1, pa1, c)``;
val _ = print_eval "gc_partial_move_inside"
  ``let (w1,i1,pa1,m1,c) = word_gen_gc_partial_move ^conf (Word 0x101w, 7w:64 word, 2000w,
      1000w, ^mem, UNIV, 8w, 32w) in (w1, i1, pa1, m1 1008w, c)``;
val _ = print_eval "gc_move_roots"
  ``let (ws,i1,pa1,m1,c) = word_gc_move_roots ^conf ([Word 4w; Loc 1 0; Word 0x101w],
      7w:64 word, 2000w, 1000w, ^mem, UNIV) in (ws, i1, pa1, c)``;
val _ = print_eval "gc_move_list"
  ``let (a2,i1,pa1,m1,c) = word_gc_move_list ^conf (500w, 2w, 7w:64 word, 2000w, 1000w,
      (\a:64 word. if a = 1008w then Word 0x1000000000002w else
                   if a = 500w then Word 0x101w else (Word 4w : 64 word_loc)), UNIV)
    in (a2, i1, pa1, m1 500w, m1 508w, c)``;
val _ = print_eval "gc_glob_real" ``glob_real ^conf (1000w:64 word) (Word 0x200w)``;
val _ = print_eval "gc_glob_real_loc" ``glob_real ^conf (1000w:64 word) (Loc 2 3)``;
val _ = print_eval "gc_new_trig_small" ``new_trig (100w:64 word) 8w [10]``;
val _ = print_eval "gc_new_trig_big" ``new_trig (100w:64 word) 200w [1]``;
val _ = print_eval "gc_new_trig_aligned" ``new_trig (1000w:64 word) 200w [1]``;
val _ = print_eval "gc_new_trig_unaligned" ``new_trig (1000w:64 word) 201w [1]``;
val _ = print_eval "gc_is_gc_const_even" ``word_simp$is_gc_const (6w:64 word)``;
val _ = print_eval "gc_is_gc_const_odd" ``word_simp$is_gc_const (7w:64 word)``;
val _ = print_eval "gc_is_gc_word_const_loc" ``word_simpProof$is_gc_word_const (Loc 1 2 : 64 word_loc)``;
val _ = print_eval "gc_is_gc_word_const_odd" ``word_simpProof$is_gc_word_const (Word 7w : 64 word_loc)``;

val _ = print_eval "gc_refs_to_addresses_empty"
  ``refs_to_addresses ([] : (64 word, 64 word) heap_element list)``;
val _ = print_eval "gc_refs_to_addresses_basic"
  ``refs_to_addresses ([DataElement [(Pointer 0 (1000w:64 word)); (Data (2000w:64 word))] 2 (9w:64 word);
                        Unused 3;
                        ForwardPointer 1 (1000w:64 word) 4])``;
val _ = print_eval "gc_refs_to_addresses_skip"
  ``refs_to_addresses ([Unused 1;
                        DataElement [(Data (3000w:64 word))] 5 (7w:64 word)] :
                       (64 word, 64 word) heap_element list)``;
