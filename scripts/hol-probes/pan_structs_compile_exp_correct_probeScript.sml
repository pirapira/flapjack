(* Direct HOL-EVAL instances of pan_structsProof$compile_exp_correct for its
   expression constructors, including Local and Global Var and NStruct. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

fun print_simp label rewrites q =
  let
    val th = SIMP_CONV (srw_ss()) rewrites q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val ctxt =
  ``<| structs := [(strlit "Pair", [(strlit "left", One);
                                    (strlit "right", One)])];
      locals := [(strlit "local", Comb [One; One])];
      globals := [] |>``;
val state = ``(s:(8,'ffi) panSem$state)``;
val local_state =
  ``^state with <|
      structs := [(strlit "Pair", <| fields := [(strlit "left", One);
                                                   (strlit "right", One)];
                                       size := 2 |> )];
      locals := FUPDATE FEMPTY
        (strlit "local", RStruct [ValWord (3w:8 word); ValWord (5w:8 word)]);
      globals := FEMPTY
    |>``;
val local_value = ``RStruct [ValWord (3w:8 word); ValWord (5w:8 word)]``;
val local_expression = ``(panLang$Var Local (strlit "local") : 8 panLang$exp)``;

val _ = print_simp "compile_exp_correct_local_var"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def,
   FLOOKUP_UPDATE,
   FLOOKUP_FMAP_MAP2,
   FLOOKUP_FUN_FMAP]
  ``(pan_structs$old_exp_shape ^ctxt ^local_expression,
     panSem$shape_of ^local_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^local_value,
     panSem$eval (^local_state) ^local_expression = SOME ^local_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^local_expression) =
       SOME (pan_structsProof$convert_v ^local_value))``;

val global_ctxt = ``^ctxt with globals := [(strlit "global", One)]``;
val global_state = ``^local_state with globals := FUPDATE FEMPTY
  (strlit "global", ValWord (7w:8 word))``;
val global_value = ``ValWord (7w:8 word)``;
val global_expression = ``(panLang$Var Global (strlit "global") : 8 panLang$exp)``;

val _ = print_simp "compile_exp_correct_global_var"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def,
   FLOOKUP_UPDATE,
   FLOOKUP_FMAP_MAP2,
   FLOOKUP_FUN_FMAP]
  ``(pan_structs$old_exp_shape ^global_ctxt ^global_expression,
     panSem$shape_of ^global_value,
     pan_structsProof$v_flds_ok (^global_state).structs ^global_value,
     panSem$eval (^global_state) ^global_expression = SOME ^global_value,
     panSem$eval (pan_structsProof$convert_s ^global_ctxt ^global_state)
       (pan_structs$compile_exp ^global_ctxt ^global_expression) =
       SOME (pan_structsProof$convert_v ^global_value))``;

val const_word = ``13w:8 word``;
val const_value = ``ValWord ^const_word``;
val const_expression = ``(panLang$Const ^const_word : 8 panLang$exp)``;
val _ = print_simp "compile_exp_correct_const"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def,
   FLOOKUP_UPDATE,
   FLOOKUP_FMAP_MAP2,
     FLOOKUP_FUN_FMAP]
  ``(pan_structs$old_exp_shape ^ctxt ^const_expression,
     panSem$shape_of ^const_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^const_value,
     panSem$eval (^local_state) ^const_expression = SOME ^const_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^const_expression) =
       SOME (pan_structsProof$convert_v ^const_value))``;

val mmap_expressions =
  ``[(panLang$Const (3w:8 word)); (panLang$Const (5w:8 word))]``;
val mmap_values = ``[ValWord (3w:8 word); ValWord (5w:8 word)]``;
val _ = print_simp "compile_exp_correct_mmap_nonempty"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   panSemTheory.eval_def,
   DISJ_IMP_THM,
   FORALL_AND_THM]
  ``(OPT_MMAP (panSem$eval ^local_state) ^mmap_expressions = SOME ^mmap_values,
     (!e. MEM e ^mmap_expressions ==>
       !v. panSem$eval ^local_state e = SOME v ==>
         panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
           (pan_structs$compile_exp ^ctxt e) =
             SOME (pan_structsProof$convert_v v)),
     OPT_MMAP (panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state))
       (pan_structs$compile_exps ^ctxt ^mmap_expressions) =
         SOME (MAP pan_structsProof$convert_v ^mmap_values))``;

val rstruct_value =
  ``RStruct [ValWord (3w:8 word); ValWord (5w:8 word)]``;
val rstruct_expression =
  ``(panLang$RStruct [panLang$Const (3w:8 word);
                      panLang$Const (5w:8 word)] : 8 panLang$exp)``;
val _ = print_simp "compile_exp_correct_rstruct"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def]
  ``(pan_structs$old_exp_shape ^ctxt ^rstruct_expression,
     panSem$shape_of ^rstruct_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^rstruct_value,
     panSem$eval ^local_state ^rstruct_expression = SOME ^rstruct_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^rstruct_expression) =
         SOME (pan_structsProof$convert_v ^rstruct_value))``;
val _ = print_eval "compile_exp_correct_rstruct_eval"
  ``(pan_structs$old_exp_shape ^ctxt ^rstruct_expression,
     panSem$shape_of ^rstruct_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^rstruct_value,
     panSem$eval ^local_state ^rstruct_expression = SOME ^rstruct_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^rstruct_expression) =
         SOME (pan_structsProof$convert_v ^rstruct_value))``;

val nstruct_value = ``NStruct (strlit "Pair")
  [(strlit "left", ValWord (3w:8 word));
   (strlit "right", ValWord (5w:8 word))]``;
val nstruct_expression = ``(panLang$NStruct (strlit "Pair")
  [(strlit "left", panLang$Const (3w:8 word));
   (strlit "right", panLang$Const (5w:8 word))] : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_nstruct"
  ``(pan_structs$old_exp_shape ^ctxt ^nstruct_expression,
     panSem$shape_of ^nstruct_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^nstruct_value,
     panSem$eval ^local_state ^nstruct_expression = SOME ^nstruct_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^nstruct_expression) =
       SOME (pan_structsProof$convert_v ^nstruct_value))``;
val nfield_value = ``ValWord (5w:8 word)``;
val nfield_expression = ``(panLang$NField (strlit "right") ^nstruct_expression
  : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_nfield"
  ``(pan_structs$old_exp_shape ^ctxt ^nfield_expression,
     panSem$shape_of ^nfield_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^nfield_value,
     panSem$eval ^local_state ^nfield_expression = SOME ^nfield_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^nfield_expression) =
       SOME (pan_structsProof$convert_v ^nfield_value))``;
val rfield_value = ``ValWord (5w:8 word)``;
val rfield_expression = ``(panLang$RField 1 ^local_expression
  : 8 panLang$exp)``;
val _ = print_simp "compile_exp_correct_rfield"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def,
   LLOOKUP_THM,
   FLOOKUP_UPDATE,
   FLOOKUP_FMAP_MAP2,
   FLOOKUP_FUN_FMAP]
  ``(pan_structs$old_exp_shape ^ctxt ^rfield_expression,
     panSem$shape_of ^rfield_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^rfield_value,
     panSem$eval ^local_state ^rfield_expression = SOME ^rfield_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^rfield_expression) =
       SOME (pan_structsProof$convert_v ^rfield_value))``;

val op_value = ``ValWord (8w:8 word)``;
val op_expression = ``(panLang$Op Add
  [panLang$Const (3w:8 word); panLang$Const (5w:8 word)] : 8 panLang$exp)``;
val _ = print_simp "compile_exp_correct_op"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsTheory.compile_exp_def,
   pan_structsTheory.old_exp_shape_def,
   panSemTheory.eval_def,
   panSemTheory.shape_of_def,
   pan_structsProofTheory.v_flds_ok_def,
   wordLangTheory.word_op_def]
  ``(pan_structs$old_exp_shape ^ctxt ^op_expression,
     panSem$shape_of ^op_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^op_value,
     panSem$eval ^local_state ^op_expression = SOME ^op_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^op_expression) =
       SOME (pan_structsProof$convert_v ^op_value))``;

val load_state =
  ``^local_state with <|
      memory := (\a:8 word. if a = 0w then Word (3w:8 word)
                              else if a = 1w then Word (5w:8 word) else ARB);
      memaddrs := {0w; 1w}; sh_memaddrs := {} |>``;
val load_value = ``RStruct [ValWord (3w:8 word); ValWord (5w:8 word)]``;
val load_expression =
  ``(panLang$Load (Comb [One; One]) (panLang$Const (0w:8 word))
      : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_load"
  ``(pan_structs$old_exp_shape ^ctxt ^load_expression,
     panSem$shape_of ^load_value,
     pan_structsProof$v_flds_ok (^load_state).structs ^load_value,
     panSem$eval ^load_state ^load_expression = SOME ^load_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^load_state)
       (pan_structs$compile_exp ^ctxt ^load_expression) =
         SOME (pan_structsProof$convert_v ^load_value))``;
val load_out_of_domain_state = ``^load_state with memaddrs := {1w}``;
val _ = print_eval "compile_exp_correct_load_out_of_domain"
  ``(pan_structs$old_exp_shape ^ctxt ^load_expression,
     panSem$shape_of ^load_value,
     pan_structsProof$v_flds_ok (^load_out_of_domain_state).structs ^load_value,
     panSem$eval ^load_out_of_domain_state ^load_expression = SOME ^load_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^load_out_of_domain_state)
       (pan_structs$compile_exp ^ctxt ^load_expression) =
         SOME (pan_structsProof$convert_v ^load_value))``;

val nested_load_ctxt =
  ``<| structs := [(strlit "Pair", [(strlit "inner", Named (strlit "Inner"));
                                     (strlit "last", One)]);
                    (strlit "Inner", [(strlit "left", One);
                                      (strlit "right", One)])];
      locals := []; globals := [] |>``;
val nested_load_state =
  ``^state with <|
      structs := [(strlit "Pair", <| fields := [(strlit "inner", Named (strlit "Inner"));
                                                   (strlit "last", One)]; size := 3 |>);
                  (strlit "Inner", <| fields := [(strlit "left", One);
                                                    (strlit "right", One)]; size := 2 |> )];
      memory := (\a:8 word. if a = 0w then Word (7w:8 word)
                            else if a = 1w then Word (11w:8 word)
                            else if a = 2w then Word (13w:8 word) else ARB);
      memaddrs := {0w; 1w; 2w}; sh_memaddrs := {} |>``;
val nested_load_value =
  ``NStruct (strlit "Pair")
      [(strlit "inner", NStruct (strlit "Inner")
        [(strlit "left", ValWord (7w:8 word));
         (strlit "right", ValWord (11w:8 word))]);
       (strlit "last", ValWord (13w:8 word))]``;
val nested_load_expression =
  ``(panLang$Load (Named (strlit "Pair")) (panLang$Const (0w:8 word))
      : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_load_nested_named"
  ``(pan_structs$old_exp_shape ^nested_load_ctxt ^nested_load_expression,
     panSem$shape_of ^nested_load_value,
     pan_structsProof$v_flds_ok (^nested_load_state).structs ^nested_load_value,
     panSem$eval ^nested_load_state ^nested_load_expression = SOME ^nested_load_value,
     panSem$eval (pan_structsProof$convert_s ^nested_load_ctxt ^nested_load_state)
       (pan_structs$compile_exp ^nested_load_ctxt ^nested_load_expression) =
       SOME (pan_structsProof$convert_v ^nested_load_value))``;

val _ = print_eval "compile_exp_correct_base_addr"
  ``(pan_structs$old_exp_shape ^ctxt panLang$BaseAddr,
     panSem$shape_of (ValWord (^state).base_addr),
     pan_structsProof$v_flds_ok (^state).structs (ValWord (^state).base_addr),
     panSem$eval ^state panLang$BaseAddr = SOME (ValWord (^state).base_addr),
     panSem$eval (pan_structsProof$convert_s ^ctxt ^state)
       (pan_structs$compile_exp ^ctxt panLang$BaseAddr) =
       SOME (pan_structsProof$convert_v (ValWord (^state).base_addr)))``;
val _ = print_eval "compile_exp_correct_top_addr"
  ``(pan_structs$old_exp_shape ^ctxt panLang$TopAddr,
     panSem$shape_of (ValWord (^state).top_addr),
     pan_structsProof$v_flds_ok (^state).structs (ValWord (^state).top_addr),
     panSem$eval ^state panLang$TopAddr = SOME (ValWord (^state).top_addr),
     panSem$eval (pan_structsProof$convert_s ^ctxt ^state)
       (pan_structs$compile_exp ^ctxt panLang$TopAddr) =
       SOME (pan_structsProof$convert_v (ValWord (^state).top_addr)))``;
val _ = print_eval "compile_exp_correct_bytes_in_word"
  ``(pan_structs$old_exp_shape ^ctxt panLang$BytesInWord,
     panSem$shape_of (ValWord byte$bytes_in_word),
     pan_structsProof$v_flds_ok (^state).structs (ValWord byte$bytes_in_word),
     panSem$eval ^state panLang$BytesInWord = SOME (ValWord byte$bytes_in_word),
     panSem$eval (pan_structsProof$convert_s ^ctxt ^state)
       (pan_structs$compile_exp ^ctxt panLang$BytesInWord) =
       SOME (pan_structsProof$convert_v (ValWord byte$bytes_in_word)))``;

val load_byte_state =
  ``^local_state with <|
      memory := (\a:8 word. if a = 0w then Word (19w:8 word) else ARB);
      memaddrs := {0w}; sh_memaddrs := {}; be := F |>``;
val load_byte_value = ``ValWord (19w:8 word)``;
val load_byte_expression =
  ``(panLang$LoadByte (panLang$Const (0w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_load_byte"
  ``(pan_structs$old_exp_shape ^ctxt ^load_byte_expression,
     panSem$shape_of ^load_byte_value,
     pan_structsProof$v_flds_ok (^load_byte_state).structs ^load_byte_value,
     panSem$eval ^load_byte_state ^load_byte_expression = SOME ^load_byte_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^load_byte_state)
       (pan_structs$compile_exp ^ctxt ^load_byte_expression) =
       SOME (pan_structsProof$convert_v ^load_byte_value))``;
val load_byte_out_of_domain_state =
  ``^load_byte_state with memaddrs := {}``;
val _ = print_eval "compile_exp_correct_load_byte_out_of_domain"
  ``panSem$eval ^load_byte_out_of_domain_state ^load_byte_expression``;

val load32_64_state =
  ``(s:(64,'ffi) panSem$state) with <|
      structs := []; locals := FEMPTY; globals := FEMPTY;
      memory := (\a:64 word. if a = 8w then
        Word (0x8877665544332211w:64 word) else ARB);
      memaddrs := {8w}; sh_memaddrs := {}; be := F |>``;
val load32_64_value = ``ValWord (0x44332211w:64 word)``;
val load32_64_ctxt = ``<| structs := []; locals := []; globals := [] |>``;
val load32_64_expression =
  ``(panLang$Load32 (panLang$Const (8w:64 word)) : 64 panLang$exp)``;
val _ = print_eval "compile_exp_correct_load32_le_success"
  ``(pan_structs$old_exp_shape ^load32_64_ctxt ^load32_64_expression,
     panSem$shape_of ^load32_64_value,
     pan_structsProof$v_flds_ok (^load32_64_state).structs ^load32_64_value,
     panSem$eval ^load32_64_state ^load32_64_expression = SOME ^load32_64_value,
     panSem$eval (pan_structsProof$convert_s ^load32_64_ctxt ^load32_64_state)
       (pan_structs$compile_exp ^load32_64_ctxt ^load32_64_expression) =
       SOME (pan_structsProof$convert_v ^load32_64_value))``;

val panop_value = ``ValWord (15w:8 word)``;
val panop_expression =
  ``(panLang$Panop Mul [panLang$Const (3w:8 word);
                        panLang$Const (5w:8 word)] : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_panop_mul"
  ``(pan_structs$old_exp_shape ^ctxt ^panop_expression,
     panSem$shape_of ^panop_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^panop_value,
     panSem$eval ^local_state ^panop_expression = SOME ^panop_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^panop_expression) =
       SOME (pan_structsProof$convert_v ^panop_value))``;

val cmp_value = ``ValWord (1w:8 word)``;
val cmp_expression =
  ``(panLang$Cmp Equal (panLang$Const (3w:8 word))
       (panLang$Const (3w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_cmp_equal"
  ``(pan_structs$old_exp_shape ^ctxt ^cmp_expression,
     panSem$shape_of ^cmp_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^cmp_value,
     panSem$eval ^local_state ^cmp_expression = SOME ^cmp_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^cmp_expression) =
       SOME (pan_structsProof$convert_v ^cmp_value))``;

val shift_value = ``ValWord (6w:8 word)``;
val shift_expression =
  ``(panLang$Shift Lsl (panLang$Const (3w:8 word))
       (panLang$Const (1w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_shift_lsl"
  ``(pan_structs$old_exp_shape ^ctxt ^shift_expression,
     panSem$shape_of ^shift_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^shift_value,
     panSem$eval ^local_state ^shift_expression = SOME ^shift_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^shift_expression) =
       SOME (pan_structsProof$convert_v ^shift_value))``;

val shift_asr_value = ``ValWord (192w:8 word)``;
val shift_asr_expression =
  ``(panLang$Shift Asr (panLang$Const (128w:8 word))
       (panLang$Const (1w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_shift_asr"
  ``(pan_structs$old_exp_shape ^ctxt ^shift_asr_expression,
     panSem$shape_of ^shift_asr_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^shift_asr_value,
     panSem$eval ^local_state ^shift_asr_expression = SOME ^shift_asr_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^shift_asr_expression) =
       SOME (pan_structsProof$convert_v ^shift_asr_value))``;

val shift_ror_value = ``ValWord (192w:8 word)``;
val shift_ror_expression =
  ``(panLang$Shift Ror (panLang$Const (129w:8 word))
       (panLang$Const (1w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_shift_ror"
  ``(pan_structs$old_exp_shape ^ctxt ^shift_ror_expression,
     panSem$shape_of ^shift_ror_value,
     pan_structsProof$v_flds_ok (^local_state).structs ^shift_ror_value,
     panSem$eval ^local_state ^shift_ror_expression = SOME ^shift_ror_value,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^shift_ror_expression) =
       SOME (pan_structsProof$convert_v ^shift_ror_value))``;

val shift_width_expression =
  ``(panLang$Shift Lsl (panLang$Const (3w:8 word))
       (panLang$Const (8w:8 word)) : 8 panLang$exp)``;
val _ = print_eval "compile_exp_correct_shift_width_cutoff"
  ``(panSem$eval ^local_state ^shift_width_expression,
     panSem$eval (pan_structsProof$convert_s ^ctxt ^local_state)
       (pan_structs$compile_exp ^ctxt ^shift_width_expression))``;

val _ = print_eval "size_of_compile_shape_comb"
  ``(is_wf_shape [] (Comb [One; One]),
     struct_infos_ok [],
     size_of_sh_with_ctxt []
       (pan_structs$compile_shape [] (Comb [One; One])) =
       size_of_sh_with_ctxt [] (Comb [One; One]))``;
