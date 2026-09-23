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
