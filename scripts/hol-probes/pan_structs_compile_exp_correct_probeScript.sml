(* Direct HOL-EVAL instance of pan_structsProof$compile_exp_correct for its
   Local and Global Var induction cases. *)
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
