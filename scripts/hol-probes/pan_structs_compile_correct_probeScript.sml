(* Direct HOL-EVAL fixture for the `convert_v` and `Skip` case used by
   pan_structsProofScript.sml's `compile_correct` induction. *)
load "bossLib";
load "preamble";
load "panSemTheory";
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

val _ = print_eval "convert_named_record"
  ``pan_structsProof$convert_v
      (panSem$NStruct (strlit "Pair")
        [(strlit "left", ValWord 3w);
         (strlit "right", ValWord 5w)])``;

val state = ``(s:('a,'ffi) panSem$state)``;
val _ = print_eval "compile_correct_skip_source"
  ``(FST (panSem$evaluate (panLang$Skip, ^state)),
     SND (panSem$evaluate (panLang$Skip, ^state)) = ^state)``;
val _ = print_eval "compile_correct_skip_converted"
  ``(FST (panSem$evaluate (panLang$Skip,
      pan_structsProof$convert_s (ARB:pan_structs$context) ^state)),
     SND (panSem$evaluate (panLang$Skip,
      pan_structsProof$convert_s (ARB:pan_structs$context) ^state)) =
        pan_structsProof$convert_s (ARB:pan_structs$context) ^state)``;

val finite_map_state = ``^state with <|
    locals := FUPDATE FEMPTY (strlit "local", ValWord 7w);
    globals := FUPDATE FEMPTY (strlit "global", ValWord 11w);
    eshapes := FUPDATE FEMPTY (strlit "E", panLang$One)
  |>``;
val _ = print_simp "convert_s_finite_maps"
  [pan_structsProofTheory.convert_s_def,
   pan_structsProofTheory.convert_v_def,
   pan_structsProofTheory.convert_eshapes_def,
   pan_structsTheory.compile_shape_def,
   FLOOKUP_FMAP_MAP2, FLOOKUP_UPDATE]
  ``(FLOOKUP (pan_structsProof$convert_s (ARB:pan_structs$context)
       ^finite_map_state).locals (strlit "local"),
     FLOOKUP (pan_structsProof$convert_s (ARB:pan_structs$context)
       ^finite_map_state).globals (strlit "global"),
     FLOOKUP (pan_structsProof$convert_s (ARB:pan_structs$context)
       ^finite_map_state).eshapes (strlit "E"))``;

val zero_state = ``(^state with clock := 0)``;
val positive_state = ``(^state with clock := 1)``;
val _ = print_eval "compile_correct_tick_zero_source"
  ``(FST (panSem$evaluate (panLang$Tick, ^zero_state)),
     SND (panSem$evaluate (panLang$Tick, ^zero_state)) =
       (^zero_state with locals := FEMPTY))``;
val _ = print_eval "compile_correct_tick_zero_converted"
  ``(FST (panSem$evaluate (panLang$Tick,
       pan_structsProof$convert_s (ARB:pan_structs$context) ^zero_state)),
     SND (panSem$evaluate (panLang$Tick,
       pan_structsProof$convert_s (ARB:pan_structs$context) ^zero_state)) =
       (pan_structsProof$convert_s (ARB:pan_structs$context) ^zero_state
         with locals := FEMPTY))``;
val _ = print_eval "compile_correct_tick_positive_source"
  ``(FST (panSem$evaluate (panLang$Tick, ^positive_state)),
     SND (panSem$evaluate (panLang$Tick, ^positive_state)) =
       (^positive_state with clock := 0))``;
val _ = print_eval "compile_correct_tick_positive_converted"
  ``(FST (panSem$evaluate (panLang$Tick,
       pan_structsProof$convert_s (ARB:pan_structs$context) ^positive_state)),
     SND (panSem$evaluate (panLang$Tick,
       pan_structsProof$convert_s (ARB:pan_structs$context) ^positive_state)) =
       (pan_structsProof$convert_s (ARB:pan_structs$context) ^positive_state
         with clock := 0))``;
