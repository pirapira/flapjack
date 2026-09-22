(* Direct HOL-EVAL and proof probes for pan_to_crepProof$code_rel.
   Reference: cakeml/pancake/proofs/pan_to_crepProofScript.sml:32-43. *)
load "bossLib";
load "preamble";
load "pan_to_crepTheory";
load "pan_to_crepProofTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
open pan_to_crepProofTheory;
open panPropsTheory;

val _ = print ("code_rel_type=" ^ type_to_string (type_of ``code_rel``) ^ "\n");

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val context =
  ``ctxt_fc
      (FEMPTY |+ («f», ([(«x», panLang$One)], panLang$One)))
      FEMPTY [«x»] [panLang$One] [0]``;
val source_code =
  ``FEMPTY |+ («f», ([(«x», panLang$One)],
      panLang$Return (panLang$Var panLang$Local «x»), panLang$One))``;
val matching_target =
  ``FEMPTY |+ («f», ([(0:num)], crepLang$Return [crepLang$Var 0]))``;
val bad_body_target = ``FEMPTY |+ («f», ([(0:num)], crepLang$Skip))``;
val bad_function_context =
  ``ctxt_fc FEMPTY FEMPTY [«x»] [panLang$One] [0]``;
val unlocalised_source =
  ``FEMPTY |+ («f», ([(«x», panLang$One)],
      panLang$Assign panLang$Global «x» (panLang$Var panLang$Local «x»),
      panLang$One))``;

val _ = print_eval "compiled_return" ``pan_to_crep$compile ^context
  (panLang$Return (panLang$Var panLang$Local «x»))``;
val _ = print_eval "localised_return"
  ``panProps$localised_prog (panLang$Return (panLang$Var panLang$Local «x»))``;
val _ = print_eval "localised_global_assignment"
  ``panProps$localised_prog
      (panLang$Assign panLang$Global «x» (panLang$Var panLang$Local «x»))``;
val _ = print_eval "function_signature_lookup"
  ``FLOOKUP (^context).funcs «f»``;
val _ = print_eval "target_function_lookup"
  ``FLOOKUP ^matching_target «f»``;

fun prove_and_print label proposition =
  let
    val _ = prove (proposition,
      simp [code_rel_def, ctxt_fc_def, pan_to_crepTheory.compile_def,
        pan_to_crepTheory.compile_exp_def, panPropsTheory.localised_prog_def,
        panPropsTheory.localised_exp_simps, panPropsTheory.localised_exp_real_def,
        FUPDATE_LIST_THM, FLOOKUP_FUPDATE_LIST, FLOOKUP_UPDATE,
        panLangTheory.size_of_shape_def,
        panLangTheory.with_shape_def] THEN EVAL_TAC);
  in
    print (label ^ "=PASS\n")
  end;

val _ = prove_and_print "code_rel_matching"
  ``code_rel ^context ^source_code ^matching_target``;
val _ = prove_and_print "code_rel_rejects_wrong_body"
  ``~code_rel ^context ^source_code ^bad_body_target``;
val _ = prove_and_print "code_rel_rejects_missing_function_signature"
  ``~code_rel ^bad_function_context ^source_code ^matching_target``;
val _ = prove_and_print "code_rel_rejects_unlocalised_source"
  ``~code_rel ^context ^unlocalised_source ^bad_body_target``;
