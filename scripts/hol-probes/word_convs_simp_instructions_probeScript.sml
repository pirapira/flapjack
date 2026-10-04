load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordLangTheory wordConvsTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
(* Literal original local statements/proofs, replayed in their source order.
   dest_If_thm is replayed solely as a prerequisite of the original hoisting proof. *)
val dest_If_thm = Q.prove (`
   dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
`,
  Cases_on `x2` \\ fs [dest_If_def]
);
val dest_Seq_no_inst = Q.prove (`
  ∀prog.
  every_inst P prog ⇒
  every_inst P (FST (dest_Seq prog)) ∧
  every_inst P (SND (dest_Seq prog))
`,
  ho_match_mp_tac dest_Seq_ind>>rw[dest_Seq_def]>>fs[every_inst_def]
);
val dest_Seq_no_inst_closed = GEN_ALL dest_Seq_no_inst;
val _ = if null(hyp dest_Seq_no_inst_closed) andalso null(free_vars(concl dest_Seq_no_inst_closed)) then () else raise Fail "open dest_Seq_no_inst";
val _ = (print "dest_Seq_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl dest_Seq_no_inst_closed));
val _ = print("dest_Seq_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO dest_Seq_no_inst_closed))) ^ "\n");
val _ = print("dest_Seq_no_inst_hypotheses=" ^ Int.toString(length(hyp dest_Seq_no_inst_closed)) ^ "\n");
val Seq_assoc_no_inst = Q.prove (`
  ∀p1 p2.
  every_inst P p1 ∧ every_inst P p2 ⇒
  every_inst P (Seq_assoc p1 p2)
`,
  ho_match_mp_tac Seq_assoc_ind>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[every_inst_def]>>
  every_case_tac>>fs[]
);
val Seq_assoc_no_inst_closed = GEN_ALL Seq_assoc_no_inst;
val _ = if null(hyp Seq_assoc_no_inst_closed) andalso null(free_vars(concl Seq_assoc_no_inst_closed)) then () else raise Fail "open Seq_assoc_no_inst";
val _ = (print "Seq_assoc_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl Seq_assoc_no_inst_closed));
val _ = print("Seq_assoc_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO Seq_assoc_no_inst_closed))) ^ "\n");
val _ = print("Seq_assoc_no_inst_hypotheses=" ^ Int.toString(length(hyp Seq_assoc_no_inst_closed)) ^ "\n");
val every_inst_SmartSeq = Q.prove (`
  every_inst P (SmartSeq p q) =
  (every_inst P p ∧ every_inst P q)
`,
  rw[SmartSeq_def,every_inst_def]
);
val every_inst_SmartSeq_closed = GEN_ALL every_inst_SmartSeq;
val _ = if null(hyp every_inst_SmartSeq_closed) andalso null(free_vars(concl every_inst_SmartSeq_closed)) then () else raise Fail "open every_inst_SmartSeq";
val _ = (print "every_inst_SmartSeq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl every_inst_SmartSeq_closed));
val _ = print("every_inst_SmartSeq_proved=" ^ term_to_string(rhs(concl(EQT_INTRO every_inst_SmartSeq_closed))) ^ "\n");
val _ = print("every_inst_SmartSeq_hypotheses=" ^ Int.toString(length(hyp every_inst_SmartSeq_closed)) ^ "\n");
val every_inst_drop_consts = Q.prove (`
  every_inst P (SmartSeq (drop_consts cs ls) p) =
  every_inst P p
`,
  rw[every_inst_SmartSeq]>>
  `every_inst P (drop_consts cs ls)` by (
    Induct_on`ls`>>rw[drop_consts_def]>>every_case_tac>>
    rw[every_inst_def,every_inst_SmartSeq] )>>
  rw[]
);
val _ = augment_srw_ss [rewrites [every_inst_drop_consts]];
val every_inst_drop_consts_closed = GEN_ALL every_inst_drop_consts;
val _ = if null(hyp every_inst_drop_consts_closed) andalso null(free_vars(concl every_inst_drop_consts_closed)) then () else raise Fail "open every_inst_drop_consts";
val _ = (print "every_inst_drop_consts_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl every_inst_drop_consts_closed));
val _ = print("every_inst_drop_consts_proved=" ^ term_to_string(rhs(concl(EQT_INTRO every_inst_drop_consts_closed))) ^ "\n");
val _ = print("every_inst_drop_consts_hypotheses=" ^ Int.toString(length(hyp every_inst_drop_consts_closed)) ^ "\n");
val every_inst_const_fp = Q.prove (`
   ∀prog.
    every_inst P prog ⇒
    every_inst P (const_fp prog)
`,
  strip_tac
  \\ fs [const_fp_def] \\ Cases_on `const_fp_loop prog LN`
  \\ rename1 `const_fp_loop p cs = (p1,cs1)` \\ fs []
  \\ pop_assum mp_tac
  \\ qspec_tac (`cs1`,`cs1`) \\ qspec_tac (`p1`,`p1`)
  \\ qspec_tac (`cs`,`cs`) \\ qspec_tac (`p`,`p`)
  \\ ho_match_mp_tac const_fp_loop_ind \\ rw []
  >~ [`Loop names p exit_names`]
  >- (fs [const_fp_loop_def] \\ rw [] \\ fs [every_inst_def]
      \\ Cases_on `const_fp_loop p LN` \\ fs []
      \\ first_x_assum drule \\ fs [])
  \\ fs [const_fp_loop_def] \\ rw [] \\ fs [every_inst_def]
  \\ every_case_tac \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
);
val every_inst_const_fp_closed = GEN_ALL every_inst_const_fp;
val _ = if null(hyp every_inst_const_fp_closed) andalso null(free_vars(concl every_inst_const_fp_closed)) then () else raise Fail "open every_inst_const_fp";
val _ = (print "every_inst_const_fp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl every_inst_const_fp_closed));
val _ = print("every_inst_const_fp_proved=" ^ term_to_string(rhs(concl(EQT_INTRO every_inst_const_fp_closed))) ^ "\n");
val _ = print("every_inst_const_fp_hypotheses=" ^ Int.toString(length(hyp every_inst_const_fp_closed)) ^ "\n");
val try_if_hoist2_no_inst = Q.prove (`
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  every_inst P p1 ==>
  every_inst P interm ==>
  every_inst P p2 ==>
  every_inst P p3
`,
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs [dest_If_thm]
  \\ fs [every_inst_def, every_inst_const_fp]
);
val try_if_hoist2_no_inst_closed = GEN_ALL try_if_hoist2_no_inst;
val _ = if null(hyp try_if_hoist2_no_inst_closed) andalso null(free_vars(concl try_if_hoist2_no_inst_closed)) then () else raise Fail "open try_if_hoist2_no_inst";
val _ = (print "try_if_hoist2_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl try_if_hoist2_no_inst_closed));
val _ = print("try_if_hoist2_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO try_if_hoist2_no_inst_closed))) ^ "\n");
val _ = print("try_if_hoist2_no_inst_hypotheses=" ^ Int.toString(length(hyp try_if_hoist2_no_inst_closed)) ^ "\n");
val simp_duplicate_if_no_inst = Q.prove (`
  !p. every_inst P p ==> every_inst P (simp_duplicate_if p)
`,
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ fs [every_inst_def]
  \\ every_case_tac \\ fs []
  \\ fs [every_inst_def]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod"]
  \\ imp_res_tac try_if_hoist2_no_inst
  \\ gs [dest_If_thm]
  \\ fs [every_inst_def, Seq_assoc_no_inst, every_inst_const_fp]
);
val simp_duplicate_if_no_inst_closed = GEN_ALL simp_duplicate_if_no_inst;
val _ = if null(hyp simp_duplicate_if_no_inst_closed) andalso null(free_vars(concl simp_duplicate_if_no_inst_closed)) then () else raise Fail "open simp_duplicate_if_no_inst";
val _ = (print "simp_duplicate_if_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl simp_duplicate_if_no_inst_closed));
val _ = print("simp_duplicate_if_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO simp_duplicate_if_no_inst_closed))) ^ "\n");
val _ = print("simp_duplicate_if_no_inst_hypotheses=" ^ Int.toString(length(hyp simp_duplicate_if_no_inst_closed)) ^ "\n");
val simp_push_out_if_no_inst = Q.prove (`
  !p. every_inst P p ==> every_inst P (push_out_if p)
`,
  simp [push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw []
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ asm_simp_tac(srw_ss())[])
  \\ fs[every_inst_def]
  \\ res_tac \\ fs []
);
val simp_push_out_if_no_inst_closed = GEN_ALL simp_push_out_if_no_inst;
val _ = if null(hyp simp_push_out_if_no_inst_closed) andalso null(free_vars(concl simp_push_out_if_no_inst_closed)) then () else raise Fail "open simp_push_out_if_no_inst";
val _ = (print "simp_push_out_if_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl simp_push_out_if_no_inst_closed));
val _ = print("simp_push_out_if_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO simp_push_out_if_no_inst_closed))) ^ "\n");
val _ = print("simp_push_out_if_no_inst_hypotheses=" ^ Int.toString(length(hyp simp_push_out_if_no_inst_closed)) ^ "\n");
val compile_exp_no_inst = Q.prove (`
  ∀prog.
    every_inst P prog ⇒
    every_inst P (compile_exp prog)
`,
  rw[compile_exp_def]>>
  rpt (MAP_FIRST irule [Seq_assoc_no_inst,every_inst_def,
            every_inst_const_fp,simp_duplicate_if_no_inst,
            simp_push_out_if_no_inst]) >>
  simp[every_inst_def]
);
val compile_exp_no_inst_closed = GEN_ALL compile_exp_no_inst;
val _ = if null(hyp compile_exp_no_inst_closed) andalso null(free_vars(concl compile_exp_no_inst_closed)) then () else raise Fail "open compile_exp_no_inst";
val _ = (print "compile_exp_no_inst_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_exp_no_inst_closed));
val _ = print("compile_exp_no_inst_proved=" ^ term_to_string(rhs(concl(EQT_INTRO compile_exp_no_inst_closed))) ^ "\n");
val _ = print("compile_exp_no_inst_hypotheses=" ^ Int.toString(length(hyp compile_exp_no_inst_closed)) ^ "\n");
val _ = if aconv (concl compile_exp_no_inst_closed) (concl(GEN_ALL wordConvsProofTheory.compile_exp_no_inst)) then () else raise Fail "compile_exp_no_inst statement drift";
