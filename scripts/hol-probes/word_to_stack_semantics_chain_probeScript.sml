load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory wordSemTheory stackSemTheory wordLangTheory stackLangTheory;
val _ = new_theory "flapjack_word_to_stack_semantics_chain_replay";
val _ = Globals.linewidth := 1000000;
(* match original comp_correct shape: n, sprog, bs', n' are free *)
val comp_correct = let
  val th = REWRITE_RULE [FORALL_PROD] comp_correct
  val vs = th |> concl |> strip_forall |> #1
  val drops = List.filter (fn v => let val n = #1 (dest_var v) in
    n = "n" orelse n = "sprog" orelse n = "bs'" orelse n = "n'" end) vs
  val keeps = List.filter (fn v => not (List.exists (fn d => Term.compare(v,d) = EQUAL) drops)) vs
  in GENL keeps (SPECL vs th) end;

Theorem evaluate_Seq_Skip:
  stackSem$evaluate (Seq Skip p,s) = evaluate (p,s)
Proof
  fs [stackSemTheory.evaluate_def,LET_THM]
QED

val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,call_dest_def,LET_THM]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       evaluate_Seq_Skip,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0] NONE)``,
       EVAL  ``flat_exp_conventions (Call NONE (SOME start) [0] NONE)``,
       wordLangTheory.max_var_def,LET_DEF,MAX_DEF] |> GEN_ALL

Theorem comp_Call:
  ∀start (s:('a,num # 'c,'ffi) wordSem$state) k res s1 t lens.
      evaluate (Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
      res ≠ SOME Error /\ state_rel ac k 0 0 s t lens 0 ⇒
      ∃ck t1:(α,'c,'ffi)stackSem$state res1.
        evaluate (Call NONE (INL start) NONE,t with clock := t.clock + ck) =
        (res1,t1) /\ 1w <> (0w:'a word) /\ 2w <> (0w:'a word) /\
        if OPTION_MAP compile_result res = res1 then
          s1.ffi = t1.ffi /\ s1.clock = t1.clock
        else
          res1 = SOME (Halt (Word 2w)) /\
          t1.ffi.io_events ≼ s1.ffi.io_events /\
          the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
Proof
  rw [] \\ old_drule comp_Call_lemma \\ fs [get_labels_def]
  \\ disch_then drule
  \\ disch_then(qspecl_then[`LENGTH t.bitmaps`,`Nil`] mp_tac)
  \\ fs [] \\ strip_tac
  \\ `0 < 2 * k` by (fs [state_rel_def] \\ decide_tac) \\ fs []
  \\ fs[evaluate_Seq_Skip]
  \\ asm_exists_tac \\ fs []
  \\ conj_tac THEN1 (fs [state_rel_def,good_dimindex_def,dimword_def])
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs [state_rel_def,push_locals_def,LET_DEF]
QED

val _ = if null (hyp (evaluate_Seq_Skip)) then () else raise Fail "hypotheses: evaluate_Seq_Skip";
val _ = (print "evaluate_Seq_Skip_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (evaluate_Seq_Skip)); print "\n");
val _ = print("evaluate_Seq_Skip_hypotheses=" ^ Int.toString(length(hyp (evaluate_Seq_Skip))) ^ "\n");
val _ = if null (hyp (comp_Call)) then () else raise Fail "hypotheses: comp_Call";
val _ = (print "comp_Call_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (comp_Call)); print "\n");
val _ = print("comp_Call_hypotheses=" ^ Int.toString(length(hyp (comp_Call))) ^ "\n");
val _ = if null (hyp (word_to_stackProofTheory.state_rel_IMP_semantics)) then () else raise Fail "hypotheses: state_rel_IMP_semantics";
val _ = (print "state_rel_IMP_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_to_stackProofTheory.state_rel_IMP_semantics)); print "\n");
val _ = print("state_rel_IMP_semantics_hypotheses=" ^ Int.toString(length(hyp (word_to_stackProofTheory.state_rel_IMP_semantics))) ^ "\n");
val _ = if null (hyp (word_to_stackProofTheory.state_rel_IMP_semantics')) then () else raise Fail "hypotheses: state_rel_IMP_semantics_prime";
val _ = (print "state_rel_IMP_semantics_prime_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_to_stackProofTheory.state_rel_IMP_semantics')); print "\n");
val _ = print("state_rel_IMP_semantics_prime_hypotheses=" ^ Int.toString(length(hyp (word_to_stackProofTheory.state_rel_IMP_semantics'))) ^ "\n");
val _ = if null (hyp (word_to_stackProofTheory.compile_semantics)) then () else raise Fail "hypotheses: compile_semantics";
val _ = (print "compile_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_to_stackProofTheory.compile_semantics)); print "\n");
val _ = print("compile_semantics_hypotheses=" ^ Int.toString(length(hyp (word_to_stackProofTheory.compile_semantics))) ^ "\n");
