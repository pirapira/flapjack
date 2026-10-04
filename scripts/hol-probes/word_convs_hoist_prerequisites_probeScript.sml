load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory word_simpTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val const_fp_loop_Seq = GEN_ALL(
  const_fp_loop_def |> BODY_CONJUNCTS
  |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl)
  |> LIST_CONJ
);
val _ = if null(hyp const_fp_loop_Seq) andalso null(free_vars(concl const_fp_loop_Seq)) then () else raise Fail "open const_fp_loop_Seq";
val _ = (print "hoistPrerequisite1_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl const_fp_loop_Seq));
val _ = print("hoistPrerequisite1_proved=" ^ term_to_string(rhs(concl(EQT_INTRO const_fp_loop_Seq))) ^ "\n");
val _ = print("hoistPrerequisite1_hypotheses=" ^ Int.toString(length(hyp const_fp_loop_Seq)) ^ "\n");
val const_fp_loop_dummy_cases = GEN_ALL(prove(``
const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs = (p2, cs2) ==>
  (dest_Raise_num p2 = 1 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br1 cs)) \/
  (dest_Raise_num p2 = 2 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br2 cs)) \/
  (dest_Raise_num p2 = 0)
``,
  rw [const_fp_loop_def, dest_Raise_num_def]
  \\ gvs [CaseEq "option", CaseEq "bool"]
));
val _ = if null(hyp const_fp_loop_dummy_cases) andalso null(free_vars(concl const_fp_loop_dummy_cases)) then () else raise Fail "open const_fp_loop_dummy_cases";
val _ = (print "hoistPrerequisite2_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl const_fp_loop_dummy_cases));
val _ = print("hoistPrerequisite2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO const_fp_loop_dummy_cases))) ^ "\n");
val _ = print("hoistPrerequisite2_hypotheses=" ^ Int.toString(length(hyp const_fp_loop_dummy_cases)) ^ "\n");
val dest_If_thm = GEN_ALL(prove(``
dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
``,
  Cases_on `x2` \\ fs [dest_If_def]
));
val _ = if null(hyp dest_If_thm) andalso null(free_vars(concl dest_If_thm)) then () else raise Fail "open dest_If_thm";
val _ = (print "hoistPrerequisite3_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl dest_If_thm));
val _ = print("hoistPrerequisite3_proved=" ^ term_to_string(rhs(concl(EQT_INTRO dest_If_thm))) ^ "\n");
val _ = print("hoistPrerequisite3_hypotheses=" ^ Int.toString(length(hyp dest_If_thm)) ^ "\n");
