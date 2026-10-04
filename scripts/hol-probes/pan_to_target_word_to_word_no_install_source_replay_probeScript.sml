(* Literal source-theorem replay of pan_to_targetProof909-938
   (word_to_word_compile_no_install_no_alloc). The original proof theory is
   unbuilt; the statement and HOL's own proof are replayed over the loaded
   original theories. This is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "word_to_wordProofTheory";
load "wordConvsProofTheory"; load "wordPropsTheory";
open bossLib HolKernel Parse preamble word_to_wordProofTheory;
(* Fail rather than capture a stale literal if the pinned source changes. *)
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
val _ = if String.isSubstring "Theorem word_to_word_compile_no_install_no_alloc:\n  word_to_word$compile wconf aconf progs0 = (col, progs) \226\136\167\n  ALL_DISTINCT (MAP FST progs0) \226\136\167\n  no_mt_code (fromAList progs0) \226\136\167\n  no_install_code (fromAList progs0) \226\135\146\n  no_install_code (fromAList progs) \226\136\167\n  (no_alloc_code (fromAList progs0) \226\135\146 no_alloc_code (fromAList progs))\nProof" source_text
  then () else raise Fail "word_to_word_compile_no_install_no_alloc literal source changed";

val _ = new_theory "flapjack_word_to_word_no_install_source_replay";
val word_to_word_compile_no_install_no_alloc_replay = store_thm(
  "word_to_word_compile_no_install_no_alloc_replay",
  ``word_to_word$compile wconf aconf progs0 = (col, progs) /\
    ALL_DISTINCT (MAP FST progs0) /\
    no_mt_code (fromAList progs0) /\
    no_install_code (fromAList progs0) ==>
    no_install_code (fromAList progs) /\
    (no_alloc_code (fromAList progs0) ==> no_alloc_code (fromAList progs))``,
  strip_tac>>gs[word_to_wordTheory.compile_def]>>
  rpt (pairarg_tac>>gs[])>>
  gvs[]>>
  DEP_REWRITE_TAC[word_to_wordProofTheory.no_mt_code_full_compile_single]>>
  simp []>>
  conj_asm1_tac >- (
    fs[word_to_wordTheory.next_n_oracle_def]>>every_case_tac>>gvs[]
  )>>
  fs[wordPropsTheory.no_install_code_def, wordPropsTheory.no_alloc_code_def,
        lookup_fromAList]>>
  fs[wordConvsTheory.no_install_subprogs_def,
        wordConvsTheory.no_alloc_subprogs_def]>>
  rw[]>>drule ALOOKUP_MEM>>strip_tac>>
  gs[PAIR_FST_SND_EQ, MEM_MAP]>>
  irule wordConvsProofTheory.compile_single_not_created_subprogs>>
  first_x_assum irule>>
  gs[MEM_ZIP]>>
  drule_at Any ALOOKUP_ALL_DISTINCT_EL>>
  rw[]>>
  drule_then (irule_at Any) EQ_TRANS>>
  simp[PAIR_FST_SND_EQ]);
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = pr_stmt "word_to_word_compile_no_install_no_alloc_replay_statement" word_to_word_compile_no_install_no_alloc_replay;
val _ = pr_hyps "word_to_word_compile_no_install_no_alloc_replay_hypotheses" word_to_word_compile_no_install_no_alloc_replay;
val _ = pr_typed "word_to_word_compile_no_install_no_alloc_replay_typed" word_to_word_compile_no_install_no_alloc_replay;
