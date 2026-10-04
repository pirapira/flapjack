(* Literal source-theorem replay of pan_to_targetProof helper theorems (79-87, 249-288,
   1193-1254). The original proof theory is unbuilt; every statement and HOL's own proof are
   replayed in source order over the loaded original theories, with the script's
   word_to_stack_compile overload. This is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "word_to_stackProofTheory"; load "stack_to_labProofTheory";
load "stack_allocProofTheory"; load "stack_removeProofTheory"; load "stackPropsTheory";
load "targetSemTheory"; load "miscTheory"; load "crep_to_loopTheory"; load "bvl_to_bviTheory";
load "data_to_word_gcProofTheory"; load "set_sepTheory"; load "addressTheory";
open bossLib HolKernel Parse preamble;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun guard name lit = if String.isSubstring lit source_text then ()
  else raise Fail (name ^ " literal source changed");
val _ = guard "overloads" "Overload word_to_stack_compile[local] = ``word_to_stack$compile``";
val _ = new_theory "flapjack_pan_to_target_init_helpers_source_replay";
val _ = overload_on ("word_to_stack_compile", ``word_to_stack$compile``);
open miscTheory alignmentTheory crep_to_loopTheory bvl_to_bviTheory stack_removeProofTheory;
val _ = guard "word_to_stack_compile_FST" "Theorem word_to_stack_compile_FST:\n  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) \226\135\146\n  MAP FST p =\n  raise_stub_location::store_consts_stub_location::MAP FST wprog\nProof\n  strip_tac>>gs[word_to_stackTheory.compile_def]>>\n  pairarg_tac>>gs[]>>rveq>>gs[]>>\n  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack\nQED";
val word_to_stack_compile_FST = store_thm("word_to_stack_compile_FST",
``  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) ⇒
  MAP FST p =
  raise_stub_location::store_consts_stub_location::MAP FST wprog``,
  strip_tac>>gs[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack);
val _ = guard "good_dimindex_0w_8w" "Theorem good_dimindex_0w_8w:\n  good_dimindex (:\206\177) \226\135\146 (0w:\206\177 word) \226\137\164 8w \226\136\167 -8w \226\137\164 (0w:\206\177 word)\nProof\n  strip_tac>>\n  fs[WORD_LE,miscTheory.good_dimindex_def,word_2comp_n2w,\n     dimword_def,word_msb_n2w]\nQED";
val good_dimindex_0w_8w = store_thm("good_dimindex_0w_8w",
``  good_dimindex (:α) ⇒ (0w:α word) ≤ 8w ∧ -8w ≤ (0w:α word)``,
  strip_tac>>
  fs[WORD_LE,miscTheory.good_dimindex_def,word_2comp_n2w,
     dimword_def,word_msb_n2w]);
val _ = guard "FLOOKUP_MAP_KEYS_LINV" "Theorem FLOOKUP_MAP_KEYS_LINV:\n  f PERMUTES \240\157\149\140(:\206\177) \226\135\146\n  FLOOKUP (MAP_KEYS (LINV f \240\157\149\140(:\206\177)) m) (i:\206\177) = FLOOKUP m (f i)\nProof\n  strip_tac>>\n  drule BIJ_LINV_INV>>strip_tac>>\n  drule BIJ_LINV_BIJ>>strip_tac>>\n  gs[BIJ_DEF]>>\n  mp_tac (GEN_ALL $ INST_TYPE [beta|->alpha,gamma|->beta] FLOOKUP_MAP_KEYS_MAPPED)>>\n  disch_then $ qspecl_then [\226\128\152m\226\128\153, \226\128\152f i\226\128\153, \226\128\152LINV f \240\157\149\140(:\206\177)\226\128\153] mp_tac>>\n  gs[]>>\n  last_x_assum assume_tac>>\n  drule LINV_DEF>>\n  disch_then $ qspec_then \226\128\152i\226\128\153 mp_tac>>\n  impl_tac >- gs[]>>\n  strip_tac>>pop_assum (fn h => rewrite_tac[h])\nQED";
val FLOOKUP_MAP_KEYS_LINV = store_thm("FLOOKUP_MAP_KEYS_LINV",
``  f PERMUTES 𝕌(:α) ⇒
  FLOOKUP (MAP_KEYS (LINV f 𝕌(:α)) m) (i:α) = FLOOKUP m (f i)``,
  strip_tac>>
  drule BIJ_LINV_INV>>strip_tac>>
  drule BIJ_LINV_BIJ>>strip_tac>>
  gs[BIJ_DEF]>>
  mp_tac (GEN_ALL $ INST_TYPE [beta|->alpha,gamma|->beta] FLOOKUP_MAP_KEYS_MAPPED)>>
  disch_then $ qspecl_then [‘m’, ‘f i’, ‘LINV f 𝕌(:α)’] mp_tac>>
  gs[]>>
  last_x_assum assume_tac>>
  drule LINV_DEF>>
  disch_then $ qspec_then ‘i’ mp_tac>>
  impl_tac >- gs[]>>
  strip_tac>>pop_assum (fn h => rewrite_tac[h]));
val _ = guard "full_make_init_be" "Theorem full_make_init_be:\n  (FST(full_make_init a b c d e f g h i j k)).be \226\135\148 h.be\nProof\n  fs[stack_to_labProofTheory.full_make_init_def]>>\n  fs[stack_allocProofTheory.make_init_def]>>\n  simp[stack_removeProofTheory.make_init_any_def,\n       stack_removeProofTheory.make_init_opt_def]>>\n  every_case_tac>>fs[]>>\n  imp_res_tac stackPropsTheory.evaluate_consts>>\n  EVAL_TAC>>fs[]>>\n  EVAL_TAC>>fs[]\nQED";
val full_make_init_be = store_thm("full_make_init_be",
``  (FST(full_make_init a b c d e f g h i j k)).be ⇔ h.be``,
  fs[stack_to_labProofTheory.full_make_init_def]>>
  fs[stack_allocProofTheory.make_init_def]>>
  simp[stack_removeProofTheory.make_init_any_def,
       stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac stackPropsTheory.evaluate_consts>>
  EVAL_TAC>>fs[]>>
  EVAL_TAC>>fs[]);
val _ = guard "n2w_sub_alt" "Theorem n2w_sub_alt[local]:\n  \226\136\128a b. b \226\137\164 a \226\135\146 n2w (a - b) = n2w a + -1w * n2w b\nProof\n  rpt strip_tac >>\n  irule EQ_TRANS >>\n  drule_then (irule_at (Pos hd)) n2w_sub >>\n  simp[] >>\n  metis_tac[WORD_NEG_MUL]\nQED";
val n2w_sub_alt = store_thm("n2w_sub_alt",
``  ∀a b. b ≤ a ⇒ n2w (a - b) = n2w a + -1w * n2w b``,
  rpt strip_tac >>
  irule EQ_TRANS >>
  drule_then (irule_at (Pos hd)) n2w_sub >>
  simp[] >>
  metis_tac[WORD_NEG_MUL]);
val _ = guard "aligned_n2w_IMP" "Theorem aligned_n2w_IMP[local]:\n  aligned k ((n2w n):'a word) \226\136\167 n < dimword(:'a) \226\135\146 divides (2**k) n\nProof\n  rw[aligned_w2n,dimword_def] >>\n  gvs[dividesTheory.DIVIDES_MOD_0]\nQED";
val aligned_n2w_IMP = store_thm("aligned_n2w_IMP",
``  aligned k ((n2w n):'a word) ∧ n < dimword(:'a) ⇒ divides (2**k) n``,
  rw[aligned_w2n,dimword_def] >>
  gvs[dividesTheory.DIVIDES_MOD_0]);
val _ = guard "word_list_exists_addresses" "Theorem word_list_exists_addresses:\n  (word_list_exists a n) (fun2set (d, addresses (a:'a word) m)) \226\136\167 good_dimindex(:'a) \226\136\167 m < dimword(:'a) DIV w2n(bytes_in_word:'a word) \226\135\146 n = m\nProof\n  rw[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM] >>\n  imp_res_tac data_to_word_gcProofTheory.word_list_IMP_limit >>\n  gvs[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM,set_sepTheory.fun2set_def,\n     set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.cond_def] >>\n  rpt $ pop_assum mp_tac >>\n  qid_spec_tac \226\128\152xs\226\128\153 >>\n  qid_spec_tac \226\128\152a\226\128\153 >>\n  qid_spec_tac \226\128\152m\226\128\153 >>\n  Induct_on \226\128\152xs\226\128\153 >>\n  Cases_on \226\128\152m\226\128\153 >>\n  rw[miscTheory.word_list_def,stack_removeProofTheory.addresses_def]\n  >- (gvs[set_sepTheory.emp_def,FUN_EQ_THM, SF DNF_ss])\n  >- gvs[set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.one_def, SF DNF_ss] >>\n  gvs[set_sepTheory.STAR_def,set_sepTheory.one_def,set_sepTheory.SPLIT_def] >>\n  \226\128\152v = {(a', d a') | a' \226\136\136 addresses (a + bytes_in_word) n}\226\128\153\n    by(gvs[SET_EQ_SUBSET,SUBSET_DEF] >>\n       rw[] >>\n       fs[SF DNF_ss] >>\n       res_tac >>\n       gvs[] >>\n       gvs[stack_removeProofTheory.addresses_thm] >>\n       FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>\n       gvs[good_dimindex_def,bytes_in_word_def,dimword_def,word_add_n2w,word_mul_n2w]) >>\n  rveq >>\n  first_x_assum drule >>\n  simp[]\nQED";
val word_list_exists_addresses = store_thm("word_list_exists_addresses",
``  (word_list_exists a n) (fun2set (d, addresses (a:'a word) m)) ∧ good_dimindex(:'a) ∧ m < dimword(:'a) DIV w2n(bytes_in_word:'a word) ⇒ n = m``,
  rw[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM] >>
  imp_res_tac data_to_word_gcProofTheory.word_list_IMP_limit >>
  gvs[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM,set_sepTheory.fun2set_def,
     set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.cond_def] >>
  rpt $ pop_assum mp_tac >>
  qid_spec_tac ‘xs’ >>
  qid_spec_tac ‘a’ >>
  qid_spec_tac ‘m’ >>
  Induct_on ‘xs’ >>
  Cases_on ‘m’ >>
  rw[miscTheory.word_list_def,stack_removeProofTheory.addresses_def]
  >- (gvs[set_sepTheory.emp_def,FUN_EQ_THM, SF DNF_ss])
  >- gvs[set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.one_def, SF DNF_ss] >>
  gvs[set_sepTheory.STAR_def,set_sepTheory.one_def,set_sepTheory.SPLIT_def] >>
  ‘v = {(a', d a') | a' ∈ addresses (a + bytes_in_word) n}’
    by(gvs[SET_EQ_SUBSET,SUBSET_DEF] >>
       rw[] >>
       fs[SF DNF_ss] >>
       res_tac >>
       gvs[] >>
       gvs[stack_removeProofTheory.addresses_thm] >>
       FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
       gvs[good_dimindex_def,bytes_in_word_def,dimword_def,word_add_n2w,word_mul_n2w]) >>
  rveq >>
  first_x_assum drule >>
  simp[]);
val _ = guard "good_dimindex_div_mul" "Theorem good_dimindex_div_mul:\n  good_dimindex(:\206\177) \226\135\146 a * dimindex(:\206\177) DIV 8 = a * (dimindex (:\206\177) DIV 8)\nProof\n  rw[good_dimindex_def] >>\n  rw[] >>\n  intLib.COOPER_TAC\nQED";
val good_dimindex_div_mul = store_thm("good_dimindex_div_mul",
``  good_dimindex(:α) ⇒ a * dimindex(:α) DIV 8 = a * (dimindex (:α) DIV 8)``,
  rw[good_dimindex_def] >>
  rw[] >>
  intLib.COOPER_TAC);
val _ = guard "InitGlobals_location_eq_first_name" "Theorem InitGlobals_location_eq_first_name:\n  InitGlobals_location = first_name\nProof\n  EVAL_TAC\nQED";
val InitGlobals_location_eq_first_name = store_thm("InitGlobals_location_eq_first_name",
``  InitGlobals_location = first_name``,
  EVAL_TAC);
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = pr_stmt "word_to_stack_compile_FST_replay_statement" word_to_stack_compile_FST;
val _ = pr_hyps "word_to_stack_compile_FST_replay_hypotheses" word_to_stack_compile_FST;
val _ = pr_typed "word_to_stack_compile_FST_replay_typed" word_to_stack_compile_FST;
val _ = pr_stmt "good_dimindex_0w_8w_replay_statement" good_dimindex_0w_8w;
val _ = pr_hyps "good_dimindex_0w_8w_replay_hypotheses" good_dimindex_0w_8w;
val _ = pr_typed "good_dimindex_0w_8w_replay_typed" good_dimindex_0w_8w;
val _ = pr_stmt "FLOOKUP_MAP_KEYS_LINV_replay_statement" FLOOKUP_MAP_KEYS_LINV;
val _ = pr_hyps "FLOOKUP_MAP_KEYS_LINV_replay_hypotheses" FLOOKUP_MAP_KEYS_LINV;
val _ = pr_typed "FLOOKUP_MAP_KEYS_LINV_replay_typed" FLOOKUP_MAP_KEYS_LINV;
val _ = pr_stmt "full_make_init_be_replay_statement" full_make_init_be;
val _ = pr_hyps "full_make_init_be_replay_hypotheses" full_make_init_be;
val _ = pr_typed "full_make_init_be_replay_typed" full_make_init_be;
val _ = pr_stmt "n2w_sub_alt_replay_statement" n2w_sub_alt;
val _ = pr_hyps "n2w_sub_alt_replay_hypotheses" n2w_sub_alt;
val _ = pr_typed "n2w_sub_alt_replay_typed" n2w_sub_alt;
val _ = pr_stmt "aligned_n2w_IMP_replay_statement" aligned_n2w_IMP;
val _ = pr_hyps "aligned_n2w_IMP_replay_hypotheses" aligned_n2w_IMP;
val _ = pr_typed "aligned_n2w_IMP_replay_typed" aligned_n2w_IMP;
val _ = pr_stmt "word_list_exists_addresses_replay_statement" word_list_exists_addresses;
val _ = pr_hyps "word_list_exists_addresses_replay_hypotheses" word_list_exists_addresses;
val _ = pr_typed "word_list_exists_addresses_replay_typed" word_list_exists_addresses;
val _ = pr_stmt "good_dimindex_div_mul_replay_statement" good_dimindex_div_mul;
val _ = pr_hyps "good_dimindex_div_mul_replay_hypotheses" good_dimindex_div_mul;
val _ = pr_typed "good_dimindex_div_mul_replay_typed" good_dimindex_div_mul;
val _ = pr_stmt "InitGlobals_location_eq_first_name_replay_statement" InitGlobals_location_eq_first_name;
val _ = pr_hyps "InitGlobals_location_eq_first_name_replay_hypotheses" InitGlobals_location_eq_first_name;
val _ = pr_typed "InitGlobals_location_eq_first_name_replay_typed" InitGlobals_location_eq_first_name;
