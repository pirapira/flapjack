load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 parmoveTheory bitTheory word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val TIMES2_DIV2_lemma = GEN_ALL (prove(``
  windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP ($* 2 o THE) (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves))))
    = MAP THE (FILTER IS_SOME (MAP FST (parmove moves)))``,

  strip_tac
  \\ simp[MAP_o_THE_FILTER_IS_SOME]
  \\ simp[GSYM MAP_MAP_o]
  \\ simp[MAP_OPTION_MAP_FILTER_IS_SOME]
  \\ ntac 2 AP_TERM_TAC
  \\ qispl_then[`moves`,`DIV2`]mp_tac(Q.GENL[`ls`,`f`]parmove_MAP_INJ)
  \\ impl_tac
  >- (
    simp[]
    \\ fs[EVERY_MEM]
    \\ metis_tac[EVEN_DIV2_INJ] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[MAP_MAP_o,o_DEF]
  \\ simp[MAP_EQ_f]
  \\ simp[FORALL_PROD]
  \\ Cases \\ simp[]
  \\ rw[]
  \\ simp[DIV2_def,bitTheory.DIV_MULT_THM2]
  \\ `EVEN x` suffices_by metis_tac[EVEN_MOD2,SUB_0]
  \\ `MEM x (MAP FST moves)` suffices_by metis_tac[EVERY_MEM]
  \\ match_mp_tac MEM_MAP_FST_parmove
  \\ simp[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]));
val _ = if null(hyp TIMES2_DIV2_lemma) andalso null(free_vars(concl TIMES2_DIV2_lemma)) then () else raise Fail "open local lemma";
val _ = (print "times2_div2_statement="; print_term(concl TIMES2_DIV2_lemma); print "\n");
val _ = print("times2_div2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO TIMES2_DIV2_lemma))) ^ "\n");
val _ = print("times2_div2_hypotheses=" ^ Int.toString(length(hyp TIMES2_DIV2_lemma)) ^ "\n");
val parsem_parmove_DIV2_lemma = GEN_ALL (prove(``
  windmill moves ∧
   EVERY EVEN (MAP FST moves) ∧
   EVERY EVEN (MAP SND moves) ⇒
   MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
      (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves)))) =
   (MAP (parsem (MAP (SOME ## SOME) moves) (r o OPTION_MAP DIV2))
     (FILTER IS_SOME (MAP FST (parmove moves))))``,

  rw[]
  \\ drule(Q.ISPEC`DIV2`(Q.GEN`f`(ONCE_REWRITE_RULE[CONJ_COMM]parmove_MAP_INJ)))
  \\ impl_tac
  >- ( simp[] \\ rw[] \\ metis_tac[EVERY_MEM,EVEN_DIV2_INJ] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[MAP_MAP_o,o_PAIR_MAP]
  \\ simp[PAIR_MAP_SOME_SWAP]
  \\ simp[FILTER_MAP]
  \\ REWRITE_TAC[o_ASSOC]
  \\ REWRITE_TAC[IS_SOME_o_OPTION_MAP]
  \\ simp[MAP_MAP_o]
  \\ simp[MAP_EQ_f]
  \\ simp[MEM_FILTER,IS_SOME_EXISTS,PULL_EXISTS]
  \\ rw[]
  \\ simp[GSYM MAP_MAP_o]
  \\ qpat_abbrev_tac`mvs = MAP _ moves`
  \\ `windmill mvs`
  by (
    fs[parmoveTheory.windmill_def,Abbr`mvs`]
    \\ simp[MAP_MAP_o,o_PAIR_MAP]
    \\ simp[GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ qispl_then[`OPTION_MAP DIV2`,`r`]drule(Q.GENL[`f`,`r`]parsem_MAP_INJ)
  \\ simp[GSYM PULL_FORALL, GSYM AND_IMP_INTRO] >> impl_tac
  >- (
    simp[INJ_DEF]
    \\ Cases \\ simp[]
    \\ Cases \\ simp[]
    \\ fs[EVERY_MEM,Abbr`mvs`,MAP_MAP_o,o_PAIR_MAP,MEM_MAP,EXISTS_PROD]
    \\ metis_tac[EVEN_DIV2_INJ,SOME_11] )
  \\ simp[Abbr`mvs`,MEM_MAP,PULL_EXISTS]
  \\ qmatch_assum_rename_tac`MEM e (parmove moves)`
  \\ `MEM (FST e) (MAP FST (parmove moves))` by metis_tac[MEM_MAP]
  \\ rfs[]
  \\ imp_res_tac MEM_MAP_FST_parmove
  \\ fs[MEM_MAP]
  \\ disch_then drule
  \\ simp[] \\ disch_then kall_tac
  \\ rveq \\ fs[]));
val _ = if null(hyp parsem_parmove_DIV2_lemma) andalso null(free_vars(concl parsem_parmove_DIV2_lemma)) then () else raise Fail "open local lemma";
val _ = (print "parsem_parmove_div2_statement="; print_term(concl parsem_parmove_DIV2_lemma); print "\n");
val _ = print("parsem_parmove_div2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO parsem_parmove_DIV2_lemma))) ^ "\n");
val _ = print("parsem_parmove_div2_hypotheses=" ^ Int.toString(length(hyp parsem_parmove_DIV2_lemma)) ^ "\n");

(* Full typed original terms for source/carrier review; original replay is unchanged. *)
val _ = (print "times2_div2_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl TIMES2_DIV2_lemma); print "\n");
val _ = (print "parsem_parmove_div2_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl parsem_parmove_DIV2_lemma); print "\n");
