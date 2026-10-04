load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory wordSemTheory stackSemTheory wordLangTheory stackLangTheory;
val _ = Globals.linewidth := 1000000;
val motive = ``
   λ(prog:'a wordLang$prog,s:('a,num # 'c,'ffi) wordSem$state).
     ∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     comp ac F prog (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``;
val ind = wordSemTheory.evaluate_ind |> ISPEC motive |> GEN_BETA_RULE;
val obligations = ind |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;
val getCase = first (can (find_term (can (match_term ``wordLang$Install ptr len dptr dlen names``)))) obligations;
val whole = GEN_ALL (Q.SPECL [`wordLang$Install ptr len dptr dlen names`, `s`] word_to_stackProofTheory.comp_correct);
val callTh = GEN_ALL(prove(getCase,rpt gen_tac >>
  MATCH_ACCEPT_TAC (Q.SPECL [`wordLang$Install ptr len dptr dlen names`,`s`] word_to_stackProofTheory.comp_correct)));
val _ = if null(hyp whole) andalso null(free_vars(concl whole)) andalso
  null(hyp callTh) andalso null(free_vars(concl callTh)) then () else raise Fail "open case";
val _ = (print "comp_correct_install_full_statement="; print_term(concl callTh); print "\n");
val _ = print("comp_correct_install_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO callTh))) ^ "\n");
val _ = print("comp_correct_install_full_hypotheses=" ^ Int.toString(length(hyp callTh)) ^ "\n");
val _ = (print "comp_correct_install_whole_statement="; print_term(concl whole); print "\n");
val _ = print("comp_correct_install_whole_proved=" ^ term_to_string(rhs(concl(EQT_INTRO whole))) ^ "\n");
val _ = print("comp_correct_install_whole_hypotheses=" ^ Int.toString(length(hyp whole)) ^ "\n");
val _ = (Globals.show_types := true; print "comp_correct_install_full_statement_typed="; print_term(concl callTh); print "\n"; Globals.show_types := false);
