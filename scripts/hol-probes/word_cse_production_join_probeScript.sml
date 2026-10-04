load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "join_type="; print_type (type_of ``merge_data``); print "\n");
val _ = (print "join_definition="; print_thm merge_data_def; print "\n");
val _ = (print "join_wf_definition="; print_thm wf_data_def; print "\n");
val _ = (print "join_wf_preservation="; print_thm word_cse_wf_data; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "join_fields" ``
  let a = empty_data with <|
    to_canonical := sptree$fromAList [(1,11);(3,33);(5,55)];
    to_latest := sptree$fromAList [(1,99)];
    gets_mem := [(CurrHeap,11);(NextFree,33);(EndOfHeap,55)];
    instrs_mem := balanced_map$insert listCmp [] 11
      (balanced_map$insert listCmp [1] 33 (balanced_map$insert listCmp [1;2] 55 empty));
    loads_mem := balanced_map$insert listCmp [] 11
      (balanced_map$insert listCmp [1] 33 (balanced_map$insert listCmp [1;2] 55 empty)) |>;
      b = empty_data with <|
    to_canonical := sptree$fromAList [(1,11);(3,333);(7,77)];
    to_latest := sptree$fromAList [(1,99)];
    gets_mem := [(CurrHeap,11);(NextFree,333);(Temp 3w,77)];
    instrs_mem := balanced_map$insert listCmp [] 11
      (balanced_map$insert listCmp [1] 333 (balanced_map$insert listCmp [7] 77 empty));
    loads_mem := balanced_map$insert listCmp [] 11
      (balanced_map$insert listCmp [1] 333 (balanced_map$insert listCmp [7] 77 empty)) |>;
      j = merge_data a b
  in (MAP (\k. sptree$lookup k j.to_canonical) [1;3;5;7],
      MAP (\k. sptree$lookup k j.to_latest) [1;3],
      MAP (ALOOKUP j.gets_mem) [CurrHeap;NextFree;EndOfHeap;Temp 3w],
      MAP (\k. balanced_map$lookup listCmp k j.instrs_mem) [[];[1];[1;2];[7]],
      MAP (\k. balanced_map$lookup listCmp k j.loads_mem) [[];[1];[1;2];[7]])``;
val _ = out "join_empty" ``merge_data empty_data empty_data = empty_data``;
val _ = out "join_duplicate_boundary" ``
  let a = empty_data with gets_mem := [(CurrHeap,11);(CurrHeap,33)];
      b = empty_data with gets_mem := [(CurrHeap,33)]
  in (ALOOKUP a.gets_mem CurrHeap,
      ALOOKUP (merge_data a b).gets_mem CurrHeap,
      ALL_DISTINCT (MAP FST a.gets_mem))``;
