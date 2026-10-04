load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "memory_source_type="; print_type(type_of ``word_cseInst``); print "\n");
val _ = (print "memory_source_definition="; print_thm word_cseInst_def; print "\n");
val _ = (print "memory_inst_caller_clause="; print_term(List.nth(boolSyntax.strip_conj(concl word_cse_def),1)); print "\n");
val _ = (print "memory_wf_definition="; print_thm wf_data_def; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "memory_0" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_1" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_2" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_3" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_4" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_5" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_6" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_7" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_8" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_9" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_10" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_11" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_12" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :64 word);loadToNumList Load 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_13" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (18446744073709551615w :64 word);loadToNumList Load 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_14" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_15" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_16" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_17" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_18" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_19" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_20" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_21" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_22" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_23" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_24" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_25" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_26" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :64 word);loadToNumList Load8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_27" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (18446744073709551615w :64 word);loadToNumList Load8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_28" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_29" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_30" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_31" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_32" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_33" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_34" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_35" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_36" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_37" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_38" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_39" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_40" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :64 word);loadToNumList Load16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_41" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (18446744073709551615w :64 word);loadToNumList Load16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_42" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_43" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_44" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_45" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_46" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_47" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_48" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_49" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_50" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_51" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_52" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_53" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_54" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :64 word);loadToNumList Load32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_55" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (18446744073709551615w :64 word);loadToNumList Load32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_56" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_57" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_58" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_59" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_60" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_61" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_62" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_63" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_64" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_65" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_66" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_67" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_68" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :64 word);loadToNumList Store 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_69" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (18446744073709551615w :64 word);loadToNumList Store 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_70" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_71" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_72" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_73" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_74" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_75" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_76" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_77" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_78" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_79" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_80" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_81" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_82" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :64 word);loadToNumList Store8 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_83" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (18446744073709551615w :64 word);loadToNumList Store8 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_84" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_85" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_86" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_87" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_88" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_89" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_90" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_91" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_92" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_93" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_94" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_95" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_96" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :64 word);loadToNumList Store16 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_97" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (18446744073709551615w :64 word);loadToNumList Store16 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_98" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_99" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_100" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_101" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_102" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 2 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_103" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 2 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_104" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 8 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_105" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 8 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_106" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 9 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_107" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 9 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_108" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 3 (0w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_109" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 3 (18446744073709551615w :64 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_110" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :64 word);loadToNumList Store32 3 (0w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_111" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (18446744073709551615w :64 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (18446744073709551615w :64 word);loadToNumList Store32 3 (18446744073709551615w :64 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_112" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :1 word);loadToNumList Load 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_113" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1w :1 word);loadToNumList Load 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_114" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :1 word);loadToNumList Load 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_115" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1w :1 word);loadToNumList Load 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_116" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :1 word);loadToNumList Load 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_117" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1w :1 word);loadToNumList Load 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_118" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :1 word);loadToNumList Load8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_119" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1w :1 word);loadToNumList Load8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_120" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :1 word);loadToNumList Load8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_121" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1w :1 word);loadToNumList Load8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_122" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :1 word);loadToNumList Load8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_123" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1w :1 word);loadToNumList Load8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_124" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :1 word);loadToNumList Load16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_125" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1w :1 word);loadToNumList Load16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_126" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :1 word);loadToNumList Load16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_127" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1w :1 word);loadToNumList Load16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_128" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :1 word);loadToNumList Load16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_129" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1w :1 word);loadToNumList Load16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_130" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :1 word);loadToNumList Load32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_131" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1w :1 word);loadToNumList Load32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_132" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :1 word);loadToNumList Load32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_133" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1w :1 word);loadToNumList Load32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_134" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :1 word);loadToNumList Load32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_135" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1w :1 word);loadToNumList Load32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_136" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :1 word);loadToNumList Store 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_137" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1w :1 word);loadToNumList Store 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_138" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :1 word);loadToNumList Store 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_139" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1w :1 word);loadToNumList Store 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_140" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :1 word);loadToNumList Store 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_141" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1w :1 word);loadToNumList Store 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_142" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :1 word);loadToNumList Store8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_143" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1w :1 word);loadToNumList Store8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_144" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :1 word);loadToNumList Store8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_145" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1w :1 word);loadToNumList Store8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_146" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :1 word);loadToNumList Store8 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_147" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1w :1 word);loadToNumList Store8 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_148" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :1 word);loadToNumList Store16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_149" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1w :1 word);loadToNumList Store16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_150" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :1 word);loadToNumList Store16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_151" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1w :1 word);loadToNumList Store16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_152" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :1 word);loadToNumList Store16 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_153" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1w :1 word);loadToNumList Store16 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_154" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :1 word);loadToNumList Store32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_155" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1w :1 word);loadToNumList Store32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_156" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :1 word);loadToNumList Store32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_157" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (1w :1 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1w :1 word);loadToNumList Store32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_158" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :1 word);loadToNumList Store32 3 (0w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_159" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1w :1 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1w :1 word);loadToNumList Store32 3 (1w :1 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_160" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :8 word);loadToNumList Load 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_161" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (255w :8 word);loadToNumList Load 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_162" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :8 word);loadToNumList Load 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_163" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (255w :8 word);loadToNumList Load 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_164" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :8 word);loadToNumList Load 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_165" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (255w :8 word);loadToNumList Load 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_166" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :8 word);loadToNumList Load8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_167" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (255w :8 word);loadToNumList Load8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_168" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :8 word);loadToNumList Load8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_169" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (255w :8 word);loadToNumList Load8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_170" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :8 word);loadToNumList Load8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_171" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (255w :8 word);loadToNumList Load8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_172" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :8 word);loadToNumList Load16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_173" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (255w :8 word);loadToNumList Load16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_174" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :8 word);loadToNumList Load16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_175" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (255w :8 word);loadToNumList Load16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_176" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :8 word);loadToNumList Load16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_177" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (255w :8 word);loadToNumList Load16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_178" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :8 word);loadToNumList Load32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_179" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (255w :8 word);loadToNumList Load32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_180" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :8 word);loadToNumList Load32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_181" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (255w :8 word);loadToNumList Load32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_182" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :8 word);loadToNumList Load32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_183" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (255w :8 word);loadToNumList Load32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_184" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :8 word);loadToNumList Store 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_185" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (255w :8 word);loadToNumList Store 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_186" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :8 word);loadToNumList Store 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_187" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (255w :8 word);loadToNumList Store 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_188" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :8 word);loadToNumList Store 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_189" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (255w :8 word);loadToNumList Store 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_190" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :8 word);loadToNumList Store8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_191" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (255w :8 word);loadToNumList Store8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_192" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :8 word);loadToNumList Store8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_193" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (255w :8 word);loadToNumList Store8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_194" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :8 word);loadToNumList Store8 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_195" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (255w :8 word);loadToNumList Store8 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_196" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :8 word);loadToNumList Store16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_197" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (255w :8 word);loadToNumList Store16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_198" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :8 word);loadToNumList Store16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_199" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (255w :8 word);loadToNumList Store16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_200" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :8 word);loadToNumList Store16 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_201" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (255w :8 word);loadToNumList Store16 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_202" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :8 word);loadToNumList Store32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_203" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (255w :8 word);loadToNumList Store32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_204" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :8 word);loadToNumList Store32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_205" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (255w :8 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (255w :8 word);loadToNumList Store32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_206" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :8 word);loadToNumList Store32 3 (0w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_207" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (255w :8 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (255w :8 word);loadToNumList Store32 3 (255w :8 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_208" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :80 word);loadToNumList Load 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_209" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1208925819614629174706175w :80 word);loadToNumList Load 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_210" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :80 word);loadToNumList Load 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_211" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1208925819614629174706175w :80 word);loadToNumList Load 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_212" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (0w :80 word);loadToNumList Load 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_213" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load 9 (1208925819614629174706175w :80 word);loadToNumList Load 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_214" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :80 word);loadToNumList Load8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_215" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1208925819614629174706175w :80 word);loadToNumList Load8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_216" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :80 word);loadToNumList Load8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_217" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load8 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1208925819614629174706175w :80 word);loadToNumList Load8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_218" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (0w :80 word);loadToNumList Load8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_219" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load8 9 (1208925819614629174706175w :80 word);loadToNumList Load8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_220" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :80 word);loadToNumList Load16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_221" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1208925819614629174706175w :80 word);loadToNumList Load16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_222" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :80 word);loadToNumList Load16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_223" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load16 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1208925819614629174706175w :80 word);loadToNumList Load16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_224" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (0w :80 word);loadToNumList Load16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_225" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load16 9 (1208925819614629174706175w :80 word);loadToNumList Load16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_226" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :80 word);loadToNumList Load32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_227" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1208925819614629174706175w :80 word);loadToNumList Load32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_228" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :80 word);loadToNumList Load32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_229" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Load32 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1208925819614629174706175w :80 word);loadToNumList Load32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_230" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (0w :80 word);loadToNumList Load32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_231" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Load32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Load32 9 (1208925819614629174706175w :80 word);loadToNumList Load32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_232" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :80 word);loadToNumList Store 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_233" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1208925819614629174706175w :80 word);loadToNumList Store 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_234" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :80 word);loadToNumList Store 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_235" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1208925819614629174706175w :80 word);loadToNumList Store 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_236" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (0w :80 word);loadToNumList Store 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_237" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store 9 (1208925819614629174706175w :80 word);loadToNumList Store 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_238" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :80 word);loadToNumList Store8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_239" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1208925819614629174706175w :80 word);loadToNumList Store8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_240" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :80 word);loadToNumList Store8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_241" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store8 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1208925819614629174706175w :80 word);loadToNumList Store8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_242" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (0w :80 word);loadToNumList Store8 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_243" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store8 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store8 9 (1208925819614629174706175w :80 word);loadToNumList Store8 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_244" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :80 word);loadToNumList Store16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_245" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1208925819614629174706175w :80 word);loadToNumList Store16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_246" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :80 word);loadToNumList Store16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_247" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store16 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1208925819614629174706175w :80 word);loadToNumList Store16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_248" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (0w :80 word);loadToNumList Store16 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_249" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store16 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store16 9 (1208925819614629174706175w :80 word);loadToNumList Store16 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_250" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :80 word);loadToNumList Store32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_251" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1208925819614629174706175w :80 word);loadToNumList Store32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_252" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (0w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :80 word);loadToNumList Store32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_253" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp (loadToNumList Store32 9 (1208925819614629174706175w :80 word)) 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1208925819614629174706175w :80 word);loadToNumList Store32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_254" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (0w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (0w :80 word);loadToNumList Store32 3 (0w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
val _ = out "memory_255" ``
  let data = empty_data with <|
      to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
      to_latest := sptree$fromAList [(3,5);(9,9)];
      gets_mem := [(CurrHeap,3)];
      instrs_mem := balanced_map$insert listCmp [99] 3 empty;
      loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cseInst data (Mem Store32 7 (Addr 9 (1208925819614629174706175w :80 word)))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem)
        [loadToNumList Store32 9 (1208925819614629174706175w :80 word);loadToNumList Store32 3 (1208925819614629174706175w :80 word);[99]],
      case program of Inst (Mem mop r (Addr a ofs)) => (1,memOpToNum mop,r,a,w2n ofs)
        | Move priority [(r,current)] => (0,priority,r,current,0)
        | _ => (2,0,0,0,0))``;
