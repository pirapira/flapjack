load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "heap_loc_source_type="; print_type(type_of ``word_cse``); print "\n");
val _ = (print "heap_loc_source_definition="; print_thm word_cse_def; print "\n");
val _ = (print "heap_loc_inst_caller_clause="; print_term(List.nth(boolSyntax.strip_conj(concl word_cse_def),1)); print "\n");
val _ = (print "heap_loc_wf_definition="; print_thm wf_data_def; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "heap_loc_0" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_1" ``
  let key = OpCurrHeapToNumList Add 9;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_2" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 2 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 2 (invalidate_data data 2) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_3" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 7 8 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 7 (invalidate_data data 7) 8);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_4" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 9 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 9 (invalidate_data data 9) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_5" ``
  let key = OpCurrHeapToNumList Add 3;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_6" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_7" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Add 1208925819614629174706183 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [1208925819614629174706183;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;1208925819614629174706183;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Add (canonicalRegs' 1208925819614629174706183 (invalidate_data data 1208925819614629174706183) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_8" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_9" ``
  let key = OpCurrHeapToNumList Sub 9;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_10" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 2 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 2 (invalidate_data data 2) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_11" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 7 8 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 7 (invalidate_data data 7) 8);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_12" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 9 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 9 (invalidate_data data 9) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_13" ``
  let key = OpCurrHeapToNumList Sub 3;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_14" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_15" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Sub 1208925819614629174706183 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [1208925819614629174706183;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;1208925819614629174706183;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Sub (canonicalRegs' 1208925819614629174706183 (invalidate_data data 1208925819614629174706183) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_16" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_17" ``
  let key = OpCurrHeapToNumList And 9;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_18" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 2 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 2 (invalidate_data data 2) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_19" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 7 8 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 7 (invalidate_data data 7) 8);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_20" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 9 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 9 (invalidate_data data 9) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_21" ``
  let key = OpCurrHeapToNumList And 3;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_22" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_23" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap And 1208925819614629174706183 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [1208925819614629174706183;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;1208925819614629174706183;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList And (canonicalRegs' 1208925819614629174706183 (invalidate_data data 1208925819614629174706183) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_24" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_25" ``
  let key = OpCurrHeapToNumList Or 9;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_26" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 2 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 2 (invalidate_data data 2) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_27" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 7 8 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 7 (invalidate_data data 7) 8);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_28" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 9 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 9 (invalidate_data data 9) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_29" ``
  let key = OpCurrHeapToNumList Or 3;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_30" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_31" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Or 1208925819614629174706183 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [1208925819614629174706183;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;1208925819614629174706183;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Or (canonicalRegs' 1208925819614629174706183 (invalidate_data data 1208925819614629174706183) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_32" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_33" ``
  let key = OpCurrHeapToNumList Xor 9;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_34" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 2 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 2 (invalidate_data data 2) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_35" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 7 8 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 7 (invalidate_data data 7) 8);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_36" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 9 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 9 (invalidate_data data 9) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_37" ``
  let key = OpCurrHeapToNumList Xor 3;
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_38" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 7 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 7 (invalidate_data data 7) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_39" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (OpCurrHeap Xor 1208925819614629174706183 9 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [1208925819614629174706183;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;1208925819614629174706183;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [OpCurrHeapToNumList Xor (canonicalRegs' 1208925819614629174706183 (invalidate_data data 1208925819614629174706183) 9);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_40" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 0 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;0];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_41" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 23 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;23];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_42" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 1208925819614629174706193 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;1208925819614629174706193];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_43" ``
  let key = [48;0];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 0 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;0];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_44" ``
  let key = [48;23];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 23 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;23];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_45" ``
  let key = [48;1208925819614629174706193];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 7 1208925819614629174706193 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;1208925819614629174706193];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_46" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 0 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;0];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_47" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 23 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;23];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_48" ``
  let key = [99];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 1208925819614629174706193 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;1208925819614629174706193];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_49" ``
  let key = [48;0];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 0 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;0];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_50" ``
  let key = [48;23];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 23 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;23];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
val _ = out "heap_loc_51" ``
  let key = [48;1208925819614629174706193];
      data = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp key 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      (result,program) = word_cse data (LocValue 2 1208925819614629174706193 :64 prog)
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[48;1208925819614629174706193];key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of OpCurrHeap b r s => (1,arithOpToNum b,r,s)
        | LocValue r l => (2,48,r,l)
        | Move priority [(r,current)] => (0,priority,r,current)
        | _ => (3,0,0,0))``;
