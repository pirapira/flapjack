load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "aux_data_definition="; print_thm add_to_data_aux_def; print "\n");
val _ = (print "aux_load_definition="; print_thm add_to_load_aux_def; print "\n");
val _ = (print "aux_data_type="; print_type(type_of ``add_to_data_aux``); print "\n");
val _ = (print "aux_load_type="; print_type(type_of ``add_to_load_aux``); print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "aux_data_0_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [99] 9 empty; loads_mem := balanced_map$insert listCmp [99] 9 empty |>;
          (result,program) = add_to_data_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_data_0_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [99] 9 empty; loads_mem := balanced_map$insert listCmp [99] 9 empty |>;
          (result,program) = add_to_data_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_data_1_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_data_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_data_1_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_data_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_data_2_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(3,5);(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_data_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_data_2_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(3,5);(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_data_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_0_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [99] 9 empty; loads_mem := balanced_map$insert listCmp [99] 9 empty |>;
          (result,program) = add_to_load_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_0_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [99] 9 empty; loads_mem := balanced_map$insert listCmp [99] 9 empty |>;
          (result,program) = add_to_load_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_1_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_load_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_1_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_load_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_2_2" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(3,5);(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_load_aux data 2 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;2;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
val _ = out "aux_load_2_7" ``
      let data = empty_data with <|
          to_canonical := sptree$fromAList [(3,3);(9,9)];
          to_latest := sptree$fromAList [(3,5);(9,9)];
          gets_mem := [(CurrHeap,9)]; instrs_mem := balanced_map$insert listCmp [42] 3 empty; loads_mem := balanced_map$insert listCmp [42] 3 empty |>;
          (result,program) = add_to_load_aux data 7 [42] (Tick :64 prog)
      in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;9],
          MAP (\k. sptree$lookup k result.to_latest) [3;7;9],
          MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
          MAP (\k. balanced_map$lookup listCmp k result.instrs_mem) [[42];[99]],
          MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[42];[99]],
          case program of Move priority moves => (0,priority,moves)
            | Tick => (1,0,[]) | _ => (2,0,[]))``;
