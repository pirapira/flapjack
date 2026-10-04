load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "arithmetic_source_type="; print_type(type_of ``word_cseInst``); print "\n");
val _ = (print "arithmetic_source_definition="; print_thm word_cseInst_def; print "\n");
val _ = (print "arithmetic_inst_caller_clause="; print_term(List.nth(boolSyntax.strip_conj(concl word_cse_def),1)); print "\n");
val _ = (print "arithmetic_wf_definition="; print_thm wf_data_def; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "arithmetic_0" ``
  let operation = (Binop Add 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_1" ``
  let operation = (Binop Add 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_2" ``
  let operation = (Binop Add 2 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_3" ``
  let operation = (Binop Add 9 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_4" ``
  let operation = (Binop Add 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_5" ``
  let operation = (Binop Add 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_6" ``
  let operation = (Binop Sub 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_7" ``
  let operation = (Binop Sub 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_8" ``
  let operation = (Binop Sub 2 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_9" ``
  let operation = (Binop Sub 9 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_10" ``
  let operation = (Binop Sub 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_11" ``
  let operation = (Binop Sub 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_12" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_13" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_14" ``
  let operation = (Shift Lsl 2 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_15" ``
  let operation = (Shift Lsl 9 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_16" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_17" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_18" ``
  let operation = (Shift Lsr 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_19" ``
  let operation = (Shift Lsr 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_20" ``
  let operation = (Shift Lsr 2 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_21" ``
  let operation = (Shift Lsr 9 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_22" ``
  let operation = (Shift Lsr 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_23" ``
  let operation = (Shift Lsr 7 9 (Imm (1w :1 word)) :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_24" ``
  let operation = (Div 7 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_25" ``
  let operation = (Div 7 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_26" ``
  let operation = (Div 2 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_27" ``
  let operation = (Div 9 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_28" ``
  let operation = (Div 7 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_29" ``
  let operation = (Div 7 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_30" ``
  let operation = (LongMul 7 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_31" ``
  let operation = (LongMul 7 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_32" ``
  let operation = (LongMul 2 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_33" ``
  let operation = (LongMul 9 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_34" ``
  let operation = (LongMul 7 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_35" ``
  let operation = (LongMul 7 11 9 5 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_36" ``
  let operation = (LongDiv 7 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_37" ``
  let operation = (LongDiv 7 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_38" ``
  let operation = (LongDiv 2 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_39" ``
  let operation = (LongDiv 9 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_40" ``
  let operation = (LongDiv 7 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_41" ``
  let operation = (LongDiv 7 11 9 5 3 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_42" ``
  let operation = (AddCarry 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_43" ``
  let operation = (AddCarry 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_44" ``
  let operation = (AddCarry 2 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_45" ``
  let operation = (AddCarry 9 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_46" ``
  let operation = (AddCarry 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_47" ``
  let operation = (AddCarry 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_48" ``
  let operation = (AddOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_49" ``
  let operation = (AddOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_50" ``
  let operation = (AddOverflow 2 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_51" ``
  let operation = (AddOverflow 9 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_52" ``
  let operation = (AddOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_53" ``
  let operation = (AddOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_54" ``
  let operation = (SubOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_55" ``
  let operation = (SubOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_56" ``
  let operation = (SubOverflow 2 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_57" ``
  let operation = (SubOverflow 9 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_58" ``
  let operation = (SubOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_59" ``
  let operation = (SubOverflow 7 9 5 11 :1 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_60" ``
  let operation = (Binop Add 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_61" ``
  let operation = (Binop Add 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_62" ``
  let operation = (Binop Add 2 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_63" ``
  let operation = (Binop Add 9 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_64" ``
  let operation = (Binop Add 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_65" ``
  let operation = (Binop Add 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_66" ``
  let operation = (Binop Sub 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_67" ``
  let operation = (Binop Sub 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_68" ``
  let operation = (Binop Sub 2 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_69" ``
  let operation = (Binop Sub 9 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_70" ``
  let operation = (Binop Sub 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_71" ``
  let operation = (Binop Sub 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_72" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_73" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_74" ``
  let operation = (Shift Lsl 2 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_75" ``
  let operation = (Shift Lsl 9 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_76" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_77" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_78" ``
  let operation = (Shift Lsr 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_79" ``
  let operation = (Shift Lsr 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_80" ``
  let operation = (Shift Lsr 2 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_81" ``
  let operation = (Shift Lsr 9 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_82" ``
  let operation = (Shift Lsr 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_83" ``
  let operation = (Shift Lsr 7 9 (Imm (255w :8 word)) :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_84" ``
  let operation = (Div 7 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_85" ``
  let operation = (Div 7 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_86" ``
  let operation = (Div 2 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_87" ``
  let operation = (Div 9 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_88" ``
  let operation = (Div 7 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_89" ``
  let operation = (Div 7 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_90" ``
  let operation = (LongMul 7 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_91" ``
  let operation = (LongMul 7 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_92" ``
  let operation = (LongMul 2 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_93" ``
  let operation = (LongMul 9 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_94" ``
  let operation = (LongMul 7 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_95" ``
  let operation = (LongMul 7 11 9 5 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_96" ``
  let operation = (LongDiv 7 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_97" ``
  let operation = (LongDiv 7 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_98" ``
  let operation = (LongDiv 2 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_99" ``
  let operation = (LongDiv 9 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_100" ``
  let operation = (LongDiv 7 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_101" ``
  let operation = (LongDiv 7 11 9 5 3 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_102" ``
  let operation = (AddCarry 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_103" ``
  let operation = (AddCarry 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_104" ``
  let operation = (AddCarry 2 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_105" ``
  let operation = (AddCarry 9 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_106" ``
  let operation = (AddCarry 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_107" ``
  let operation = (AddCarry 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_108" ``
  let operation = (AddOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_109" ``
  let operation = (AddOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_110" ``
  let operation = (AddOverflow 2 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_111" ``
  let operation = (AddOverflow 9 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_112" ``
  let operation = (AddOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_113" ``
  let operation = (AddOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_114" ``
  let operation = (SubOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_115" ``
  let operation = (SubOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_116" ``
  let operation = (SubOverflow 2 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_117" ``
  let operation = (SubOverflow 9 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_118" ``
  let operation = (SubOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_119" ``
  let operation = (SubOverflow 7 9 5 11 :8 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_120" ``
  let operation = (Binop Add 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_121" ``
  let operation = (Binop Add 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_122" ``
  let operation = (Binop Add 2 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_123" ``
  let operation = (Binop Add 9 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_124" ``
  let operation = (Binop Add 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_125" ``
  let operation = (Binop Add 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_126" ``
  let operation = (Binop Sub 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_127" ``
  let operation = (Binop Sub 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_128" ``
  let operation = (Binop Sub 2 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_129" ``
  let operation = (Binop Sub 9 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_130" ``
  let operation = (Binop Sub 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_131" ``
  let operation = (Binop Sub 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_132" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_133" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_134" ``
  let operation = (Shift Lsl 2 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_135" ``
  let operation = (Shift Lsl 9 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_136" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_137" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_138" ``
  let operation = (Shift Lsr 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_139" ``
  let operation = (Shift Lsr 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_140" ``
  let operation = (Shift Lsr 2 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_141" ``
  let operation = (Shift Lsr 9 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_142" ``
  let operation = (Shift Lsr 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_143" ``
  let operation = (Shift Lsr 7 9 (Imm (18446744073709551615w :64 word)) :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_144" ``
  let operation = (Div 7 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_145" ``
  let operation = (Div 7 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_146" ``
  let operation = (Div 2 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_147" ``
  let operation = (Div 9 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_148" ``
  let operation = (Div 7 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_149" ``
  let operation = (Div 7 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_150" ``
  let operation = (LongMul 7 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_151" ``
  let operation = (LongMul 7 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_152" ``
  let operation = (LongMul 2 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_153" ``
  let operation = (LongMul 9 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_154" ``
  let operation = (LongMul 7 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_155" ``
  let operation = (LongMul 7 11 9 5 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_156" ``
  let operation = (LongDiv 7 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_157" ``
  let operation = (LongDiv 7 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_158" ``
  let operation = (LongDiv 2 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_159" ``
  let operation = (LongDiv 9 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_160" ``
  let operation = (LongDiv 7 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_161" ``
  let operation = (LongDiv 7 11 9 5 3 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_162" ``
  let operation = (AddCarry 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_163" ``
  let operation = (AddCarry 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_164" ``
  let operation = (AddCarry 2 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_165" ``
  let operation = (AddCarry 9 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_166" ``
  let operation = (AddCarry 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_167" ``
  let operation = (AddCarry 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_168" ``
  let operation = (AddOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_169" ``
  let operation = (AddOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_170" ``
  let operation = (AddOverflow 2 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_171" ``
  let operation = (AddOverflow 9 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_172" ``
  let operation = (AddOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_173" ``
  let operation = (AddOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_174" ``
  let operation = (SubOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_175" ``
  let operation = (SubOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_176" ``
  let operation = (SubOverflow 2 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_177" ``
  let operation = (SubOverflow 9 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_178" ``
  let operation = (SubOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_179" ``
  let operation = (SubOverflow 7 9 5 11 :64 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_180" ``
  let operation = (Binop Add 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_181" ``
  let operation = (Binop Add 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_182" ``
  let operation = (Binop Add 2 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_183" ``
  let operation = (Binop Add 9 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_184" ``
  let operation = (Binop Add 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_185" ``
  let operation = (Binop Add 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_186" ``
  let operation = (Binop Sub 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_187" ``
  let operation = (Binop Sub 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_188" ``
  let operation = (Binop Sub 2 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_189" ``
  let operation = (Binop Sub 9 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_190" ``
  let operation = (Binop Sub 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_191" ``
  let operation = (Binop Sub 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_192" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_193" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_194" ``
  let operation = (Shift Lsl 2 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_195" ``
  let operation = (Shift Lsl 9 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_196" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_197" ``
  let operation = (Shift Lsl 7 9 (Reg 5) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_198" ``
  let operation = (Shift Lsr 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_199" ``
  let operation = (Shift Lsr 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_200" ``
  let operation = (Shift Lsr 2 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_201" ``
  let operation = (Shift Lsr 9 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_202" ``
  let operation = (Shift Lsr 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_203" ``
  let operation = (Shift Lsr 7 9 (Imm (1208925819614629174706175w :80 word)) :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_204" ``
  let operation = (Div 7 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_205" ``
  let operation = (Div 7 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_206" ``
  let operation = (Div 2 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_207" ``
  let operation = (Div 9 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_208" ``
  let operation = (Div 7 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_209" ``
  let operation = (Div 7 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_210" ``
  let operation = (LongMul 7 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_211" ``
  let operation = (LongMul 7 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_212" ``
  let operation = (LongMul 2 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_213" ``
  let operation = (LongMul 9 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_214" ``
  let operation = (LongMul 7 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_215" ``
  let operation = (LongMul 7 11 9 5 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_216" ``
  let operation = (LongDiv 7 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_217" ``
  let operation = (LongDiv 7 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_218" ``
  let operation = (LongDiv 2 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_219" ``
  let operation = (LongDiv 9 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_220" ``
  let operation = (LongDiv 7 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_221" ``
  let operation = (LongDiv 7 11 9 5 3 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_222" ``
  let operation = (AddCarry 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_223" ``
  let operation = (AddCarry 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_224" ``
  let operation = (AddCarry 2 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_225" ``
  let operation = (AddCarry 9 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_226" ``
  let operation = (AddCarry 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_227" ``
  let operation = (AddCarry 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_228" ``
  let operation = (AddOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_229" ``
  let operation = (AddOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_230" ``
  let operation = (AddOverflow 2 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_231" ``
  let operation = (AddOverflow 9 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_232" ``
  let operation = (AddOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_233" ``
  let operation = (AddOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_234" ``
  let operation = (SubOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_235" ``
  let operation = (SubOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_236" ``
  let operation = (SubOverflow 2 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [2;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;2;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_237" ``
  let operation = (SubOverflow 9 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,9)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [9;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;9;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_238" ``
  let operation = (SubOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if T /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
val _ = out "arithmetic_239" ``
  let operation = (SubOverflow 7 9 5 11 :80 arith);
      initial = empty_data with <|
        to_canonical := sptree$fromAList [(3,3);(5,5);(9,3)];
        to_latest := sptree$fromAList [(3,5);(9,9)];
        gets_mem := [(CurrHeap,3)];
        instrs_mem := balanced_map$insert listCmp [99] 3 empty;
        loads_mem := balanced_map$insert listCmp [99] 3 empty |>;
      invalid = invalidate_regs initial (arithWrites operation);
      adjusted = canonicalArith invalid operation;
      key = if F /\ can_mem_arith adjusted /\
               ~MEM (firstRegOfArith operation) (arithReads adjusted)
            then instToNumList (Arith adjusted) else [99];
      data = initial with instrs_mem := balanced_map$insert listCmp key 3 empty;
      (result,program) = word_cse data (Inst (Arith operation))
  in (MAP (\k. sptree$lookup k result.to_canonical) [7;3;5;9;11],
      MAP (\k. sptree$lookup k result.to_latest) [3;7;9;11],
      MAP (ALOOKUP result.gets_mem) [CurrHeap;NextFree],
      MAP (\k. balanced_map$lookup listCmp k result.instrs_mem)
        [instToNumList (Arith adjusted);key;[99]],
      MAP (\k. balanced_map$lookup listCmp k result.loads_mem) [[99]],
      case program of Inst (Arith a) => (1,arithToNumList a,arithWrites a,arithReads a)
        | Move priority [(r,current)] => (0,[priority],[r],[current])
        | _ => (2,[],[],[]))``;
