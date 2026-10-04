load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseTheory word_cseProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Feedback.set_trace "types" 1;
val _ = (print "assign_source_type="; print_type(type_of ``word_cse``); print "\n");
val _ = (print "assign_source_definition="; print_thm word_cse_def; print "\n");
val _ = Feedback.set_trace "types" 0;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "assign_empty_load" ``word_cse empty_data
  (Assign 7 (Load (Op Add [Var 9;Const (0w:64 word)]))) =
  (empty_data,Assign 7 (Load (Op Add [Var 9;Const (0w:64 word)])))``;
val _ = out "assign_even_load" ``word_cse empty_data
  (Assign 2 (Load (Op Add [Var 9;Const (7w:64 word)]))) =
  (empty_data,Assign 2 (Load (Op Add [Var 9;Const (7w:64 word)])))``;
val _ = out "assign_alias_load" ``word_cse empty_data
  (Assign 9 (Load (Op Add [Var 9;Const (7w:64 word)]))) =
  (empty_data,Assign 9 (Load (Op Add [Var 9;Const (7w:64 word)])))``;
val _ = out "assign_seeded_load" ``let data = empty_data with <|
  to_canonical := sptree$fromAList [(3,3);(5,5);(7,3);(9,9)];
  to_latest := sptree$fromAList [(3,5);(9,9)];
  gets_mem := [(CurrHeap,3)];
  instrs_mem := balanced_map$insert listCmp [99] 3 empty;
  loads_mem := balanced_map$insert listCmp [21;109;0] 3 empty |>
  in word_cse data (Assign 7 (Load (Op Add [Var 9;Const (0w:64 word)]))) =
     (data,Assign 7 (Load (Op Add [Var 9;Const (0w:64 word)])))``;
val _ = out "assign_large_load" ``word_cse empty_data
  (Assign 1208925819614629174706183 (Load (Op Add [Var 9;Const (1208925819614629174706175w:80 word)]))) =
  (empty_data,Assign 1208925819614629174706183 (Load (Op Add [Var 9;Const (1208925819614629174706175w:80 word)])))``;
val _ = out "assign_const" ``word_cse empty_data (Assign 7 (Const (255w:8 word))) =
  (empty_data,Assign 7 (Const (255w:8 word)))``;
val _ = out "assign_var" ``word_cse empty_data (Assign 7 (Var 9:1 exp)) =
  (empty_data,Assign 7 (Var 9:1 exp))``;
val _ = out "assign_lookup" ``word_cse empty_data (Assign 7 (Lookup CurrHeap:64 exp)) =
  (empty_data,Assign 7 (Lookup CurrHeap:64 exp))``;
val _ = out "assign_op" ``word_cse empty_data (Assign 7 (Op Xor [Var 9;Const (3w:64 word)])) =
  (empty_data,Assign 7 (Op Xor [Var 9;Const (3w:64 word)]))``;
val _ = out "assign_shift" ``word_cse empty_data (Assign 7 (Shift Lsl (Var 9) (Var 5):64 exp)) =
  (empty_data,Assign 7 (Shift Lsl (Var 9) (Var 5):64 exp))``;
val _ = out "assign_nested_load" ``word_cse empty_data (Assign 7 (Load (Load (Var 9)):64 exp)) =
  (empty_data,Assign 7 (Load (Load (Var 9)):64 exp))``;
