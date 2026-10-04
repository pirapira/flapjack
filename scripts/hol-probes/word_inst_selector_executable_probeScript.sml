load "preamble"; load "word_instTheory";
open HolKernel Parse bossLib preamble wordLangTheory word_instTheory asmTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail ("open HOL hypotheses: " ^ label);
   print (label ^ "="); print_term (concl th); print "\n");
val _ = checked "inst_select_definition" inst_select_def;
val _ = print "inst_select_type=";
val _ = print (type_to_string (type_of ``word_inst$inst_select``));
val _ = print "\n";
val _ = show_types := false;
(* Only valid_imm, addr_offset, hw_offset and byte_offset are read by
   inst_select; the remaining asm_config fields are left unspecified. *)
val cfg = ``(ARB : 64 asm_config) with <|
   valid_imm := (\b i. -2048w <= i /\ i <= 2047w);
   addr_offset := (-2048w, 2047w); hw_offset := (-2048w, 2047w);
   byte_offset := (-2048w, 2047w) |>``;
fun evald name tm = let
  val th = EVAL tm
  val _ = if null (hyp th) then () else raise Fail ("hyp " ^ name)
in rhs (concl th) end;
fun sel p = ``inst_select ^cfg 100 ^p``;
val _ = (print "skip="; print_term (evald "skip" (sel ``(Skip : 64 wordLang$prog)``)); print "\n");
val _ = (print "move="; print_term (evald "move" (sel ``(Move 5 [(1,2); (3,4)] : 64 wordLang$prog)``)); print "\n");
val _ = (print "inst_skip="; print_term (evald "inst_skip" (sel ``(Inst Skip : 64 wordLang$prog)``)); print "\n");
val _ = (print "inst_fp="; print_term (evald "inst_fp" (sel ``(Inst (FP (FPSqrt 1 2)) : 64 wordLang$prog)``)); print "\n");
val _ = (print "assign="; print_term (evald "assign" (sel ``(Assign 5 (Op Add [Var 1; Const 3w; Var 2]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "get="; print_term (evald "get" (sel ``(Get 3 Globals : 64 wordLang$prog)``)); print "\n");
val _ = (print "set="; print_term (evald "set" (sel ``(Set Globals (Const 3w) : 64 wordLang$prog)``)); print "\n");
val _ = (print "store="; print_term (evald "store" (sel ``(Store (Op Add [Var 1; Const 8w]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "must_terminate="; print_term (evald "must_terminate" (sel ``(MustTerminate (Assign 3 (Const 5w)) : 64 wordLang$prog)``)); print "\n");
val _ = (print "call_none="; print_term (evald "call_none" (sel ``(Call NONE (SOME 9) [1;2] NONE : 64 wordLang$prog)``)); print "\n");
val _ = (print "call_both="; print_term (evald "call_both" (sel ``(Call (SOME ([1;2],(LN,LN),Assign 3 (Const 5w),11,12)) (SOME 9) [4;5] (SOME (6,Set Globals (Const 7w),13,14)) : 64 wordLang$prog)``)); print "\n");
val _ = (print "seq="; print_term (evald "seq" (sel ``(Seq (Assign 1 (Const 2w)) (Get 3 Globals) : 64 wordLang$prog)``)); print "\n");
val _ = (print "if="; print_term (evald "if" (sel ``(If Equal 1 (Imm 0w) (Assign 3 (Const 4w)) (Store (Var 1) 2) : 64 wordLang$prog)``)); print "\n");
val _ = (print "loop="; print_term (evald "loop" (sel ``(Loop LN (Assign 1 (Const 4w)) LN : 64 wordLang$prog)``)); print "\n");
val _ = (print "alloc="; print_term (evald "alloc" (sel ``(Alloc 1 (LN,LN) : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_consts="; print_term (evald "store_consts" (sel ``(StoreConsts 1 2 3 4 [(T,7w);(F,9w)] : 64 wordLang$prog)``)); print "\n");
val _ = (print "raise="; print_term (evald "raise" (sel ``(Raise 1 : 64 wordLang$prog)``)); print "\n");
val _ = (print "return="; print_term (evald "return" (sel ``(Return 1 [2;3] : 64 wordLang$prog)``)); print "\n");
val _ = (print "break="; print_term (evald "break" (sel ``(Break 1 : 64 wordLang$prog)``)); print "\n");
val _ = (print "continue="; print_term (evald "continue" (sel ``(Continue 2 : 64 wordLang$prog)``)); print "\n");
val _ = (print "tick="; print_term (evald "tick" (sel ``(Tick : 64 wordLang$prog)``)); print "\n");
val _ = (print "curr_heap="; print_term (evald "curr_heap" (sel ``(OpCurrHeap Sub 1 2 : 64 wordLang$prog)``)); print "\n");
val _ = (print "loc_value="; print_term (evald "loc_value" (sel ``(LocValue 1 2 : 64 wordLang$prog)``)); print "\n");
val _ = (print "install="; print_term (evald "install" (sel ``(Install 1 2 3 4 (LN,LN) : 64 wordLang$prog)``)); print "\n");
val _ = (print "code_write="; print_term (evald "code_write" (sel ``(CodeBufferWrite 1 2 : 64 wordLang$prog)``)); print "\n");
val _ = (print "data_write="; print_term (evald "data_write" (sel ``(DataBufferWrite 1 2 : 64 wordLang$prog)``)); print "\n");
val _ = (print "ffi="; print_term (evald "ffi" (sel ``(FFI (strlit "write") 1 2 3 4 (LN,LN) : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_load8="; print_term (evald "share_load8" (sel ``(ShareInst Load8 3 (Op Add [Var 1; Const 4w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_hi="; print_term (evald "store_hi" (sel ``(Store (Op Add [Var 1; Const 2047w]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_above="; print_term (evald "store_above" (sel ``(Store (Op Add [Var 1; Const 2048w]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_lo="; print_term (evald "store_lo" (sel ``(Store (Op Add [Var 1; Const (-2048w)]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "store_below="; print_term (evald "store_below" (sel ``(Store (Op Add [Var 1; Const (-2049w)]) 4 : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_load16="; print_term (evald "share_load16" (sel ``(ShareInst Load16 3 (Op Add [Var 1; Const 8w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_load32="; print_term (evald "share_load32" (sel ``(ShareInst Load32 3 (Op Add [Var 1; Const 8w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_store="; print_term (evald "share_store" (sel ``(ShareInst Store 3 (Op Add [Var 1; Const 8w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "share_above="; print_term (evald "share_above" (sel ``(ShareInst Store8 3 (Op Add [Var 1; Const 2048w]) : 64 wordLang$prog)``)); print "\n");
val _ = (print "nested_call="; print_term (evald "nested_call" (sel ``(Call (SOME ([1],(LN,LN),Loop LN (Assign 2 (Const 3w)) LN,4,5)) NONE [6] (SOME (7,MustTerminate (Assign 8 (Const 9w)),10,11)) : 64 wordLang$prog)``)); print "\n");
