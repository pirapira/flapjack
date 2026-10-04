import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect
import Flapjack.Test.WordInstSelectExactParity
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

/-! Fresh original selector regressions. Inputs and complete expected native
programs are transcribed from word_inst_selector_executable_probe.out. Kernel
reduction checks all 37 full native program equalities. Runtime checks project
the 35 supported cases through the existing reviewed codec and compare complete
production Repr observations; either codec rejection fails the check. Inst Skip
and FP are native-only cases covered by kernel equality rather than that partial
production codec. No expected program is obtained from either Lean selector.
Original captures are regressions, not HOL-to-Lean equivalence proofs. -/

namespace Flapjack.Test.WordInstSelectorExecutableParity
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Basis.Pure.MlString
abbrev P := WordLangProgHOL (BitVec 64)

private def input_skip : P := .skip
private def expected_skip : P := .skip

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_skip =
    expected_skip := by with_unfolding_all rfl

private def input_move : P := .move 5 [(1,2), (3,4)]
private def expected_move : P := .move 5 [(1,2), (3,4)]

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_move =
    expected_move := by with_unfolding_all rfl

private def input_inst_skip : P := .inst .skip
private def expected_inst_skip : P := .inst .skip

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_inst_skip =
    expected_inst_skip := by with_unfolding_all rfl

private def input_inst_fp : P := .inst (.fp (.fpSqrt 1 2))
private def expected_inst_fp : P := .inst (.fp (.fpSqrt 1 2))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_inst_fp =
    expected_inst_fp := by with_unfolding_all rfl

private def input_assign : P := .assign 5 (.op .add [.var 1, .const 3, .var 2])
private def expected_assign : P := .seq (.seq (.move 0 [(100,2)]) (.seq (.move 0 [(101,1)]) (.inst (.arith (.binop .add 100 100 (.reg 101)))))) (.inst (.arith (.binop .add 5 100 (.imm 3))))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_assign =
    expected_assign := by with_unfolding_all rfl

private def input_get : P := .get 3 .globals
private def expected_get : P := .get 3 .globals

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_get =
    expected_get := by with_unfolding_all rfl

private def input_set : P := .set .globals (.const 3)
private def expected_set : P := .seq (.inst (.const 100 3)) (.set .globals (.var 100))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_set =
    expected_set := by with_unfolding_all rfl

private def input_store : P := .store (.op .add [.var 1, .const 8]) 4
private def expected_store : P := .seq (.move 0 [(100,1)]) (.inst (.mem .store 4 (.addr 100 8)))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store =
    expected_store := by with_unfolding_all rfl

private def input_must_terminate : P := .mustTerminate (.assign 3 (.const 5))
private def expected_must_terminate : P := .mustTerminate (.inst (.const 3 5))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_must_terminate =
    expected_must_terminate := by with_unfolding_all rfl

private def input_call_none : P := .call none (some 9) [1,2] none
private def expected_call_none : P := .call none (some 9) [1, 2] none

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_call_none =
    expected_call_none := by with_unfolding_all rfl

private def input_call_both : P := .call (some ([1,2],(.ln,.ln),.assign 3 (.const 5),11,12)) (some 9) [4,5] (some (6,.set .globals (.const 7),13,14))
private def expected_call_both : P := .call (some ([1, 2],(.ln,.ln),.inst (.const 3 5),11,12)) (some 9) [4, 5] (some (6,.seq (.inst (.const 100 7)) (.set .globals (.var 100)),13,14))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_call_both =
    expected_call_both := by with_unfolding_all rfl

private def input_seq : P := .seq (.assign 1 (.const 2)) (.get 3 .globals)
private def expected_seq : P := .seq (.inst (.const 1 2)) (.get 3 .globals)

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_seq =
    expected_seq := by with_unfolding_all rfl

private def input_if : P := .ite .equal 1 (.imm 0) (.assign 3 (.const 4)) (.store (.var 1) 2)
private def expected_if : P := .ite .equal 1 (.imm 0) (.inst (.const 3 4)) (.seq (.move 0 [(100,1)]) (.inst (.mem .store 2 (.addr 100 0))))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_if =
    expected_if := by with_unfolding_all rfl

private def input_loop : P := .loop .ln (.assign 1 (.const 4)) .ln
private def expected_loop : P := .loop .ln (.inst (.const 1 4)) .ln

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_loop =
    expected_loop := by with_unfolding_all rfl

private def input_alloc : P := .alloc 1 (.ln,.ln)
private def expected_alloc : P := .alloc 1 (.ln,.ln)

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_alloc =
    expected_alloc := by with_unfolding_all rfl

private def input_store_consts : P := .storeConsts 1 2 3 4 [(true,7),(false,9)]
private def expected_store_consts : P := .storeConsts 1 2 3 4 [(true,7), (false,9)]

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store_consts =
    expected_store_consts := by with_unfolding_all rfl

private def input_raise : P := .raise 1
private def expected_raise : P := .raise 1

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_raise =
    expected_raise := by with_unfolding_all rfl

private def input_return : P := .return 1 [2,3]
private def expected_return : P := .return 1 [2, 3]

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_return =
    expected_return := by with_unfolding_all rfl

private def input_break : P := .break 1
private def expected_break : P := .break 1

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_break =
    expected_break := by with_unfolding_all rfl

private def input_continue : P := .continue 2
private def expected_continue : P := .continue 2

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_continue =
    expected_continue := by with_unfolding_all rfl

private def input_tick : P := .tick
private def expected_tick : P := .tick

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_tick =
    expected_tick := by with_unfolding_all rfl

private def input_curr_heap : P := .opCurrHeap .sub 1 2
private def expected_curr_heap : P := .opCurrHeap .sub 1 2

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_curr_heap =
    expected_curr_heap := by with_unfolding_all rfl

private def input_loc_value : P := .locValue 1 2
private def expected_loc_value : P := .locValue 1 2

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_loc_value =
    expected_loc_value := by with_unfolding_all rfl

private def input_install : P := .install 1 2 3 4 (.ln,.ln)
private def expected_install : P := .install 1 2 3 4 (.ln,.ln)

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_install =
    expected_install := by with_unfolding_all rfl

private def input_code_write : P := .codeBufferWrite 1 2
private def expected_code_write : P := .codeBufferWrite 1 2

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_code_write =
    expected_code_write := by with_unfolding_all rfl

private def input_data_write : P := .dataBufferWrite 1 2
private def expected_data_write : P := .dataBufferWrite 1 2

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_data_write =
    expected_data_write := by with_unfolding_all rfl

private def input_ffi : P := .ffi (ofString "write") 1 2 3 4 (.ln,.ln)
private def expected_ffi : P := .ffi (ofString "write") 1 2 3 4 (.ln,.ln)

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_ffi =
    expected_ffi := by with_unfolding_all rfl

private def input_share_load8 : P := .shareInst .load8 3 (.op .add [.var 1, .const 4])
private def expected_share_load8 : P := .seq (.move 0 [(100,1)]) (.shareInst .load8 3 (.op .add [.var 100, .const 4]))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_share_load8 =
    expected_share_load8 := by with_unfolding_all rfl

private def input_store_hi : P := .store (.op .add [.var 1, .const 2047]) 4
private def expected_store_hi : P := .seq (.move 0 [(100,1)]) (.inst (.mem .store 4 (.addr 100 2047)))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store_hi =
    expected_store_hi := by with_unfolding_all rfl

private def input_store_above : P := .store (.op .add [.var 1, .const 2048]) 4
private def expected_store_above : P := .seq (.seq (.move 0 [(100,1)]) (.inst (.arith (.binop .sub 100 100 (.imm 0xFFFFFFFFFFFFF800))))) (.inst (.mem .store 4 (.addr 100 0)))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store_above =
    expected_store_above := by with_unfolding_all rfl

private def input_store_lo : P := .store (.op .add [.var 1, .const (-2048)]) 4
private def expected_store_lo : P := .seq (.move 0 [(100,1)]) (.inst (.mem .store 4 (.addr 100 0xFFFFFFFFFFFFF800)))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store_lo =
    expected_store_lo := by with_unfolding_all rfl

private def input_store_below : P := .store (.op .add [.var 1, .const (-2049)]) 4
private def expected_store_below : P := .seq (.seq (.move 0 [(100,1)]) (.seq (.inst (.const 101 0xFFFFFFFFFFFFF7FF)) (.inst (.arith (.binop .add 100 100 (.reg 101)))))) (.inst (.mem .store 4 (.addr 100 0)))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_store_below =
    expected_store_below := by with_unfolding_all rfl

private def input_share_load16 : P := .shareInst .load16 3 (.op .add [.var 1, .const 8])
private def expected_share_load16 : P := .seq (.move 0 [(100,1)]) (.shareInst .load16 3 (.op .add [.var 100, .const 8]))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_share_load16 =
    expected_share_load16 := by with_unfolding_all rfl

private def input_share_load32 : P := .shareInst .load32 3 (.op .add [.var 1, .const 8])
private def expected_share_load32 : P := .seq (.move 0 [(100,1)]) (.shareInst .load32 3 (.op .add [.var 100, .const 8]))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_share_load32 =
    expected_share_load32 := by with_unfolding_all rfl

private def input_share_store : P := .shareInst .store 3 (.op .add [.var 1, .const 8])
private def expected_share_store : P := .seq (.move 0 [(100,1)]) (.shareInst .store 3 (.op .add [.var 100, .const 8]))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_share_store =
    expected_share_store := by with_unfolding_all rfl

private def input_share_above : P := .shareInst .store8 3 (.op .add [.var 1, .const 2048])
private def expected_share_above : P := .seq (.seq (.move 0 [(100,1)]) (.inst (.arith (.binop .sub 100 100 (.imm 0xFFFFFFFFFFFFF800))))) (.shareInst .store8 3 (.var 100))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_share_above =
    expected_share_above := by with_unfolding_all rfl

private def input_nested_call : P := .call (some ([1],(.ln,.ln),.loop .ln (.assign 2 (.const 3)) .ln,4,5)) none [6] (some (7,.mustTerminate (.assign 8 (.const 9)),10,11))
private def expected_nested_call : P := .call (some ([1],(.ln,.ln),.loop .ln (.inst (.const 2 3)) .ln,4,5)) none [6] (some (7,.mustTerminate (.inst (.const 8 9)),10,11))

example : instSelectExecutable WordInstSelectExactParity.cfg 100 input_nested_call =
    expected_nested_call := by with_unfolding_all rfl

/-- Runtime comparison cannot pass by collapsing both inputs to codec NONE.
All fields of the accepted production image are observed through its full Repr. -/
private def check (input expected : P) : Bool :=
  match wordLangProgFromHOL (instSelectExecutable WordInstSelectExactParity.cfg 100 input),
      wordLangProgFromHOL expected with
  | some actual, some want => reprStr actual == reprStr want
  | _, _ => false

private def checks : List (String × Bool) := [
  ("skip", check input_skip expected_skip),
  ("move", check input_move expected_move),
  ("assign", check input_assign expected_assign),
  ("get", check input_get expected_get),
  ("set", check input_set expected_set),
  ("store", check input_store expected_store),
  ("must_terminate", check input_must_terminate expected_must_terminate),
  ("call_none", check input_call_none expected_call_none),
  ("call_both", check input_call_both expected_call_both),
  ("seq", check input_seq expected_seq),
  ("if", check input_if expected_if),
  ("loop", check input_loop expected_loop),
  ("alloc", check input_alloc expected_alloc),
  ("store_consts", check input_store_consts expected_store_consts),
  ("raise", check input_raise expected_raise),
  ("return", check input_return expected_return),
  ("break", check input_break expected_break),
  ("continue", check input_continue expected_continue),
  ("tick", check input_tick expected_tick),
  ("curr_heap", check input_curr_heap expected_curr_heap),
  ("loc_value", check input_loc_value expected_loc_value),
  ("install", check input_install expected_install),
  ("code_write", check input_code_write expected_code_write),
  ("data_write", check input_data_write expected_data_write),
  ("ffi", check input_ffi expected_ffi),
  ("share_load8", check input_share_load8 expected_share_load8),
  ("store_hi", check input_store_hi expected_store_hi),
  ("store_above", check input_store_above expected_store_above),
  ("store_lo", check input_store_lo expected_store_lo),
  ("store_below", check input_store_below expected_store_below),
  ("share_load16", check input_share_load16 expected_share_load16),
  ("share_load32", check input_share_load32 expected_share_load32),
  ("share_store", check input_share_store expected_share_store),
  ("share_above", check input_share_above expected_share_above),
  ("nested_call", check input_nested_call expected_nested_call)
 ]

def runChecks : IO Bool := do
  for (label, ok) in checks do
    unless ok do throw (IO.userError ("original native selector mismatch: " ++ label))
  IO.println "PASS executable full native inst_select: 37 kernel cases and 35 runtime cases"
  return true

end Flapjack.Test.WordInstSelectorExecutableParity
