import Flapjack.CrepeSemantics
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.CrepToLoopCorrectness
import Flapjack.RiscV.PanMemory

/-!
Focused executable regressions for the separate global environment introduced
by the CakeML Crepe state.  These tests exercise the state-aware evaluator
slice before the full evaluator is migrated to it.
-/

namespace Flapjack

def crepeGlobalSemanticsState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun address => if address == 200 then some 7 else none
    globals := fun address => if address == 200 then some 42 else none }

def crepeGlobalSkipContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

theorem compile_full_extCall_const_noop_state_correct_regression :
    evalCrepFullProgState [] (fun _ _ => none)
        (fun _ _ _ _ _ sourceState => some (.returned sourceState))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 30
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.extCall "noop" (.const 1) (.const 2) (.const 3) (.const 4) :
            Prog Nat)) = some (.normal crepeGlobalSemanticsState) := by
  exact compile_full_extCall_const_noop_correct crepeGlobalSkipContext
    crepeGlobalSemanticsState (fun _ _ => none)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1 2 3 4
    "noop"

theorem compile_full_pan_value_return_word_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.return (.const 7) : Prog Nat)) =
      (evalPanValueProg ([] : StructContext) 0 100 1
        (fun _ => none) (fun _ => none)
        (fun address => (crepeGlobalSemanticsState.memory address).map PanValue.word)
        (.return (.const 7) : Prog Nat)).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  exact compile_full_pan_value_return_word_correct crepeGlobalSkipContext
    ([] : StructContext) (fun _ => none) (fun _ => none)
    crepeGlobalSemanticsState (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1 7

theorem compile_full_pan_value_while_zero_state_correct_regression :
    evalCrepFullProgState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.while (.const 0) (.skip : Prog Nat))) =
      some (.normal crepeGlobalSemanticsState) ∧
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 10
        (fun _ => none) (fun _ => none)
        (fun address => (crepeGlobalSemanticsState.memory address).map PanValue.word)
        (.while (.const 0) (.skip : Prog Nat)) =
      some (.normal (fun _ => none) (fun _ => none)
        (fun address => (crepeGlobalSemanticsState.memory address).map PanValue.word)) := by
  exact compile_full_pan_value_while_zero_state_correct crepeGlobalSkipContext
    ([] : StructContext) (fun _ => none) (fun _ => none)
    (fun address => (crepeGlobalSemanticsState.memory address).map PanValue.word)
    crepeGlobalSemanticsState (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1 9
    (.skip : Prog Nat)

/- The nonzero loop composition theorem is exercised on a mutable local: the
   first condition is true, the body clears it, and the recursive condition is
   false.  This keeps the Cake source and full Crep state paths finite while
   checking that the post-body local state is threaded into the loop result. -/
def crepeGlobalLoopContext : CompileContext (RiscV.Word 8) :=
  { vars := [("x", (.one, [1]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 1 }

def crepeGlobalLoopSourceLocals : VarName → Option (PanValue (RiscV.Word 8)) :=
  fun name => if name == "x" then some (.word 1) else none

def crepeGlobalLoopState : CrepState (RiscV.Word 8) :=
  { locals := fun slot => if slot == 1 then some 1 else none
    memory := fun _ => none
    globals := fun _ => none }

def crepeGlobalLoopBody : Prog (RiscV.Word 8) :=
  .assign .local "x" (.const 0)

def crepeGlobalLoopProgram : Prog (RiscV.Word 8) :=
  .while (.var .local "x") crepeGlobalLoopBody

#guard (evalPanValueProgWithPrimitiveCallsAndFfi
    (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    ([] : StructContext) [] 0 100 1 3
    crepeGlobalLoopSourceLocals (fun _ => none) (fun _ => none)
    crepeGlobalLoopProgram).map
      (fun result => match result with
      | .normal locals _ _ => match locals "x" with
        | some (.word value) => value == 0
        | _ => false
      | _ => false) == some true

#guard (evalCrepFullProgStateFull [] (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 3 crepeGlobalLoopState
    (compileProg crepeGlobalLoopContext crepeGlobalLoopProgram)).map
      (fun result => match result with
      | .normal state => state.locals 1 == some 0
      | _ => false) == some true

/-! The full Cake exception evaluator and full Crep evaluator agree on a
    closed raised word, including the global payload spill and exception-code
    lookup. -/
def crepeFullRaiseContext : CompileContext (RiscV.Word 8) :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 1 }

def crepeFullRaiseState : CrepState (RiscV.Word 8) :=
  { locals := fun _ => none, memory := fun _ => none, globals := fun _ => none }

/- The stateful nonzero/break composition rule is exercised on a closed loop.
   Both evaluators consume the body's break and return normally with the
   complete post-body state, including the global and memory projections. -/
theorem compile_full_pan_value_while_break_compose_state_full_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 3
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.while (.const 1) (.break) : Prog (RiscV.Word 8)) =
      some (.normal (fun _ => none) (fun _ => none) (fun _ => none)) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 3 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.while (.const 1) (.break) : Prog (RiscV.Word 8))) =
      some (.normal crepeFullRaiseState) := by
  have hsourceBody :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 2
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.break : Prog (RiscV.Word 8)) =
      some (.broke (fun _ => none) (fun _ => none) (fun _ => none)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi]
  have hcrepBody :
      evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 2 crepeFullRaiseState
        (compileProg crepeFullRaiseContext (.break)) =
      some (.broke crepeFullRaiseState 0) := by
    simp [compileProg, evalCrepFullProgStateFull]
  exact compile_full_pan_value_while_break_compose_state_full
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState crepeFullRaiseState
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 2 (.const 1) (.const 1) (.break)
    (compileProg crepeFullRaiseContext (.break))
    1 1 (by simp [compileExp]) (by rfl)
    (by simp [evalPanValueExp])
    (by simp [evalCrepFullExpStateFull]) rfl (by decide)
    hsourceBody hcrepBody

def crepeFullLoadContext : CompileContext (RiscV.Word 8) :=
  { vars := [("x", (.one, [1]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 1 }

def crepeFullLoadState : CrepState (RiscV.Word 8) :=
  { locals := fun slot => if slot == 1 then some 0 else none
    memory := fun address => if address == 7 then some 42 else none
    globals := fun _ => none }

def crepeFullRecordAssignContext : CompileContext (RiscV.Word 8) :=
  { vars := [("pair", (.comb [.one, .one], [1, 2]))], functions := [],
    exceptions := [], maxVar := 2, bytesInWord := 1 }

def crepeFullRecordAssignState : CrepState (RiscV.Word 8) :=
  { locals := fun slot => if slot == 1 then some 0 else
      if slot == 2 then some 1 else none
    memory := fun _ => none
    globals := fun _ => none }

/- The exact structured-program adapter uses the Cake fixed-width shared-read
   operation at the source boundary; this guard would not hold for a legacy
   whole-cell memory fallback on a non-word-shaped cell. -/
def exactStructuredLoad : Option ((VarName → Option (PanValue (RiscV.Word 8))) ×
    (VarName → Option (PanValue (RiscV.Word 8))) ×
    ((RiscV.Word 8) → Option (PanValue (RiscV.Word 8))) ×
    List (PanValue (RiscV.Word 8))) :=
  evalPanValueProgWithPrimitiveExact
    ([] : StructContext) 0 100 1
    (fun name => if name == "x" then some (.word 0) else none)
    (fun _ => none)
    (fun address => if address == 7 then some (.word 42) else none)
    (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel)
    (fun _ _ => none)
    (.shMemLoad .opW .local "x" (.const 7) : Prog (RiscV.Word 8))

#guard match exactStructuredLoad with
  | some (locals, _, _, []) =>
      match locals "x" with
      | some (.word value) => value == (42 : RiscV.Word 8)
      | _ => false
  | _ => false

theorem compile_full_pan_value_shMemLoad_word_state_full_regression :
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun name => if name == "x" then some (.word 0) else none)
        (fun _ => none)
        (fun address => if address == 7 then some (.word 42) else none)
        (fun _ _ => none)
        (.shMemLoad .opW .local "x" (.const 7) : Prog (RiscV.Word 8)) =
      some (updatePanValueMap
        (fun name => if name == "x" then some (.word 0) else none)
        "x" (.word 42),
        (fun _ => none),
        (fun address => if address == 7 then some (.word 42) else none), []) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 10 crepeFullLoadState
        (compileProg crepeFullLoadContext
          (.shMemLoad .opW .local "x" (.const 7) : Prog (RiscV.Word 8))) =
      some (.normal { crepeFullLoadState with
        locals := updateCrepLocal crepeFullLoadState.locals 1 42 }) := by
  exact compile_full_pan_value_shMemLoad_word_state_full_correct
    crepeFullLoadContext ([] : StructContext) []
    (fun name => if name == "x" then some (.word 0) else none)
    (fun _ => none)
    (fun address => if address == 7 then some (.word 42) else none)
    crepeFullLoadState
    { crepeFullLoadState with
        locals := updateCrepLocal crepeFullLoadState.locals 1 42 }
    (fun _ _ => none)
    (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 9 .opW "x" 1 7 42 0 (.const 7) (.const 7)
    (by simp [crepeFullLoadContext, lookupInfo])
    (by simp [evalPanValueExpFull])
    (by simp)
    (by simp [firstCompiledExpAnyShape, compileExp])
    (by simp [evalCrepFullExpStateFull])
    (by simp [defaultCrepSharedMemHandler, loadMemOpHOL,
      crepeFullLoadState])
    (by simp)

theorem compile_full_pan_value_local_assign_word_state_full_regression :
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun name => if name == "x" then some (.word 0) else none)
        (fun _ => none)
        (fun address => if address == 7 then some (.word 42) else none)
        (fun _ _ => none)
        (.assign .local "x" (.const 42) : Prog (RiscV.Word 8)) =
      some (updatePanValueMap
        (fun name => if name == "x" then some (.word 0) else none)
        "x" (.word 42),
        (fun _ => none),
        (fun address => if address == 7 then some (.word 42) else none), []) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 10 crepeFullLoadState
        (compileProg crepeFullLoadContext
          (.assign .local "x" (.const 42) : Prog (RiscV.Word 8))) =
      some (.normal { crepeFullLoadState with
        locals := updateCrepLocal crepeFullLoadState.locals 1 42 }) := by
  exact compile_full_pan_value_local_assign_word_state_full_correct
    crepeFullLoadContext ([] : StructContext)
    (fun name => if name == "x" then some (.word 0) else none)
    (fun _ => none)
    (fun address => if address == 7 then some (.word 42) else none)
    crepeFullLoadState (fun _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 42 0 8 "x" 1
    (by simp [crepeFullLoadContext, lookupInfo])
    (by simp)
    (by simp [crepeFullLoadState])

theorem compile_full_pan_value_local_assign_record_state_full_regression :
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 30 crepeFullRecordAssignState
        (compileProg crepeFullRecordAssignContext
          (.assign .local "pair"
            (.rStruct [.const 11, .const 22]) : Prog (RiscV.Word 8))) =
      some (.normal { crepeFullRecordAssignState with
        locals := updateCrepLocal
          (updateCrepLocal crepeFullRecordAssignState.locals 1 11) 2 22 }) ∧
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun name => if name == "pair" then
          some (.rStruct [.word 0, .word 1]) else none)
        (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.assign .local "pair"
          (.rStruct [.const 11, .const 22]) : Prog (RiscV.Word 8)) =
      some (updatePanValueMap
        (fun name => if name == "pair" then
          some (.rStruct [.word 0, .word 1]) else none)
        "pair" (.rStruct [.word 11, .word 22]),
        (fun _ => none), (fun _ => none), []) := by
  have h := compile_full_pan_value_local_assign_record_state_full_correct
    crepeFullRecordAssignContext ([] : StructContext)
    (fun name => if name == "pair" then
      some (.rStruct [.word 0, .word 1]) else none)
    (fun _ => none) (fun _ => none)
    crepeFullRecordAssignState (fun _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 11 22 0 1 "pair" 1 2
    (by simp [crepeFullRecordAssignContext, lookupInfo])
    (by simp)
    (by simp)
    (by simp [crepeFullRecordAssignState])
    (by simp [crepeFullRecordAssignState])
  exact ⟨h.2, h.1⟩

theorem compile_full_pan_value_dec_word_return_state_full_regression :
    evalCrepFullProgStateFull [] (fun _ _ => none) (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 10 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.dec "x" .one (.const 7)
            (.return (.var .local "x")) : Prog (RiscV.Word 8))) =
      some (.returned
        { crepeFullRaiseState with
            locals := restoreCrepLocal
              (updateCrepLocal crepeFullRaiseState.locals 1 7) 1 none }
        [7]) ∧
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ => none)
        (.dec "x" .one (.const 7)
          (.return (.var .local "x")) : Prog (RiscV.Word 8)) =
      some (restorePanValueLocal (fun _ => none) "x" none,
        (fun _ => none), (fun _ => none), [.word 7]) := by
  exact compile_full_pan_value_dec_word_return_state_full
    crepeFullRaiseContext ([] : StructContext)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState (fun _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 7 "x"

theorem compile_full_pan_value_dec_two_word_record_return_state_full_regression :
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 10 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.dec "pair" (.comb [.one, .one])
            (.rStruct [.const 11, .const 22])
            (.return (.var .local "pair")) : Prog (RiscV.Word 8))) =
      some (.returned crepeFullRaiseState [11, 22]) ∧
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ => none)
        (.dec "pair" (.comb [.one, .one])
          (.rStruct [.const 11, .const 22])
          (.return (.var .local "pair")) : Prog (RiscV.Word 8)) =
      some (restorePanValueLocal (fun _ => none) "pair" none,
        (fun _ => none), (fun _ => none),
        [.rStruct [.word 11, .word 22]]) := by
  exact compile_full_pan_value_dec_two_word_record_return_state_full
    crepeFullRaiseContext ([] : StructContext)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState (fun _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 11 22 "pair"

theorem compile_full_pan_value_store_word_state_full_regression :
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 20 crepeFullLoadState
        (compileProg crepeFullLoadContext
          (.store (.const 7) (.const 99) : Prog (RiscV.Word 8))) =
      some (.normal { crepeFullLoadState with
        memory := updateMemory crepeFullLoadState.memory 7 99 }) ∧
    evalPanValueProgWithPrimitiveFull
        ([] : StructContext) 0 100 1
        (fun name => if name == "x" then some (.word 0) else none)
        (fun _ => none)
        (fun address => if address == 7 then some (.word 42) else none)
        (fun _ _ => none)
        (.store (.const 7) (.const 99) : Prog (RiscV.Word 8)) =
      some ((fun name => if name == "x" then some (.word 0) else none),
        (fun _ => none),
        updatePanValueMemory
          (fun address => if address == 7 then some (.word 42) else none)
          7 (.word 99), []) := by
  exact compile_full_pan_value_store_word_state_full_correct
    crepeFullLoadContext ([] : StructContext)
    (fun name => if name == "x" then some (.word 0) else none)
    (fun _ => none)
    (fun address => if address == 7 then some (.word 42) else none)
    crepeFullLoadState (fun _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 7 99

theorem compile_full_pan_value_raise_word_state_full_correct_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 3
        (fun _ => none) (fun _ => none)
        (fun _ => none)
        (.raise "E" (.const 7) : Prog (RiscV.Word 8)) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" (.word 7)) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none) (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 10 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.raise "E" (.const 7) : Prog (RiscV.Word 8))) =
      some (.raised
        { crepeFullRaiseState with
            globals := updateMemory crepeFullRaiseState.globals 0 7 } 9) := by
  exact compile_full_pan_value_raise_word_state_full_correct crepeFullRaiseContext
    ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 7 "E" 9 (by simp [crepeFullRaiseContext, lookupInfo])

theorem compile_full_pan_value_raise_two_word_state_full_correct_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 5
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" (.rStruct [.const 11, .const 22]) : Prog (RiscV.Word 8)) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" (.rStruct [.word 11, .word 22])) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 15 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.raise "E" (.rStruct [.const 11, .const 22]) : Prog (RiscV.Word 8))) =
      some (.raised
        { crepeFullRaiseState with
            globals := updateMemory
              (updateMemory crepeFullRaiseState.globals 0 11) 1 22 } 9) := by
  exact compile_full_pan_value_raise_two_word_state_full_correct
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ => none) (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 11 22 "E" 9 (by simp [crepeFullRaiseContext, lookupInfo]) (by
      simp [crepeFullRaiseContext])

theorem compile_full_pan_value_seq_raise_compose_state_full_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 11
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.seq (.raise "E" (.const 7)) (.skip) : Prog (RiscV.Word 8)) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" (.word 7)) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 11 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.seq (.raise "E" (.const 7)) (.skip) : Prog (RiscV.Word 8))) =
      some (.raised
        { crepeFullRaiseState with
            globals := updateMemory crepeFullRaiseState.globals 0 7 } 9) := by
  have hraise := compile_full_pan_value_raise_word_state_full_correct
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ => none) (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 7 "E" 9 (by simp [crepeFullRaiseContext, lookupInfo])
  have hsourceFirst :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 10
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" (.const 7) : Prog (RiscV.Word 8)) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" (.word 7)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp]
  exact compile_full_pan_value_seq_raise_compose_state_full
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState
    ({ crepeFullRaiseState with
        globals := updateMemory crepeFullRaiseState.globals 0 7 })
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 9
    (.raise "E" (.const 7)) (.skip)
    (compileProg crepeFullRaiseContext (.raise "E" (.const 7)))
    (compileProg crepeFullRaiseContext (.skip)) "E" (.word 7) 9
    rfl (by simp [compileProg]) hsourceFirst hraise.2

theorem compile_full_pan_value_seq_break_compose_state_full_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 3
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.seq (.break) (.skip) : Prog (RiscV.Word 8)) =
      some (.broke (fun _ => none) (fun _ => none) (fun _ => none)) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 3 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.seq (.break) (.skip) : Prog (RiscV.Word 8))) =
      some (.broke crepeFullRaiseState 0) := by
  have hsourceFirst :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 2
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.break : Prog (RiscV.Word 8)) =
      some (.broke (fun _ => none) (fun _ => none) (fun _ => none)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi]
  have hcrepFirst :
      evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 2 crepeFullRaiseState
        (compileProg crepeFullRaiseContext (.break)) =
      some (.broke crepeFullRaiseState 0) := by
    simp [compileProg, evalCrepFullProgStateFull]
  exact compile_full_pan_value_seq_break_compose_state_full
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState crepeFullRaiseState
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 1 (.break) (.skip)
    (compileProg crepeFullRaiseContext (.break))
    (compileProg crepeFullRaiseContext (.skip)) rfl
    (by simp [compileProg]) hsourceFirst hcrepFirst

theorem compile_full_pan_value_seq_continue_compose_state_full_regression :
    evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 3
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.seq (.continue) (.skip) : Prog (RiscV.Word 8)) =
      some (.continued (fun _ => none) (fun _ => none) (fun _ => none)) ∧
    evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 3 crepeFullRaiseState
        (compileProg crepeFullRaiseContext
          (.seq (.continue) (.skip) : Prog (RiscV.Word 8))) =
      some (.continued crepeFullRaiseState 0) := by
  have hsourceFirst :
      evalPanValueProgWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 2
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.continue : Prog (RiscV.Word 8)) =
      some (.continued (fun _ => none) (fun _ => none) (fun _ => none)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfi]
  have hcrepFirst :
      evalCrepFullProgStateFull [] (fun _ _ => none)
        (noCrepFfi (RiscV.Word 8))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
        0 100 2 crepeFullRaiseState
        (compileProg crepeFullRaiseContext (.continue)) =
      some (.continued crepeFullRaiseState 0) := by
    simp [compileProg, evalCrepFullProgStateFull]
  exact compile_full_pan_value_seq_continue_compose_state_full
    crepeFullRaiseContext ([] : StructContext) [] []
    (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ => none) (fun _ => none)
    crepeFullRaiseState crepeFullRaiseState
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8))
    0 100 1 1 (.continue) (.skip)
    (compileProg crepeFullRaiseContext (.continue))
    (compileProg crepeFullRaiseContext (.skip)) rfl
    (by simp [compileProg]) hsourceFirst hcrepFirst

/-! The complete-word shared-store theorem has a concrete Cake/Crep oracle:
    both evaluators write the same word at address 7, while the target path
    goes through the compiled temporary and stateful shared-memory handler. -/
def crepeFullStoreState : CrepState (RiscV.Word 8) :=
  { locals := fun name => if name == 1 then some 99 else none
    memory := fun _ => none
    globals := fun _ => none }

def crepeFullStoreProgram : Prog (RiscV.Word 8) :=
  .shMemStore .opW (.const 7) (.const 42)

def crepeFullStoreContext : CompileContext (RiscV.Word 8) :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

#guard (evalPanValueProgWithPrimitiveFull
    ([] : StructContext) 0 100 1 (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ _ => none) crepeFullStoreProgram).map
      (fun result => match result.2.2.1 7 with
      | some (.word value) => value == 42
      | _ => false) ==
    some true

#guard (evalCrepFullProgStateFull [] (fun _ _ => none)
    (noCrepFfi (RiscV.Word 8))
    (defaultCrepSharedMemHandler : CrepSharedMemHandler (RiscV.Word 8)) 0 100 10
    crepeFullStoreState
    (compileProg crepeFullStoreContext crepeFullStoreProgram)).map
      (fun result => match result with
      | .normal state => match state.memory 7 with
        | some value => value == 42
        | none => false
      | _ => false) == some true

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.loadGlob 200) = some 42

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.loadGlob 200) !=
  evalCrepFullExpState crepeGlobalSemanticsState 0 100
    (CrepExp.load (CrepExp.const 200))

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.load (CrepExp.const 200)) = some 7

#guard evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1
    crepeGlobalSemanticsState
    (compileProg crepeGlobalSkipContext (.skip : Prog Nat)) = some []

#guard evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 20
    crepeGlobalSemanticsState
    (compileProg crepeGlobalSkipContext
      (.ite (.const 0) (.return (.const 7)) (.return (.const 9)) : Prog Nat)) =
      some [9]

def crepeGlobalStoreLoadProgram : CrepProg Nat :=
  .seq
    (.storeGlob 200 (.const 42))
    (.return [.loadGlob 200])

#guard evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
    crepeGlobalSemanticsState crepeGlobalStoreLoadProgram = some [42]

#guard evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
    { crepeGlobalSemanticsState with globals := fun _ => none }
    (.return [.loadGlob 200]) = none

def crepeGlobalCallee : CompiledFunction Nat :=
  { name := "setGlobal"
    params := []
    body := .seq (.storeGlob 200 (.const 42)) (.return [])
    returnShape := .comb [] }

def crepeGlobalCallProgram : CrepProg Nat :=
  .seq (.call (some ([], none)) "setGlobal" []) (.return [.loadGlob 200])

#guard evalCrepFullResultState [crepeGlobalCallee] (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100 20 crepeGlobalSemanticsState crepeGlobalCallProgram = some [42]

def crepeGlobalRaiseContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 1 }

#guard (evalCrepFullProgState [] (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 20
    crepeGlobalSemanticsState
    (compileProg crepeGlobalRaiseContext (.raise "E" (.const 42)))).map
      (crepControlGlobalAt 0) = some (some 42)

end Flapjack
