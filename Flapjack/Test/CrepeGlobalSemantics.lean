import Flapjack.CrepeSemantics
import Flapjack.Compile
import Flapjack.CrepeCorrectness
import Flapjack.CrepToLoopCorrectness

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

/-! The full Cake exception evaluator and full Crep evaluator agree on a
    closed raised word, including the global payload spill and exception-code
    lookup. -/
def crepeFullRaiseContext : CompileContext (RiscV.Word 8) :=
  { vars := [], functions := [], exceptions := [("E", 9)], maxVar := 0,
    bytesInWord := 1 }

def crepeFullRaiseState : CrepState (RiscV.Word 8) :=
  { locals := fun _ => none, memory := fun _ => none, globals := fun _ => none }

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

theorem compile_full_pan_value_raise_word_state_full_correct_regression :
    evalPanValueProgWithPrimitiveCallsAndFfiFull
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
    evalPanValueProgWithPrimitiveCallsAndFfiFull
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
    evalPanValueProgWithPrimitiveCallsAndFfiFull
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
      evalPanValueProgWithPrimitiveCallsAndFfiFull
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 10
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.raise "E" (.const 7) : Prog (RiscV.Word 8)) =
      some (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        "E" (.word 7)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfiFull, evalPanValueExpFull]
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
    evalPanValueProgWithPrimitiveCallsAndFfiFull
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
      evalPanValueProgWithPrimitiveCallsAndFfiFull
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 2
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.break : Prog (RiscV.Word 8)) =
      some (.broke (fun _ => none) (fun _ => none) (fun _ => none)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfiFull]
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
    evalPanValueProgWithPrimitiveCallsAndFfiFull
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
      evalPanValueProgWithPrimitiveCallsAndFfiFull
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        ([] : StructContext) [] 0 100 1 2
        (fun _ => none) (fun _ => none) (fun _ => none)
        (.continue : Prog (RiscV.Word 8)) =
      some (.continued (fun _ => none) (fun _ => none) (fun _ => none)) := by
    simp [evalPanValueProgWithPrimitiveCallsAndFfiFull]
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
