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
