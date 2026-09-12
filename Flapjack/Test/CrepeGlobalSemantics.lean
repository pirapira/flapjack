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

theorem compile_full_skip_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext (.skip : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.skip : Prog Nat) := by
  exact compile_full_skip_state_correct crepeGlobalSkipContext
    (fun _ => none) crepeGlobalSemanticsState (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100

theorem compile_full_return_const_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.return (.const 7) : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.return (.const 7) : Prog Nat) := by
  exact compile_full_return_const_state_correct crepeGlobalSkipContext
    (fun _ => none) crepeGlobalSemanticsState (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100 7

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
