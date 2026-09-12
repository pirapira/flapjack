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

def crepeGlobalLocalContext : CompileContext Nat :=
  { vars := [("x", (.one, [1]))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 1 }

def crepeGlobalBoundLocalState : CrepState Nat :=
  { locals := fun slot => if slot = 1 then some 7 else none
    memory := crepeGlobalSemanticsState.memory
    globals := crepeGlobalSemanticsState.globals }

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

theorem compile_full_add_const_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.return (.op .add [.const 3, .const 4]) : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.return (.op .add [.const 3, .const 4]) : Prog Nat) := by
  exact compile_full_add_const_state_correct crepeGlobalSkipContext
    (fun _ => none) crepeGlobalSemanticsState (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100 3 4

theorem compile_full_store_load_const_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 20
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.seq (.store (.const 200) (.const 42))
            (.return (.load .one (.const 200))) : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.seq (.store (.const 200) (.const 42))
          (.return (.load .one (.const 200))) : Prog Nat) := by
  exact compile_full_store_load_const_state_correct crepeGlobalSkipContext
    (fun _ => none) crepeGlobalSemanticsState (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100 200 42

theorem compile_full_ite_const_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 20
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.ite (.const 1) (.return (.const 7)) (.return (.const 9)) : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.ite (.const 1) (.return (.const 7)) (.return (.const 9)) : Prog Nat) := by
  exact compile_full_ite_const_state_correct crepeGlobalSkipContext
    (fun _ => none) crepeGlobalSemanticsState (fun _ _ => none)
    (noCrepFfi Nat) (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat)
    0 100 1 7 9

theorem compile_full_local_assign_return_const_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 20
        crepeGlobalSemanticsState
        (compileProg crepeGlobalLocalContext
          (.seq (.assign .local "x" (.const 7))
            (.return (.var .local "x")) : Prog Nat)) =
      evalPanMemResult (fun _ => none) crepeGlobalSemanticsState.memory
        (.seq (.assign .local "x" (.const 7))
          (.return (.var .local "x")) : Prog Nat) := by
  exact compile_full_local_assign_return_const_state_correct
    crepeGlobalLocalContext (fun _ => none) crepeGlobalSemanticsState
    (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 "x" 1 7
    (by simp [crepeGlobalLocalContext, lookupInfo])

theorem compile_full_local_return_state_correct_regression :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 5
        crepeGlobalBoundLocalState
        (compileProg crepeGlobalLocalContext
          (.return (.var .local "x") : Prog Nat)) =
      evalPanMemResult (fun name => if name == "x" then some 7 else none)
        crepeGlobalBoundLocalState.memory
        (.return (.var .local "x") : Prog Nat) := by
  exact compile_full_local_return_state_correct crepeGlobalLocalContext
    (fun name => if name == "x" then some 7 else none)
    crepeGlobalBoundLocalState (fun _ _ => none) (noCrepFfi Nat)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 "x" 1
    (by simp [crepeGlobalLocalContext, lookupInfo])
    (by simp [crepeGlobalBoundLocalState])

theorem compile_full_extCall_const_noop_state_correct_regression :
    evalCrepFullProgState [] (fun _ _ => none)
        (fun _ _ _ _ _ sourceState => some (.returned sourceState))
        (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 30
        crepeGlobalSemanticsState
        (compileProg crepeGlobalSkipContext
          (.extCall "noop" (.const 1) (.const 2) (.const 3) (.const 4) :
            Prog Nat)) = some (.normal crepeGlobalSemanticsState) := by
  exact compile_full_extCall_const_noop_state_correct crepeGlobalSkipContext
    crepeGlobalSemanticsState (fun _ _ => none)
    (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 1 2 3 4
    "noop"

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
