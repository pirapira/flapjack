import Flapjack.CrepeSemantics

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

theorem crepe_global_load_uses_global_store :
    evalCrepFullExpState crepeGlobalSemanticsState 0 100
      (CrepExp.loadGlob 200) = some 42 := by
  native_decide

theorem crepe_global_load_does_not_alias_memory :
    evalCrepFullExpState crepeGlobalSemanticsState 0 100
      (CrepExp.loadGlob 200) ≠
      evalCrepFullExpState crepeGlobalSemanticsState 0 100
        (CrepExp.load (CrepExp.const 200)) := by
  native_decide

theorem crepe_memory_load_remains_in_memory :
    evalCrepFullExpState crepeGlobalSemanticsState 0 100
      (CrepExp.load (CrepExp.const 200)) = some 7 := by
  native_decide

def crepeGlobalStoreLoadProgram : CrepProg Nat :=
  .seq
    (.storeGlob 200 (.const 42))
    (.return [.loadGlob 200])

theorem crepe_global_store_load_program :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
      (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
      crepeGlobalSemanticsState
      crepeGlobalStoreLoadProgram = some [42] := by
  native_decide

theorem crepe_global_load_missing_fails :
    evalCrepFullResultState [] (fun _ _ => none) (noCrepFfi Nat)
      (defaultCrepSharedMemHandler : CrepSharedMemHandler Nat) 0 100 10
      { crepeGlobalSemanticsState with globals := fun _ => none }
      (.return [.loadGlob 200]) = none := by
  native_decide

end Flapjack
