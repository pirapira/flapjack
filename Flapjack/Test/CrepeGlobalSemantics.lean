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

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.loadGlob 200) = some 42

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.loadGlob 200) !=
  evalCrepFullExpState crepeGlobalSemanticsState 0 100
    (CrepExp.load (CrepExp.const 200))

#guard evalCrepFullExpState crepeGlobalSemanticsState 0 100
  (CrepExp.load (CrepExp.const 200)) = some 7

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

end Flapjack
