import Flapjack.Test.SourceToLoop

/-!
Source-to-Loop memory regression.

This exercises the real Pancake-to-Crepe store lowering, temporary address and
value materialization, Crepe-to-Loop memory updates, and the subsequent load
in the returned expression.
-/

namespace Flapjack

def sourceToLoopMemoryState : LoopState (RiscV.Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopMemoryProgram : Prog (RiscV.Word 64) :=
  .seq
    (.store (.const (BitVec.ofNat 64 100))
      (.const (BitVec.ofNat 64 42)))
    (.return (.load .one (.const (BitVec.ofNat 64 100))))

#guard
    (evalLoopProg 40 sourceToLoopMemoryState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopMemoryProgram))).map
        loopResultValues =
      evalPanMemResult (fun _ => none) (fun _ => none)
        sourceToLoopMemoryProgram

#guard
    (evalLoopProg 40 sourceToLoopMemoryState
      (loopCompileProg sourceToLoopLoopContext []
        (compileProg sourceToLoopCompileContext sourceToLoopMemoryProgram))).map
        loopResultValues = some [BitVec.ofNat 64 42]

end Flapjack
