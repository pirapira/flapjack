import Flapjack.CorrectnessPrimitive
import Flapjack.Test.LoopCalls

/-!
Concrete regression for the first Loop-to-Word primitive correctness bridge.
The source locals and target registers intentionally use the same small
allocation, making the required non-alias contracts executable.
-/

namespace Flapjack

def primitiveLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := []
    functions := []
    maxVar := 0
    target := .rv64i }

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result =>
          ((loopResultState result).locals 5,
            (loopResultState result).locals 6)) =
      (RiscV.evalWordProg loopAddCarryMachineState
        (loopToWordProg ({ vars := [] } : WordContext)
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result =>
          (some (RiscV.readRegister result 5),
            some (RiscV.readRegister result 6))) := by
  apply loopToWord_primitive_addCarry_agreement
    ({ vars := [] } : WordContext) loopAddCarryState loopAddCarryMachineState
    5 6 2 3 4 5 6 2 3 4
    (BitVec.ofNat 64 1) (BitVec.ofNat 64 2) (BitVec.ofNat 64 0)
  all_goals native_decide

example :
    (evalCrepStateProgWithPrimitive RiscV.loopPrimitiveHandler
      (fun name => if name == 2 then some (BitVec.ofNat 64 1)
        else if name == 3 then some (BitVec.ofNat 64 2)
        else if name == 4 then some (BitVec.ofNat 64 0)
        else none)
      (.primitive [5, 6] .addCarry [2, 3, 4])).map id =
      (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
        (loopStateOfCrepLocals (fun name => if name == 2 then
          some (BitVec.ofNat 64 1)
        else if name == 3 then some (BitVec.ofNat 64 2)
        else if name == 4 then some (BitVec.ofNat 64 0)
        else none))
        (loopCompileProg primitiveLoopContext []
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result =>
          ((loopResultState result).locals, loopResultValues result)) := by
  apply crepToLoop_primitive_agreement

end Flapjack
