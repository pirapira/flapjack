import Flapjack.RiscV.AllocatorCorrectness

namespace Flapjack

open RiscV

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory) :
    evalWordExp source
        (.shift .ror (.op .add [.var 2, .var 3]) (.const 4)) =
      evalWordExp target
        (wordSsaRenameExp ssa
          (.shift .ror (.op .add [.var 2, .var 3]) (.const 4))) := by
  apply evalWordExp_ssaRename
  · exact hregister
  · exact hmemory

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    evalWordCondition source .equal 2 (.reg 3) =
      evalWordCondition target .equal (wordSsaRead ssa 2)
        (wordSsaRenameRegImm ssa (.reg 3)) := by
  apply evalWordCondition_ssaRename
  exact hregister

end Flapjack
