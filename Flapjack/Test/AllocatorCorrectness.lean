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
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory) :
    evalWordExp source
        (.shift .ror (.op .add [.var 2, .var 3]) (.const 4)) =
      evalWordExp target
        (wordApplyColourExp colour
          (.shift .ror (.op .add [.var 2, .var 3]) (.const 4))) := by
  apply evalWordExp_applyColour
  · exact hregister
  · exact hmemory

example [NeZero 64]
    (source target : State 64) (colour : Nat → Nat)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (colour name)
        pure (readRegister target register))) :
    evalWordCondition source .equal 2 (.reg 3) =
      evalWordCondition target .equal (colour 2)
        (wordApplyColourRegImm colour (.reg 3)) := by
  apply evalWordCondition_applyColour
  exact hregister

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

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.return 0 [2, 3])).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.return 0 ([2, 3].map (wordSsaRead ssa)))).map
        wordControlResultValues := by
  exact evalWordReturn_ssaRename ssa source target hregister 3 0 [2, 3]

example [NeZero 64]
    (source target : State 64) (ssa : WordSsaState)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register))) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 source
        (.raise 2)).map wordControlResultException =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) 4 target
        (.raise (wordSsaRead ssa 2))).map wordControlResultException := by
  exact evalWordRaise_ssaRename ssa source target hregister 3 2

end Flapjack
