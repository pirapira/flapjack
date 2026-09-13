import Flapjack.RiscV.Model

/-!
# RISC-V checked-access trap contracts

These lemmas expose the failure side of the option-valued execution boundary.
The definitions follow the compact RISC-V model, whose `accessAligned`
classifier is the Lean counterpart of the aligned-access checks in the HOL
model. Keeping the trap contracts separate makes them usable by target
correctness proofs without unfolding the whole instruction transition.
-/

namespace Flapjack.RiscV

theorem executeTrap_store32_misaligned (state : State width)
    (address : Fin 32)
    (h : aligned (readRegister state address) 4 = false) :
    executeTrap state (.store32 0 address) = some .storeAmoFault := by
  simp [executeTrap, accessAligned, h]

theorem executeChecked_store32_misaligned (state : State width)
    (source address : Fin 32)
    (h : aligned (readRegister state address) 4 = false) :
    executeChecked state (.store32 source address) = none := by
  simp [executeChecked, executeTrap, accessAligned, h]

theorem executeTrap_loadWord_misaligned [NeZero width]
    (state : State width) (address : Fin 32)
    (h : aligned (readRegister state address) (width / 8) = false) :
    executeTrap state (.loadWord 0 address) = some .loadFault := by
  simp [executeTrap, accessAligned, h]

theorem executeChecked_loadWord_misaligned [NeZero width]
    (state : State width) (destination address : Fin 32)
    (h : aligned (readRegister state address) (width / 8) = false) :
    executeChecked state (.loadWord destination address) = none := by
  simp [executeChecked, executeTrap, accessAligned, h]

theorem executeChecked_storeWord_misaligned [NeZero width]
    (state : State width) (source address : Fin 32)
    (h : aligned (readRegister state address) (width / 8) = false) :
    executeChecked state (.storeWord source address) = none := by
  simp [executeChecked, executeTrap, accessAligned, h]

end Flapjack.RiscV
