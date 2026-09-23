import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.PanSem.Primop

/-!
The AddCarry primitive case needed by HOL `pc_compile_correct`.
-/

namespace Flapjack

/-- HOL `pan_primop_crep_primop`: a successful source primitive result
    flattens to exactly the result of the Crep primitive on flattened inputs.
    Both sides retain HOL's `word_lab` wrapper at this theorem boundary. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pan_primop_crep_primop"]
theorem panPrimopCrepPrimop {width : Nat} [NeZero width]
    (operator : PrimOp) (values : List (PanValue (BitVec width)))
    (value : PanValue (BitVec width))
    (hprimitive : panPrimopHOL operator values = some value) :
    crepPrimopHOL operator (values.flatMap panSemFlattenHOL) =
      some (panSemFlattenHOL value) := by
  cases operator
  cases values with
  | nil => simp [panPrimopHOL] at hprimitive
  | cons first rest =>
      cases rest with
      | nil => simp [panPrimopHOL] at hprimitive
      | cons second rest =>
          cases rest with
          | nil => simp [panPrimopHOL] at hprimitive
          | cons third rest =>
              cases rest with
              | cons _ _ => simp [panPrimopHOL] at hprimitive
              | nil =>
                  cases first <;> cases second <;> cases third <;>
                    simp [panPrimopHOL] at hprimitive
                  rw [← hprimitive]
                  simp [crepPrimopHOL, panSemFlattenHOL,
                    panSemFlattenValuesHOL]

end Flapjack
