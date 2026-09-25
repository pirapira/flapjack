import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.PanSem.Primop

/-!
The AddCarry primitive case needed by HOL `pc_compile_correct`.
-/

namespace Flapjack

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `pan_primop_crep_primop`: a successful source primitive result
    flattens to exactly the result of the Crep primitive on flattened inputs.
    Both sides retain HOL's `word_lab` wrapper at this theorem boundary. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): stated over the production
-- `PanValue` carrier, whose `nStruct` names are `FieldName` = `String`, while
-- HOL `panSem$v` uses `fldname` = `mlstring`; its dependencies
-- `panPrimopHOL`/`panSemFlattenHOL` had their tags withdrawn for the same
-- reason (`flapjack-0lj.3`). The exact MlString identifier carrier is tracked
-- by `flapjack-pxn.18.3.5.8` / `flapjack-0lj`.
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
