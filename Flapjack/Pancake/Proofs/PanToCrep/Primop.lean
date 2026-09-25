import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.PanSem.Primop

/-!
The AddCarry primitive case needed by HOL `pc_compile_correct`.
-/

namespace Flapjack

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `pan_primop_crep_primop` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096-1099`):
    `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`.
    A successful source primitive result flattens to exactly the result of the
    Crep primitive on flattened inputs; both sides retain HOL's `word_lab`
    wrapper at this theorem boundary. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed 2026-09-25:
-- statement shape is mirrored clause-for-clause: the single `SOME` implication,
-- the `FLAT (MAP flatten vs)` argument, and the `flatten value` result are all
-- present (`List.flatMap panSemFlattenHOL values`, `panSemFlattenHOL value`).
-- Carrier mismatch: the Lean statement quantifies the production `PanValue`
-- carrier, whose `nStruct` names are `FieldName` = `String` and whose word
-- payload is `BitVec width` with the executable `[NeZero width]` argument,
-- while HOL `panSem$v` uses `fldname` = `mlstring` and `fldname # value` over a
-- positive-width `'a word` without any typeclass side condition. The `flatten`
-- result is a `word_lab list` on both sides (`PanWordLab`).
-- `names_as_string` cannot authorize this: the only identifiers live inside a
-- `PanValue` datatype payload, not at the theorem boundary, and the conclusion
-- is a `SOME`-equation over flattened values, so no `NameRanged` byte witness
-- can be stated. Its dependencies `panPrimopHOL`/`panSemFlattenHOL` had their
-- tags withdrawn for the same reason (`flapjack-0lj.3`).
-- Classified `documented_mismatch` in `docs/HOL-THEOREM-MAP.json`
-- (reviewer flapjack-deepseek-two); the declaration is intentionally untagged.
-- Oracle evidence: `scripts/hol-probes/pan_crep_primop_probe.out` rows
-- `pan_valid=SOME [8;0]`, `pan_overflow=SOME [0;1]`, `pan_invalid=NONE`,
-- `crep_valid=SOME [8;0]`, `crep_overflow=SOME [0;1]`, `crep_invalid=NONE`,
-- `crep_zero_args=NONE`, `crep_four_args=NONE`, `crep_nonzero_carry=SOME [0;1]`,
-- reproduced by `Flapjack/Test/PanCrepPrimopParity.lean` (guards plus the
-- kernel-checked `bridgeFixture` applying this theorem).
-- Exact MlString carrier tracked by `flapjack-pxn.18.3.5.8` / `flapjack-0lj`.
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
