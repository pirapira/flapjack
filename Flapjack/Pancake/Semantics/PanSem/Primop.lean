import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.HolRef
import Flapjack.PanValueFlatten

/-!
HOL `panSemScript.sml` word-labeled flattening and AddCarry primitive. The
existing executable `panValueFlatten` erases the one-constructor `word_lab`
wrapper; these definitions retain it at the theorem-facing boundary.
-/

namespace Flapjack

mutual
  /-- FLAPJACK-SPECIFIC (not a statement-exact HOL port), matching the shape of
      HOL `panSem$flatten` structurally but over the production `PanValue`
      carrier: HOL's `flatten` is over `v`, whose `NStruct` name/fields are
      `mlstring` (`stcname`/`fldname`) and whose `Val` holds `'a word_lab`,
      whereas `PanValue.nStruct` uses `StructName`/`FieldName` (`String`) and
      `PanValue.word` holds `α` directly. Tracked by `flapjack-0lj`; the exact
      MlString-carrier port is `flapjack-0lj.3` (see
      `docs/PANSEM-CARRIER-AUDIT.md`). -/
  def panSemFlattenHOL : PanValue α → List (PanWordLab α)
    | .word value => [.word value]
    | .rStruct values => panSemFlattenValuesHOL values
    | .nStruct _ fields => panSemFlattenFieldsHOL fields
  termination_by value => sizeOf value
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- Flapjack-only list traversal corresponding to HOL `FLAT (MAP flatten
      vs)` in the record case of `flatten_def`; HOL has no separate name. -/
  def panSemFlattenValuesHOL : List (PanValue α) → List (PanWordLab α)
    | [] => []
    | value :: values => panSemFlattenHOL value ++ panSemFlattenValuesHOL values
  termination_by values => sizeOf values
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- Flapjack-only traversal corresponding to HOL's `MAP SND` of named
      record fields before flattening; HOL has no separate declaration. -/
  def panSemFlattenFieldsHOL :
      List (FieldName × PanValue α) → List (PanWordLab α)
    | [] => []
    | (_, value) :: fields =>
        panSemFlattenHOL value ++ panSemFlattenFieldsHOL fields
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port), matching the shape of
    HOL `panSem$pan_primop` clause-by-clause but over the production `PanValue`
    carrier: HOL quantifies over `v` (whose `NStruct` names/fields are
    `mlstring` and whose `Val` holds `'a word_lab`), whereas `PanValue` uses
    `String` names and stores `α` in `.word`. Tracked by `flapjack-0lj`; the
    exact MlString-carrier port is `flapjack-0lj.3` (see
    `docs/PANSEM-CARRIER-AUDIT.md`). -/
def panPrimopHOL {width : Nat} [NeZero width] :
    PrimOp → List (PanValue (BitVec width)) →
      Option (PanValue (BitVec width))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some (.rStruct [.word result, .word overflow])
  | _, _ => none

end Flapjack
