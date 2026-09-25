/-
EXACT CARRIER EXPRESSIONS (flapjack-pxn.18.3.6.9.15).

Direct port of HOL `eval_def` (`cakeml/pancake/semantics/panSemScript.sml:209-283`,
identical to `pan_itreeSemScript.sml:79`) over the exact `mlstring`-keyed
`PanSemStateExact` carrier, the exact `ExpHOL` syntax, and the exact `ValueHOL`
values.  Every lookup is `=`-keyed (`MlString` derives `DecidableEq`); the shape
comparisons go through `shapeEqHOL` (whose `= true` reading is proved exact in
`IsValidValueExact.lean`); loads reuse the tagged exact `memLoadHOLExact`
(`mem_load_def`), `panMemLoad32HOL` (`mem_load_32_def`), `panMemLoadByteHOL`
(`mem_load_byte_def`); the wording operations reuse the tagged exact `wordOpHOL`
(`word_op_def`), `panOpHOL` (`pan_op_def`), `wordCmpHOL` (`word_cmp_def`) and
`wordShiftHOL` (`word_sh_def`).

The evaluator itself is UNTAGGED: it is the exact-carrier prerequisite for the
recursive `evaluate` dispatcher and is only statement-exact once the whole
`evaluate_def` shape (monad, clock, exception state) is assembled.  Direct
original-HOL rows are in `scripts/hol-probes/pan_eval_probe.out` and are
reproduced by `Flapjack/Test/PanSemEvalExactParity.lean`.
-/
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact
import Flapjack.Pancake.Semantics.PanSemStateEval

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ExpHOL)
open Flapjack.Pancake.PanLang (isWfShapeExactHOL structContextLookupHOL)

/-- HOL `isWord` over the exact value carrier. -/
def valueIsWord {width : Nat} [NeZero width] : ValueHOL width → Bool
  | .val (.word _) => true
  | _ => false

/-- HOL `theWord` over the exact value carrier (totalized for the guard). -/
def valueWord {width : Nat} [NeZero width] : ValueHOL width → BitVec width
  | .val (.word value) => value
  | _ => 0

/-- HOL `ALOOKUP` for named-struct field lookup over exact values. -/
def lookupFieldHOL {width : Nat} [NeZero width] (name : MlS) :
    List (MlS × ValueHOL width) → Option (ValueHOL width)
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = name then some value else lookupFieldHOL name rest

/-! ## The exact `eval_def` evaluator -/

mutual
  /-- Untagged exact carrier port of HOL `eval`. -/
  def evalHOLExact {width : Nat} {σ : Type} [NeZero width]
      (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
      ExpHOL width → Option (ValueHOL width)
    | .const value => some (.val (.word value))
    | .var kind name =>
        match kind with
        | .local => state.locals name
        | .global => state.globals name
    | .rstruct fields => (evalListHOLExact state fields).map ValueHOL.rStruct
    | .rfield index value =>
        match evalHOLExact state value with
        | some (.rStruct values) => values[index]?
        | _ => none
    | .nstruct name fields =>
        match structContextLookupHOL name state.structs with
        | none => none
        | some info =>
            if info.fields.map Prod.fst = fields.map Prod.fst then
              match evalListFieldsHOLExact state fields with
              | none => none
              | some fieldValues =>
                  if ((info.fields.map Prod.snd).zip
                      (fieldValues.map (fun pair => shapeOfHOLExact pair.2))).all
                      (fun pair => shapeEqHOL pair.1 pair.2) then
                    some (.nStruct name fieldValues)
                  else none
            else none
    | .nfield name value =>
        match evalHOLExact state value with
        | some (.nStruct structName values) =>
            if (structContextLookupHOL structName state.structs).isSome then
              lookupFieldHOL name values
            else none
        | _ => none
    | .load shape address =>
        if isWfShapeExactHOL state.structs shape then
          match evalHOLExact state address with
          | some (.val (.word word)) =>
              memLoadHOLExact shape word state.memaddrs state.memory state.structs
          | _ => none
        else none
    | .load32 address =>
        match evalHOLExact state address with
        | some (.val (.word word)) =>
            (panMemLoad32HOL state.memory state.memaddrs state.be word).map
              (fun value => .val (.word (BitVec.ofNat width value.toNat)))
        | _ => none
    | .loadByte address =>
        match evalHOLExact state address with
        | some (.val (.word word)) =>
            (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
              (fun value => .val (.word (BitVec.ofNat width value.toNat)))
        | _ => none
    | .op operator arguments =>
        match evalListHOLExact state arguments with
        | some values =>
            if values.all valueIsWord then
              (wordOpHOL operator (values.map valueWord)).map
                (fun word => .val (.word word))
            else none
        | none => none
    | .panop operator arguments =>
        match evalListHOLExact state arguments with
        | some values =>
            if values.all valueIsWord then
              (panOpHOL operator (values.map valueWord)).map
                (fun word => .val (.word word))
            else none
        | none => none
    | .cmp operator left right =>
        match evalHOLExact state left, evalHOLExact state right with
        | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
            some (.val (.word
              (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL operator leftWord rightWord
               then 1 else 0)))
        | _, _ => none
    | .shift operator left right =>
        match evalHOLExact state left, evalHOLExact state right with
        | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
            (wordShiftHOL operator leftWord rightWord.toNat).map
              (fun word => .val (.word word))
        | _, _ => none
    | .baseAddr => some (.val (.word state.baseAddr))
    | .topAddr => some (.val (.word state.topAddr))
    | .bytesInWord => some (.val (.word (bytesInWordHOL width)))

  /-- Untagged exact port of the `OPT_MMAP eval` list step. -/
  def evalListHOLExact {width : Nat} {σ : Type} [NeZero width]
      (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
      List (ExpHOL width) → Option (List (ValueHOL width))
    | [] => some []
    | expression :: rest =>
        match evalHOLExact state expression, evalListHOLExact state rest with
        | some value, some values => some (value :: values)
        | _, _ => none

  /-- Untagged exact port of the named-struct field-expression step. -/
  def evalListFieldsHOLExact {width : Nat} {σ : Type} [NeZero width]
      (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
      List (MlS × ExpHOL width) → Option (List (MlS × ValueHOL width))
    | [] => some []
    | (name, expression) :: rest =>
        match evalHOLExact state expression, evalListFieldsHOLExact state rest with
        | some value, some values => some ((name, value) :: values)
        | _, _ => none
end

end Flapjack
