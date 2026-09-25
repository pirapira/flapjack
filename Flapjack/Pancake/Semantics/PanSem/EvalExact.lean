/-
EXACT CARRIER EXPRESSIONS (flapjack-pxn.18.3.6.9.15).

Function-backed rendering of HOL `eval_def` (`cakeml/pancake/semantics/panSemScript.sml:209-283`,
identical to `pan_itreeSemScript.sml:79`) over `PanSemStateExact`, the exact
`ExpHOL` syntax, and the exact `ValueHOL` values. `PanSemStateExact` currently
admits arbitrary lookup functions instead of HOL finite-map fields, so this
definition has no `@[hol]` tag.

Source review (flapjack-dlc.120) confirms the tag stays withdrawn: all fifteen
clauses and every used subcarrier match --- `MlS`/`ExpHOL`/`ValueHOL`/`ShapeHOL`/
`StructContextExact` carriers, `HolWordLab` memory, `memaddrs` as a `Prop` for
HOL's `'a word set`, `[NeZero width]` for HOL's positive `dimindex`, and the
Lean-only `[DecidablePred state.memaddrs]` decidability evidence. The blocking
mismatch is the state carrier: HOL `locals`/`globals` are finite maps
`varname |-> 'a v`, while `PanSemStateExact.locals`/`globals` are unrestricted
`MlS → Option _` functions, a strict superset admitting infinite support. The
evaluator is faithful only on the finite-support subcarrier; the exact
finite-map state replacement (`flapjack-pxn.18.3.7.1.3.1.1.2`; audit
`flapjack-pxn.18.3.7.1.3.1.2`) must land before the `eval_def` tag is restored.
Every lookup is `=`-keyed (`MlString` derives
`DecidableEq`); the shape
comparisons go through `shapeEqHOL` (whose `= true` reading is proved exact in
`IsValidValueExact.lean`); loads reuse the tagged exact `memLoadHOLExact`
(`mem_load_def`), `panMemLoad32HOL` (`mem_load_32_def`), `panMemLoadByteHOL`
(`mem_load_byte_def`); the wording operations reuse the tagged exact `wordOpHOL`
(`word_op_def`), `panOpHOL` (`pan_op_def`), `wordCmpHOL` (`word_cmp_def`) and
`wordShiftHOL` (`word_sh_def`).

The evaluator body is retained as a function-backed rendering of `eval_def`:
its clauses are compared one by one against
`cakeml/pancake/semantics/panSemScript.sml:209-283` --- `Const`, `Var
Local`/`Global` (`=`-keyed `FLOOKUP`), `RStruct` (`OPT_MMAP`), `RField`
(`index < LENGTH` as `values[index]?`), `NStruct` (`ALOOKUP` + `UNZIP` +
`field_names' = field_names` + `OPT_MMAP` + `EVERY (s = shape_of v) (ZIP ...)`),
`NField`, `Load`/`Load32`/`LoadByte`, `Op`/`Panop` (`EVERY isValWord` +
`MAP theWord`), `Cmp` (`word_cmp`), `Shift` (`word_sh`),
`BaseAddr`/`TopAddr`/`BytesInWord` --- over the exact `mlstring`-keyed
`PanSemStateExact` function-backed carrier, the exact `ExpHOL` syntax and the exact `ValueHOL`
values.  The mutual list helpers `evalListHOLExact`/`evalListFieldsHOLExact` and
`valueIsWord`/`valueWord`/`lookupFieldHOL` are the `OPT_MMAP`/`EVERY`/`theWord`/
`ALOOKUP` renderings and are untagged.  The shape comparisons go through
`shapeEqHOL` (whose `= true` reading is proved exact in
`IsValidValueExact.lean`); loads reuse the tagged exact `memLoadHOLExact`
(`mem_load_def`), `panMemLoad32HOL` (`mem_load_32_def`), `panMemLoadByteHOL`
(`mem_load_byte_def`); the wording operations reuse the tagged exact `wordOpHOL`
(`word_op_def`), `panOpHOL` (`pan_op_def`), `wordCmpHOL` (`word_cmp_def`) and
`wordShiftHOL` (`word_sh_def`).

Direct source review of the HOL state-invariance cluster
`panPropsScript.sml:644 eval_upd_clock_eq` (`eval (t with clock := ck) e = eval t e`),
`:654 eval_upd_code_eq` (`eval (t with code := code) e = eval t e`),
`:664 eval_upd_eshapes_eq`, and the list-level `:674 opt_mmap_eval_upd_clock_eq`
/ `:686 opt_mmap_eval_upd_clock_eq1` (clock advanced by `ck + s.clock` resp. `ck`
under `OPT_MMAP eval`) finds no separate Lean declaration: HOL `eval` carries the
whole `panSem$state`, whereas this rendering reads none of `state.clock`,
`state.code`, or `state.eshapes`, so all five invariances are consequences of the
clauses above (the list forms through `evalListHOLExact`, the `OPT_MMAP` rendering)
and are simply not stated yet.  They stay untagged together with the evaluator
because the blocking mismatch is the `PanSemStateExact` `locals`/`globals`/`code`/
`eshapes` carrier (unrestricted `MlS → Option _` functions instead of HOL finite
maps) -- not those individual fields.  Restoration of the invariance lemmas over
the faithful finite-support state is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`;
these dispositions are recorded by beads `flapjack-4ac.4.40`, `.41`, `.43`, `.44`.

The recursive `evaluate` dispatcher over this evaluator is separate and not yet
assembled.  Direct original-HOL rows are in
`scripts/hol-probes/pan_eval_probe.out` and are reproduced by
`Flapjack/Test/PanSemEvalExactParity.lean`.
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
  /-- Function-backed rendering of HOL `eval`; untagged because its state
      contains unrestricted functions in place of HOL finite maps. -/
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
