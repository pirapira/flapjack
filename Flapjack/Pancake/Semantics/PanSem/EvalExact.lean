/-
EXACT CARRIER EXPRESSIONS (flapjack-pxn.18.3.6.9.15).

Function-backed rendering of HOL `eval_def` (`cakeml/pancake/semantics/panSemScript.sml:209-283`,
identical to `pan_itreeSemScript.sml:79`) over `PanSemStateExact`, the exact
`ExpHOL` syntax, and the exact `ValueHOL` values. `PanSemStateExact` admits
arbitrary lookup functions instead of HOL finite-map fields, so this
`evalHOLExact` carries no `@[hol]` tag. The exact finite-support rendering lives
in `Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean` as
`PanSemStateFiniteExact.evalHOLFinite`, delegates here through `toExact`, and
carries the qualified `eval_def` tag (`fmap_as_finite_support :=
[locals, globals, code, eshapes]`, manifest status
`reviewed_fmap_as_finite_support`); its clause-shaped equations are in
`EvalFinite.lean`.

Source review (flapjack-dlc.120) confirms all fifteen clauses and every used
subcarrier match --- `MlS`/`ExpHOL`/`ValueHOL`/`ShapeHOL`/
`StructContextExact` carriers, `HolWordLab` memory, `memaddrs` as a `Prop` for
HOL's `'a word set`, `[NeZero width]` for HOL's positive `dimindex`, and the
Lean-only `[DecidablePred state.memaddrs]` decidability evidence. The one
carrier caveat is the state: HOL `locals`/`globals` are finite maps
`varname |-> 'a v`, while `PanSemStateExact.locals`/`globals` are unrestricted
`MlS → Option _` functions, a strict superset admitting infinite support. The
qualified `eval_def` tag is therefore placed on the finite-support rendering
over `PanSemStateFiniteExact` (audit `flapjack-pxn.18.3.7.1.3.1.2`;
`flapjack-pxn.18.3.7.1.3.1.1.2`), not on this raw-function rendering.
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
and are simply not stated yet.  Their exact analogues read this raw-function
`PanSemStateExact` carrier, so they remain untagged; restating them over the
faithful finite-support rendering (`PanSemStateFiniteExact`, the carrier of the
qualified `evalHOLFinite` tag) is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`;
these dispositions are recorded by beads `flapjack-4ac.4.40`, `.41`, `.43`, `.44`.

The recursive `evaluate` dispatcher over this evaluator is separate and not yet
assembled.  Direct original-HOL rows are in
`scripts/hol-probes/pan_eval_probe.out` and are reproduced by
`Flapjack/Test/PanSemEvalExactParity.lean`.

Direct source review of `panPropsScript.sml:621`
`eval_some_var_exp_local_lookup`
(`∀s e v n. eval s e = SOME v ∧ MEM n (var_exp e) ⇒ ∃w. FLOOKUP s.locals n = SOME w`)
finds no statement-exact Lean declaration.  The HOL statement reads the exact
`eval` (`eval_def`) together with the exact `panLang$var_exp`
(`panLangScript.sml:253-270`), whose input is the word-indexed `exp` with
`mlstring` names and whose result is `mlstring list`.  The Lean analogue of the
evaluator is this raw-function `evalHOLExact` (whose faithful finite-support
rendering `evalHOLFinite` in `StateExactFiniteMap.lean` carries the qualified
`eval_def` tag, see above), and the analogue of
`var_exp` is the untagged String-backed `expLocalVars`
(`Flapjack/Pancake/PanLang.lean:1380`, whose HOL tag is withdrawn for the same
carrier reason).  Both sides of the implication are therefore expressible only
over carriers that are not exact HOL ports, so the premise/conclusion shape
cannot be reproduced faithfully here.  The lookup invariant over the faithful
finite-support state is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`, and the
exact `mlstring`-keyed expression/variable carriers by
`flapjack-pxn.18.3.5.8`.  Recorded by bead `flapjack-4ac.4.39`.
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
      contains unrestricted functions in place of HOL finite maps.  The
      faithful finite-support rendering `PanSemStateFiniteExact.evalHOLFinite`
      in `StateExactFiniteMap.lean` delegates here and carries the qualified
      `eval_def` tag. -/
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
