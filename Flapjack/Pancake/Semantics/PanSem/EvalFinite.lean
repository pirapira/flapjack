/-
FINITE-SUPPORT CARRIER EVALUATION (flapjack-pxn.18.3.7.1.3.1.1.2.5).

The exact `eval_def` evaluator `evalHOLExact` (`EvalExact.lean`) quantifies over
`PanSemStateExact`, whose `locals`/`globals`/`code`/`eshapes` are unrestricted
`MlS → Option _` functions.  HOL `panSem$state` instead keeps those fields as
finite maps (`varname |-> 'a v`, `|->`), so the evaluator is faithful only on the
finite-support subcarrier.

This module wraps the reviewed evaluator so its state quantification is
`PanSemStateFiniteExact`, whose four map fields are `HolFiniteMapExact`
(finite support by type).  The wrappers delegate through
`PanSemStateFiniteExact.toExact`, so all fifteen `eval_def` clauses and the mutual
`OPT_MMAP` / structured-field helpers of `EvalExact.lean` are reused unchanged.

The clause-shaped equations below expose each of the fifteen `eval_def` clauses
over the finite carrier one by one; they are the per-clause review surface and
each holds definitionally.

Per-clause source review (against `cakeml/pancake/semantics/panSemScript.sml:209-283`)
is complete and each clause matches: `Const`; `Var Local`/`Global` as
`FLOOKUP` on the finite-map fields (`state.locals.lookup`/`state.globals.lookup`);
`RStruct` (`OPT_MMAP`); `RField` (`index < LENGTH` as `values[index]?`); `NStruct`
(`ALOOKUP` + `UNZIP` + field-name equality + `OPT_MMAP` + `EVERY (shape_of ·)`);
`NField`; `Load`/`Load32`/`LoadByte` (reusing the tagged exact memory helpers);
`Op`/`Panop` (`EVERY isValWord` + `theWord`); `Cmp`; `Shift`;
`BaseAddr`/`TopAddr`/`BytesInWord`.

No `@[hol]` tag yet.  The wrapper bodies are `evalHOLExact state.toExact`, so
they do not textually present HOL's clause-shaped definition body; tagging a
delegating body `eval_def` would overclaim, and the type-hash lock records the
elaborated body.  Restoring the tag requires either a literal clause-shaped
definition over `PanSemStateFiniteExact` plus a mutual-induction equality to the
delegation, or an explicit coordinator ruling that the delegation wrapper plus
these clause equations is the reviewed rendering.  The `fmap_as_finite_support`
qualifier, type-lock coverage, and the production-path follow-up are tracked by
the parent bead `flapjack-pxn.18.3.7.1.3.1.1.2.5`.
-/
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL MlS ShapeHOL StructContextExact)
open Flapjack.Pancake.PanLang (isWfShapeExactHOL structContextLookupHOL)

namespace PanSemStateFiniteExact

/-- Finite-support carrier rendering of HOL `eval` (`panSemScript.sml:209-283`):
    delegate the broad evaluator through the projection `toExact`. -/
def evalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- Finite-support carrier rendering of the `OPT_MMAP eval` list step. -/
def evalListHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact h

/-- Finite-support carrier rendering of the named-struct field-expression step. -/
def evalListFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (MlS × ExpHOL width) → Option (List (MlS × ValueHOL width)) :=
  @evalListFieldsHOLExact width σ _ state.toExact h

@[simp] theorem evalHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) :
    state.evalHOLFinite expression =
      @evalHOLExact width σ _ state.toExact h expression := rfl

@[simp] theorem evalListHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) :
    state.evalListHOLFinite expressions =
      @evalListHOLExact width σ _ state.toExact h expressions := rfl

@[simp] theorem evalListFieldsHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    state.evalListFieldsHOLFinite fields =
      @evalListFieldsHOLExact width σ _ state.toExact h fields := rfl

/-! ## Clause-shaped equations

The wrapper delegates, so the following equations expose each clause of HOL
`eval_def` one by one over the finite-support carrier.  Clause order and side
conditions match `cakeml/pancake/semantics/panSemScript.sml:209-283` exactly, with
the `Var` clauses reading `locals`/`globals` through
`HolFiniteMapExact.lookup`. -/

@[simp] theorem evalHOLFinite_const {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (value : BitVec width) :
    state.evalHOLFinite (.const value) = some (.val (.word value)) := rfl

@[simp] theorem evalHOLFinite_var_local {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) :
    state.evalHOLFinite (.var .local name) = state.locals.lookup name := rfl

@[simp] theorem evalHOLFinite_var_global {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) :
    state.evalHOLFinite (.var .global name) = state.globals.lookup name := rfl

@[simp] theorem evalHOLFinite_rstruct {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fields : List (ExpHOL width)) :
    state.evalHOLFinite (.rstruct fields) =
      (state.evalListHOLFinite fields).map ValueHOL.rStruct := rfl

@[simp] theorem evalHOLFinite_rfield {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (index : Nat) (value : ExpHOL width) :
    state.evalHOLFinite (.rfield index value) =
      (match state.evalHOLFinite value with
       | some (.rStruct values) => values[index]?
       | _ => none) := rfl

@[simp] theorem evalHOLFinite_nstruct {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (fields : List (MlS × ExpHOL width)) :
    state.evalHOLFinite (.nstruct name fields) =
      (match structContextLookupHOL name state.structs with
       | none => none
       | some info =>
           if info.fields.map Prod.fst = fields.map Prod.fst then
             match state.evalListFieldsHOLFinite fields with
             | none => none
             | some fieldValues =>
                 if ((info.fields.map Prod.snd).zip
                     (fieldValues.map (fun pair => shapeOfHOLExact pair.2))).all
                     (fun pair => shapeEqHOL pair.1 pair.2) then
                   some (.nStruct name fieldValues)
                 else none
           else none) := rfl

@[simp] theorem evalHOLFinite_nfield {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (value : ExpHOL width) :
    state.evalHOLFinite (.nfield name value) =
      (match state.evalHOLFinite value with
       | some (.nStruct structName values) =>
           if (structContextLookupHOL structName state.structs).isSome then
             lookupFieldHOL name values
           else none
       | _ => none) := rfl

@[simp] theorem evalHOLFinite_load {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (shape : ShapeHOL) (address : ExpHOL width) :
    state.evalHOLFinite (.load shape address) =
      (if isWfShapeExactHOL state.structs shape then
         match state.evalHOLFinite address with
         | some (.val (.word word)) =>
             memLoadHOLExact shape word state.memaddrs state.memory state.structs
         | _ => none
       else none) := rfl

@[simp] theorem evalHOLFinite_load32 {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (address : ExpHOL width) :
    state.evalHOLFinite (.load32 address) =
      (match state.evalHOLFinite address with
       | some (.val (.word word)) =>
           (panMemLoad32HOL state.memory state.memaddrs state.be word).map
             (fun value => .val (.word (BitVec.ofNat width value.toNat)))
       | _ => none) := rfl

@[simp] theorem evalHOLFinite_loadByte {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (address : ExpHOL width) :
    state.evalHOLFinite (.loadByte address) =
      (match state.evalHOLFinite address with
       | some (.val (.word word)) =>
           (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
             (fun value => .val (.word (BitVec.ofNat width value.toNat)))
       | _ => none) := rfl

@[simp] theorem evalHOLFinite_op {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (operator : BinOp) (arguments : List (ExpHOL width)) :
    state.evalHOLFinite (.op operator arguments) =
      (match state.evalListHOLFinite arguments with
       | some values =>
           if values.all valueIsWord then
             (wordOpHOL operator (values.map valueWord)).map
               (fun word => .val (.word word))
           else none
       | none => none) := rfl

@[simp] theorem evalHOLFinite_panop {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (operator : PanOp) (arguments : List (ExpHOL width)) :
    state.evalHOLFinite (.panop operator arguments) =
      (match state.evalListHOLFinite arguments with
       | some values =>
           if values.all valueIsWord then
             (panOpHOL operator (values.map valueWord)).map
               (fun word => .val (.word word))
           else none
       | none => none) := rfl

@[simp] theorem evalHOLFinite_cmp {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (operator : Cmp) (left right : ExpHOL width) :
    state.evalHOLFinite (.cmp operator left right) =
      (match state.evalHOLFinite left, state.evalHOLFinite right with
       | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
           some (.val (.word
             (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL operator leftWord rightWord
              then 1 else 0)))
       | _, _ => none) := rfl

@[simp] theorem evalHOLFinite_shift {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (operator : Shift) (left right : ExpHOL width) :
    state.evalHOLFinite (.shift operator left right) =
      (match state.evalHOLFinite left, state.evalHOLFinite right with
       | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
           (wordShiftHOL operator leftWord rightWord.toNat).map
             (fun word => .val (.word word))
       | _, _ => none) := rfl

@[simp] theorem evalHOLFinite_baseAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    state.evalHOLFinite .baseAddr = some (.val (.word state.baseAddr)) := rfl

@[simp] theorem evalHOLFinite_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    state.evalHOLFinite .topAddr = some (.val (.word state.topAddr)) := rfl

@[simp] theorem evalHOLFinite_bytesInWord {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    state.evalHOLFinite .bytesInWord =
      some (.val (.word (bytesInWordHOL width))) := rfl

end PanSemStateFiniteExact

end Flapjack
