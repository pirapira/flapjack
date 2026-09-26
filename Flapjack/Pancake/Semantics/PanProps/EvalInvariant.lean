import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep

/-!
Finite-map carrier and expression invariant for the HOL `eval_is_wf_shape_v`
prerequisite to `evaluate_is_wf_shape_invariant`. This submodule sits under
the `panPropsScript.sml` counterpart; its carrier owns the map fields named by
the representation qualifier and is invertibly related to `PanSemStateExact`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS StructContextExact ProgHOL ExpHOL ShapeHOL DeclHOL FunDeclHOL isWfShapeExactHOL varExpHOL
   functionsHOL exceptionsHOL isFunctionHOL isNameHOL isExnDeclHOL)

/-! ## Clearing `locals` under the exact broad evaluator

The HOL theorem `panProps$eval_empty_locals_IMP`
(`cakeml/pancake/semantics/panPropsScript.sml:1584`) reads the exact `eval`
(`eval_def`). The final tagged port below lives over the reviewed finite-map
carrier `PanPropsEvalStateFiniteExact` (whose `evalHOL` delegates to
`evalHOLExact` through the canonical translation). The broad-carrier proof
support in this section is untagged because `PanSemStateExact` represents the
HOL finite-map fields by unrestricted lookup functions.

`evalHOLExact_emptyLocalsHOLExact` is the untagged broad analogue: evaluation
that succeeds after `locals` is cleared to `FEMPTY` also succeeds in the
original state with the same value. It is proved by the mutual induction
`evalHOLExact.induct` with the list transfer rendered through the tagged
`opt_mmap_eq_some_helper` (`List.mapM` is the repository's `OPT_MMAP`). -/

/-- Decidability of the address set is inherited from the underlying state when
    only `locals` is cleared, so the empty-locals state needs no new decision
    procedure. -/
instance emptyLocalsHOLExactDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    DecidablePred (emptyLocalsHOLExact state).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

@[simp] theorem emptyLocalsHOLExact_structs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).structs = state.structs := rfl

@[simp] theorem emptyLocalsHOLExact_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).memaddrs = state.memaddrs := rfl

@[simp] theorem emptyLocalsHOLExact_memory {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).memory = state.memory := rfl

@[simp] theorem emptyLocalsHOLExact_be {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).be = state.be := rfl

@[simp] theorem emptyLocalsHOLExact_baseAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).baseAddr = state.baseAddr := rfl

@[simp] theorem emptyLocalsHOLExact_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).topAddr = state.topAddr := rfl

/-- The exact `OPT_MMAP eval` list step is `List.mapM`. -/
private theorem evalListHOLExact_eq_mapM {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) :
    evalListHOLExact state expressions = expressions.mapM (evalHOLExact state) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      rw [List.mapM_cons, ← ih]
      simp only [evalListHOLExact]
      cases hx : evalHOLExact state expression with
      | none => simp
      | some value => cases hr : evalListHOLExact state rest with
                      | none => simp
                      | some values => simp

/-- The exact named-struct field-expression step is `List.mapM` with the field
    name reattached. -/
private theorem evalListFieldsHOLExact_eq_mapM {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    evalListFieldsHOLExact state fields =
      fields.mapM (fun pair => (evalHOLExact state pair.2).map (fun value => (pair.1, value))) := by
  induction fields with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, expression⟩ := pair
      rw [List.mapM_cons, ← ih]
      simp only [evalListFieldsHOLExact]
      cases hx : evalHOLExact state expression with
      | none => simp
      | some value => cases hr : evalListFieldsHOLExact state rest with
                      | none => simp
                      | some values => simp

/-- Pointwise transfer of an `OPT_MMAP eval` success from the empty-locals state
    to the original state, via `opt_mmap_eq_some_helper`. -/
private theorem evalListHOLExact_transfer_of_pointwise {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) (values : List (ValueHOL width))
    (hpoint : ∀ x ∈ expressions, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (h : evalListHOLExact (emptyLocalsHOLExact state) expressions = some values) :
    evalListHOLExact state expressions = some values := by
  rw [evalListHOLExact_eq_mapM] at h ⊢
  exact optMmapEqSomeHelper _ _ expressions values h hpoint

/-- Pointwise transfer of a named-struct field-list success from the
    empty-locals state to the original state. -/
private theorem evalListFieldsHOLExact_transfer_of_pointwise {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) (values : List (MlS × ValueHOL width))
    (hpoint : ∀ x ∈ fields.map Prod.snd, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (h : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields = some values) :
    evalListFieldsHOLExact state fields = some values := by
  rw [evalListFieldsHOLExact_eq_mapM] at h ⊢
  refine optMmapEqSomeHelper _ _ fields values h ?_
  rintro ⟨name, x⟩ hpair y hy
  simp only [Option.map_eq_some_iff] at hy
  obtain ⟨w, hx, rfl⟩ := hy
  have hmem : x ∈ fields.map Prod.snd := List.mem_map.mpr ⟨(name, x), hpair, rfl⟩
  rw [hpoint x hmem w hx]
  rfl

/-- Untagged broad-carrier analogue of HOL `panProps$eval_empty_locals_IMP`
    (`cakeml/pancake/semantics/panPropsScript.sml:1584`): if the exact broad
    evaluator succeeds after clearing `locals` to `FEMPTY`, it succeeds with the
    same value in the original state. The statement reads the raw-function
    `PanSemStateExact`, so it carries no `@[hol]` tag; the tagged finite-map port
    is `PanPropsEvalStateFiniteExact.evalEmptyLocalsHOLFinite` below. -/
theorem evalHOLExact_emptyLocalsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    ∀ (expression : ExpHOL width) (value : ValueHOL width),
      evalHOLExact (emptyLocalsHOLExact state) expression = some value →
        evalHOLExact state expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
    (motive_2 := fun fields => ∀ x ∈ fields.map Prod.snd, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (motive_3 := fun expressions => ∀ x ∈ expressions, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
  case case1 => intro v h; simpa [evalHOLExact] using h
  case case2 => intro v h
                simp only [evalHOLExact, emptyLocalsHOLExact_locals] at h; cases h
  case case3 => intro v h
                simpa [evalHOLExact, emptyLocalsHOLExact_globals] using h
  case case4 =>
    rename_i fields ih3
    intro v h
    cases hl : evalListHOLExact (emptyLocalsHOLExact state) fields with
    | none => rw [evalHOLExact, hl] at h; cases h
    | some values =>
        have hstate := evalListHOLExact_transfer_of_pointwise state fields values ih3 hl
        rw [evalHOLExact, hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        cases h
        rw [evalHOLExact, hstate]; rfl
  case case5 =>
    rename_i index value values hstruct ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; rw [evalHOLExact, hs]; exact h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case6 =>
    rename_i index value hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => exact (hno vals (ih (.rStruct vals) hw)).elim
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case7 =>
    rename_i name fields hlookup
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup] at h; cases h
  case case8 =>
    rename_i name fields info hlookup hnames heval ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some values =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields values ih2 he
        rw [hstate] at heval; cases heval
  case case9 =>
    rename_i name fields info hlookup hnames fieldValues heval hcheck ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some fv' =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields fv' ih2 he
        simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h
        simp only [evalHOLExact, hlookup, hnames, hstate]
        exact h
  case case10 =>
    rename_i name fields info hlookup hnames fieldValues heval hcheckfalse ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some fv' =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields fv' ih2 he
        simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h
        simp only [evalHOLExact, hlookup, hnames, hstate]
        exact h
  case case11 =>
    rename_i name fields info hlookup hnotnames
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnotnames] at h; cases h
  case case12 =>
    rename_i name value structName values hstruct hisSome ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals =>
            simp only [evalHOLExact, hw, emptyLocalsHOLExact_structs] at h
            simp only [evalHOLExact, hs]; exact h
  case case13 =>
    rename_i name value structName values hstruct hnotSome ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals =>
            simp only [evalHOLExact, hw, emptyLocalsHOLExact_structs] at h
            simp only [evalHOLExact, hs]; exact h
  case case14 =>
    rename_i name value hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals => exact (hno sn vals (ih (.nStruct sn vals) hw)).elim
  case case15 =>
    rename_i shape address hwf word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw,
                  emptyLocalsHOLExact_memaddrs, emptyLocalsHOLExact_memory] at h
                simp only [evalHOLExact, hwf, hs]; exact h
        | rStruct vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
        | nStruct nm vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
  case case16 =>
    rename_i shape address hwf hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
        | nStruct nm vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
  case case17 =>
    rename_i shape address hnotwf
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hnotwf] at h; cases h
  case case18 =>
    rename_i address word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, hw, emptyLocalsHOLExact_memaddrs,
                  emptyLocalsHOLExact_memory, emptyLocalsHOLExact_be] at h
                simp only [evalHOLExact, hs]; exact h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case19 =>
    rename_i address hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case20 =>
    rename_i address word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, hw, emptyLocalsHOLExact_memaddrs,
                  emptyLocalsHOLExact_memory, emptyLocalsHOLExact_be] at h
                simp only [evalHOLExact, hs]; exact h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case21 =>
    rename_i address hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case22 =>
    rename_i operator arguments values heval hall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case23 =>
    rename_i operator arguments values heval hnotall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case24 =>
    rename_i operator arguments hnone ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        rw [hstate] at hnone; cases hnone
  case case25 =>
    rename_i operator arguments values heval hall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case26 =>
    rename_i operator arguments values heval hnotall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case27 =>
    rename_i operator arguments hnone ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        rw [hstate] at hnone; cases hnone
  case case28 =>
    rename_i operator left right lw rw hright hleft ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case29 =>
    rename_i operator left right hno ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case30 =>
    rename_i operator left right lw rw hright hleft ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case31 =>
    rename_i operator left right hno ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case32 => intro v h; simpa [evalHOLExact, emptyLocalsHOLExact_baseAddr] using h
  case case33 => intro v h; simpa [evalHOLExact, emptyLocalsHOLExact_topAddr] using h
  case case34 => intro v h; simpa [evalHOLExact] using h
  case case35 =>
    rename_i x hx y hy
    exact absurd hx (by simp)
  case case36 =>
    rename_i expression rest value values hrest hexpr ih1 ih3 x hx y hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih3 x hx y hy
  case case37 =>
    rename_i expression rest hno ih1 ih3 x hx y hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih3 x hx y hy
  case case38 =>
    rename_i x hx y hy
    exact absurd hx (by simp)
  case case39 =>
    rename_i name expression rest value values hrest hexpr ih1 ih2 x hx y hy
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih2 x hx y hy
  case case40 =>
    rename_i name expression rest hno ih1 ih2 x hx y hy
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih2 x hx y hy

/-- Broad untagged analogue of HOL `update_locals_not_vars_eval_eq_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1042`): updating `locals` at a
    name absent from `var_exp e` leaves evaluation unchanged. This reads the
    raw-function `PanSemStateExact` carrier, so it is not tagged; the tagged
    finite-map port is `updateLocalsNotVarsEvalEqEqHOLFinite` below. -/
theorem evalHOLExact_updLocals_not_mem {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) :
    ∀ (expression : ExpHOL width),
      name ∉ varExpHOL expression →
        evalHOLExact { state with locals := FUPDATE_HOL state.locals (name, word) }
          expression = evalHOLExact state expression := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields =>
        (∀ pair ∈ fields, name ∉ varExpHOL pair.2) →
          evalListFieldsHOLExact
            { state with locals := FUPDATE_HOL state.locals (name, word) } fields =
          evalListFieldsHOLExact state fields)
      (motive_3 := fun expressions =>
        (∀ e ∈ expressions, name ∉ varExpHOL e) →
          evalListHOLExact
            { state with locals := FUPDATE_HOL state.locals (name, word) } expressions =
          evalListHOLExact state expressions)
  case case1 value => intro _; rfl
  case case2 name' =>
    intro h
    have hne : name' ≠ name := by
      intro heq; exact h (by simp [varExpHOL, heq])
    change FLOOKUP (FUPDATE_HOL state.locals (name, word)) name' =
      FLOOKUP state.locals name'
    rw [FLOOKUP_FUPDATE_HOL, if_neg hne]
  case case3 name' => intro _; rfl
  case case4 fields ih =>
    intro h
    have hpoint : ∀ e ∈ fields, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih hpoint
    simp only [evalHOLExact, hlist]
  case case5 index expression values hChild ih =>
    intro h
    have hchild : name ∉ varExpHOL expression := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq, hChild]
  case case6 index expression hNo ih =>
    intro h
    have hchild : name ∉ varExpHOL expression := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case7 structName fields hlookup =>
    intro _; simp only [evalHOLExact, hlookup]
  case case8 structName fields info hlookup hnames heval ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist]
  case case9 structName fields info hlookup hnames fieldValues heval hcheck ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist, heval, hcheck]
  case case10 structName fields info hlookup hnames fieldValues heval hcheckfalse ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist, heval, hcheckfalse]
  case case11 structName fields info hlookup hnotnames =>
    intro _; simp only [evalHOLExact, hlookup, if_neg hnotnames]
  case case12 fieldName value structName values hstruct hisSome ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq, hstruct, hisSome]
  case case13 fieldName value structName values hstruct hnotSome ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case14 fieldName value hNo ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case15 shape address hShape word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hShape, hWord]
  case case16 shape address hShape hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case17 shape address hNo =>
    intro _; simp [evalHOLExact, hNo]
  case case18 address word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hWord]
  case case19 address hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case20 address word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hWord]
  case case21 address hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case22 operator arguments values heval hall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case23 operator arguments values heval hnotall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case24 operator arguments hnone ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case25 operator arguments values heval hall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case26 operator arguments values heval hnotall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case27 operator arguments hnone ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case28 operator left right leftWord rightWord hLeft hRight ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR, hLeft, hRight]
  case case29 operator left right hNo ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR]
  case case30 operator left right leftWord rightWord hLeft hRight ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR, hLeft, hRight]
  case case31 operator left right hNo ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR]
  case case32 => intro _; rfl
  case case33 => intro _; rfl
  case case34 => intro _; rfl
  case case35 => rfl
  case case36 =>
    rename_i head tail tailResult headResult tailEval headEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL head := premise head (by simp)
    have htail : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => premise e (by simp [he])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListHOLExact, hh, ht]
  case case37 =>
    rename_i head tail hNoEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL head := premise head (by simp)
    have htail : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => premise e (by simp [he])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListHOLExact, hh, ht]
  case case38 => rfl
  case case39 =>
    rename_i pairName pairExpr tail headResult tailResult tailEval headEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL pairExpr := premise (pairName, pairExpr) (by simp)
    have htail : ∀ p ∈ tail, name ∉ varExpHOL p.2 := fun p hp => premise p (by simp [hp])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListFieldsHOLExact, hh, ht]
  case case40 =>
    rename_i pairName pairExpr tail hNoEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL pairExpr := premise (pairName, pairExpr) (by simp)
    have htail : ∀ p ∈ tail, name ∉ varExpHOL p.2 := fun p hp => premise p (by simp [hp])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListFieldsHOLExact, hh, ht]

/-- Broad untagged list analogue for HOL
    `OPT_MMAP_update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1088`): a local update at a
    name absent from every expression's `var_exp` leaves the `OPT_MMAP eval`
    list step unchanged. Reads the raw-function `PanSemStateExact` carrier. -/
theorem evalListHOLExact_updLocals_not_mem {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) :
    ∀ (expressions : List (ExpHOL width)),
      name ∉ (expressions.map varExpHOL).flatten →
        evalListHOLExact { state with locals := FUPDATE_HOL state.locals (name, word) }
          expressions = evalListHOLExact state expressions := by
  intro expressions
  induction expressions with
  | nil => intro _; rfl
  | cons head tail ih =>
      intro h
      have hpoint : ∀ e ∈ head :: tail, name ∉ varExpHOL e :=
        (not_mem_map_flatten varExpHOL (head :: tail) name).mp h
      have hhead := hpoint head (by simp)
      have htailPoint : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => hpoint e (by simp [he])
      have ihTail := ih ((not_mem_map_flatten varExpHOL tail name).mpr htailPoint)
      have hheadEq := evalHOLExact_updLocals_not_mem state name word head hhead
      simp only [evalListHOLExact, hheadEq, ihTail]

/-- Two independent HOL finite-map arguments packaged as fields so the
    canonical `fmap_as_finite_support` qualifier can name each translation. -/
structure PanPropsResVarMapsExact (α β : Type) where
  fm : HolFiniteMapExact α β
  fm2 : HolFiniteMapExact α β

/-- Broad function-map counterpart for the two generic `res_var` inputs. -/
structure PanPropsResVarMapsBroad (α β : Type) where
  fm : FiniteMap α β
  fm2 : FiniteMap α β

namespace PanPropsResVarMapsExact

def toBroad {α β : Type} (maps : PanPropsResVarMapsExact α β) :
    PanPropsResVarMapsBroad α β :=
  ⟨maps.fm.lookup, maps.fm2.lookup⟩

def ofBroad {α β : Type} (maps : PanPropsResVarMapsBroad α β)
    (support : (∃ keys : List α, ∀ key, maps.fm key ≠ none → key ∈ keys) ∧
      ∃ keys : List α, ∀ key, maps.fm2 key ≠ none → key ∈ keys) :
    PanPropsResVarMapsExact α β :=
  ⟨⟨maps.fm, support.1⟩, ⟨maps.fm2, support.2⟩⟩

theorem toBroad_ofBroad {α β : Type} (maps : PanPropsResVarMapsBroad α β)
    (support : (∃ keys : List α, ∀ key, maps.fm key ≠ none → key ∈ keys) ∧
      ∃ keys : List α, ∀ key, maps.fm2 key ≠ none → key ∈ keys) :
    (ofBroad maps support).toBroad = maps := by
  cases maps
  rfl

theorem ofBroad_toBroad {α β : Type} (maps : PanPropsResVarMapsExact α β) :
    ofBroad maps.toBroad ⟨maps.fm.finiteSupport, maps.fm2.finiteSupport⟩ = maps := by
  cases maps with
  | mk fm fm2 =>
      cases fm
      cases fm2
      simp [ofBroad, toBroad]

/-- Canonical finite-map witness for the two generic HOL `fmap` arguments. -/
theorem holFmapAsFiniteSupportWitness {α β : Type} :
    (∀ (maps : PanPropsResVarMapsBroad α β) support,
        (ofBroad maps support).toBroad = maps) ∧
    (∀ maps : PanPropsResVarMapsExact α β,
        ofBroad maps.toBroad ⟨maps.fm.finiteSupport, maps.fm2.finiteSupport⟩ = maps) :=
  ⟨fun maps support => toBroad_ofBroad maps support, fun maps => ofBroad_toBroad maps⟩

end PanPropsResVarMapsExact

/-- `FEVERY P fm` on the finite-support carrier. This pointwise definition
    follows HOL's `FEVERY`/`FLOOKUP` view without adding a membership premise. -/
def feveryHOL {α β : Type} (P : α × β → Bool) (fm : HolFiniteMapExact α β) : Prop :=
  ∀ key value, fm.lookup key = some value → P (key, value) = true

/-- Exact finite-map port of HOL `FEVERY_res_var_FLOOKUP`
    (`panPropsScript.sml:1222`). The two independent HOL map parameters are
    bundled as the product fields `fm` and `fm2`: the broad counterpart stores
    both function maps independently, and the witness roundtrips them without
    relating their contents. Their finite-support proofs are intrinsic to the
    HOL fmap carrier. The qualifier records only this canonical representation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FEVERY_res_var_FLOOKUP"
  (fmap_as_finite_support := [fm, fm2])]
theorem feveryResVarFlookupHOL {α β : Type} [DecidableEq α]
    (P : α × β → Bool) (maps : PanPropsResVarMapsExact α β) (name : α) :
    (feveryHOL P maps.fm ∧ feveryHOL P maps.fm2) →
      feveryHOL P (maps.fm.resVarEq (name, maps.fm2.lookup name)) := by
  intro h
  rcases h with ⟨hfm, hfm2⟩
  intro key value hresult
  cases hlookup : maps.fm2.lookup name with
  | none =>
      by_cases hkey : key = name
      · subst key
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
          FDOMSUB_HOL, hlookup] at hresult
      · have hsource : maps.fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
            FDOMSUB_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource
  | some newValue =>
      by_cases hkey : key = name
      · subst key
        have hvalue : newValue = value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup] using hresult
        subst value
        exact hfm2 name newValue hlookup
      · have hsource : maps.fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource

/-- PanProps-local finite-map rendering of HOL's PanSem state. The four
    `HolFiniteMapExact` fields correspond to HOL `|->` fields; all other fields
    retain the exact PanSem carrier types. -/
structure PanPropsEvalStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
  locals : HolFiniteMapExact MlS (ValueHOL width)
  globals : HolFiniteMapExact MlS (ValueHOL width)
  structs : StructContextExact
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  eshapes : HolFiniteMapExact MlS ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

namespace PanPropsEvalStateFiniteExact

/-- Forget the finite-map witnesses and expose the exact broad state. -/
def toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : PanSemStateExact width σ where
  locals := state.locals.lookup
  globals := state.globals.lookup
  structs := state.structs
  code := state.code.lookup
  eshapes := state.eshapes.lookup
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- Build this finite-map carrier from a broad state with finite support. -/
def ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    PanPropsEvalStateFiniteExact width σ where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  structs := state.structs
  code := { lookup := state.code, finiteSupport := h.2.2.1 }
  eshapes := { lookup := state.eshapes, finiteSupport := h.2.2.2 }
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

instance decidableToExactMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    DecidablePred state.toExact.memaddrs := by
  simpa [PanPropsEvalStateFiniteExact.toExact] using h

theorem toExact_ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (ofExact state h).toExact = state := rfl

theorem toExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : state.toExact.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport,
    state.code.finiteSupport, state.eshapes.finiteSupport⟩

theorem ofExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    ofExact state.toExact state.toExact_finiteSupport = state := by
  cases state
  rfl

/-- Checked canonical witness for this module's finite-map field qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩

/-- State codec to the canonical PanSem finite-support carrier that owns the
    tagged `evaluate_decls_def`. Both structures retain identical HOL fields;
    this conversion changes only the Lean structure name. -/
def toPanSemFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  eshapes := state.eshapes
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

instance toPanSemFiniteDecidableMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    DecidablePred state.toPanSemFinite.memaddrs := by
  simpa [toPanSemFinite] using h

/-- Inverse state codec from the canonical PanSem finite-support carrier. -/
def ofPanSemFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanPropsEvalStateFiniteExact width σ where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  eshapes := state.eshapes
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

@[simp] theorem ofPanSemFinite_toPanSemFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ) :
    ofPanSemFinite state.toPanSemFinite = state := by
  cases state
  rfl

@[simp] theorem toPanSemFinite_ofPanSemFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) :
    (ofPanSemFinite state).toPanSemFinite = state := by
  cases state
  rfl

/-- Local finite-map `dec_clock` operation for the projection equations below. -/
def decClockForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- Local finite-map `empty_locals` operation for the projection equations. -/
def emptyLocalsForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with locals := HolFiniteMapExact.empty }

/-- Clearing `locals` changes no other state component, so the address-set
    decision procedure is inherited. -/
instance emptyLocalsForStructsSimpsDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs] :
    DecidablePred (emptyLocalsForStructsSimps state).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

/-- Projection of the finite-map empty-locals operation to the canonical broad
    `emptyLocalsHOLExact`. -/
@[simp] theorem emptyLocalsForStructsSimps_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    (emptyLocalsForStructsSimps state).toExact = emptyLocalsHOLExact state.toExact :=
  rfl

/-- HOL `panProps$structs_simps` (`panPropsScript.sml:1217`): the six
    projections of `dec_clock` and `empty_locals`. This uses the existing
    PanProps finite-map state and its canonical same-module roundtrip witness. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "structs_simps"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem structsSimpsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    (decClockForStructsSimps state).structs = state.structs ∧
    (emptyLocalsForStructsSimps state).structs = state.structs ∧
    (decClockForStructsSimps state).globals = state.globals ∧
    (emptyLocalsForStructsSimps state).globals = state.globals ∧
    (decClockForStructsSimps state).locals = state.locals ∧
    (emptyLocalsForStructsSimps state).locals = HolFiniteMapExact.empty := by
  simp [decClockForStructsSimps, emptyLocalsForStructsSimps]

/-- Flapjack-specific adapter from the PanProps finite-support state to the
    existing PanSem expression evaluator. HOL `eval_def` is tagged on its
    PanSem counterpart; this adapter has no separate HOL declaration. -/
def evalHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- The finite-map empty-locals evaluation is the broad exact evaluation over
    the canonical `emptyLocalsHOLExact` state; this is the state-translation
    bridge used by the tagged port below. -/
theorem evalHOL_emptyLocalsForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) :
    (emptyLocalsForStructsSimps state).evalHOL expression =
      @evalHOLExact width σ _ (emptyLocalsHOLExact state.toExact) h expression := rfl

/-- Exact finite-support port of HOL `panProps$eval_upd_clock_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:644-652`):
    `!t e ck. eval (t with clock := ck) e = eval t e`. The quantifier order
    (state, expression, clock) follows the source and the expression evaluator
    does not read `clock`. The state is the PanProps counterpart carrier whose
    four `|->` fields are the reviewed canonical `HolFiniteMapExact`
    translation (canonical witness `holFmapAsFiniteSupportWitness` in this
    module); `evalHOL` delegates to the exact broad evaluator through `toExact`
    and the codec `evaluateDeclsPanPropsHOLFinite_toCanonical` connects the
    PanProps carrier to the canonical tagged PanSem state. `[NeZero width]`
    models HOL's positive word dimension and `DecidablePred state.memaddrs` is
    computation evidence for the HOL word-set guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_clock_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalHOL_upd_clock_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) (clock : Nat) :
    @evalHOL width σ _ { state with clock := clock } h expression =
      @evalHOL width σ _ state h expression := by
  simp only [evalHOL]
  exact evalHOLExact_upd_clock_eq state.toExact expression clock

/-- Exact finite-support port of HOL `panProps$eval_upd_code_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:654-662`):
    `!t e code. eval (t with code := code) e = eval t e`. Same reviewed carrier
    and codec justification as `evalHOL_upd_clock_eq`; the expression evaluator
    does not read `code`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_code_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalHOL_upd_code_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    @evalHOL width σ _ { state with code := code } h expression =
      @evalHOL width σ _ state h expression := by
  simp only [evalHOL]
  exact evalHOLExact_upd_code_eq state.toExact expression code.lookup

/-- Exact finite-support port of HOL `panProps$eval_upd_eshapes_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:664-672`):
    `!t e esh. eval (t with eshapes := esh) e = eval t e`. Same reviewed carrier
    and codec justification as `evalHOL_upd_clock_eq`; the expression evaluator
    does not read `eshapes`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_eshapes_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalHOL_upd_eshapes_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) (eshapes : HolFiniteMapExact MlS ShapeHOL) :
    @evalHOL width σ _ { state with eshapes := eshapes } h expression =
      @evalHOL width σ _ state h expression := by
  simp only [evalHOL]
  exact evalHOLExact_upd_eshapes_eq state.toExact expression eshapes.lookup

/-- Exact finite-support port of HOL `panProps$eval_empty_locals_IMP`
    (`cakeml/pancake/semantics/panPropsScript.sml:1584`):
    `!s e v. eval (s with locals := FEMPTY) e = SOME v ==> eval s e = SOME v`.
    The quantifier order (state, expression, value) and the
    empty-locals premise/same-value conclusion follow the source. The state is
    the reviewed PanProps finite-map carrier: `emptyLocalsForStructsSimps` clears
    `locals` exactly like HOL `FEMPTY`, and `evalHOL` delegates to the exact
    broad evaluator through `toExact`. The four `|->` fields
    (`locals`, `globals`, `code`, `eshapes`) are the reviewed canonical
    `HolFiniteMapExact` translation recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness` in this
    module); `[NeZero width]` models HOL's nonempty word index and
    `DecidablePred state.memaddrs` is computation evidence for the HOL word-set
    guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_empty_locals_IMP"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalEmptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width),
      (emptyLocalsForStructsSimps state).evalHOL expression = some value →
        state.evalHOL expression = some value := by
  intro state hdec expression value h
  rw [evalHOL_emptyLocalsForStructsSimps state expression] at h
  exact evalHOLExact_emptyLocalsHOLExact state.toExact expression value h

/-- Flapjack-specific PanProps adapter for recursive declaration evaluation.
    It has no independent HOL tag: the faithful `evaluate_decls_def` belongs
    in the PanSem counterpart and is tracked by `flapjack-4ac.3.53`. Its
    successful and failing results are kernel-checked equivalent through
    `toExact` to the existing function-backed `evaluateDeclsHOLExact`. -/
def evaluateDeclsPanPropsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs] :
    List (DeclHOL width) → Option (PanPropsEvalStateFiniteExact width σ)
  | [] => some state
  | .name _ _ :: declarations => evaluateDeclsPanPropsHOLFinite state declarations
  | .decl shape name expression :: declarations =>
      match evalHOL { state with locals := HolFiniteMapExact.empty } expression with
      | some value =>
          if shapeEqHOL shape (shapeOfHOLExact value) then
            evaluateDeclsPanPropsHOLFinite
              { state with globals := state.globals.update (name, value) } declarations
          else none
      | none => none
  | .function declaration :: declarations =>
      if declaration.params.all
          (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
          isWfShapeExactHOL state.structs declaration.returnShape then
        evaluateDeclsPanPropsHOLFinite
          { state with code := state.code.update (declaration.name,
            (declaration.params, declaration.body, declaration.returnShape)) }
          declarations
      else none
  | .exnDecl exceptionName shape :: declarations =>
      if (state.eshapes.lookup exceptionName).isNone &&
          isWfShapeExactHOL state.structs shape then
        evaluateDeclsPanPropsHOLFinite
          { state with eshapes := state.eshapes.update (exceptionName, shape) }
          declarations
      else none

@[simp] private theorem toExact_updateGlobal {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS)
    (value : ValueHOL width) :
    ({ state with globals := state.globals.update (name, value) }).toExact =
      evaluateDeclsSetGlobal state.toExact name value := by
  cases state
  simp [PanPropsEvalStateFiniteExact.toExact, evaluateDeclsSetGlobal,
    HolFiniteMapExact.lookup_update_pointwise]

@[simp] private theorem toExact_updateCode {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (declaration : Flapjack.Pancake.PanLang.FunDeclHOL width) :
    ({ state with code := state.code.update (declaration.name,
      (declaration.params, declaration.body, declaration.returnShape)) }).toExact =
      evaluateDeclsSetCode state.toExact declaration.name declaration.params
        declaration.body declaration.returnShape := by
  cases state
  simp [PanPropsEvalStateFiniteExact.toExact, evaluateDeclsSetCode,
    HolFiniteMapExact.lookup_update_pointwise]

@[simp] private theorem toExact_updateEshape {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL) :
    ({ state with eshapes := state.eshapes.update (name, shape) }).toExact =
      evaluateDeclsSetEshape state.toExact name shape := by
  cases state
  simp [PanPropsEvalStateFiniteExact.toExact, evaluateDeclsSetEshape,
    HolFiniteMapExact.lookup_update_pointwise]

/-- Flapjack-specific bridge: the finite-support declaration rendering
    projects to the established PanSem `evaluateDeclsHOLExact` for every
    program, including failures. This checked equation connects the tagged
    finite-map definition above to the existing exact declaration semantics;
    it is infrastructure rather than a separate HOL declaration. -/
theorem evaluateDeclsPanPropsHOLFinite_toExact {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (program : List (DeclHOL width)) :
    (evaluateDeclsPanPropsHOLFinite state program).map
      PanPropsEvalStateFiniteExact.toExact =
      evaluateDeclsHOLExact state.toExact program := by
  induction program generalizing state with
  | nil => rfl
  | cons declaration rest ih =>
      letI : DecidablePred state.toExact.memaddrs := by
        simpa [PanPropsEvalStateFiniteExact.toExact] using
          (inferInstance : DecidablePred state.memaddrs)
      cases declaration with
      | name name fields =>
          simpa [evaluateDeclsPanPropsHOLFinite, evaluateDeclsHOLExact] using ih state
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite]
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none =>
              have hevalExact : evalHOLExact
                  { state.toExact with locals := fun _ => none } expression = none := by
                simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact,
                  HolFiniteMapExact.empty] using heval
              simp [evaluateDeclsHOLExact, hevalExact]
          | some value =>
              have hevalExact : evalHOLExact
                  { state.toExact with locals := fun _ => none } expression = some value := by
                simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact,
                  HolFiniteMapExact.empty] using heval
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [evaluateDeclsHOLExact, hevalExact, if_pos hshape]
                let nextState :=
                  { state with globals := state.globals.update (name, value) }
                have htail := ih nextState
                simpa [nextState, toExact_updateGlobal] using htail
              · simp [hshape, evaluateDeclsHOLExact, hevalExact]
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite]
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · have hconditionExact :
                (declaration.params.all
                    (fun parameter => isWfShapeExactHOL state.toExact.structs parameter.2) &&
                  isWfShapeExactHOL state.toExact.structs declaration.returnShape) = true := by
              simpa [condition, PanPropsEvalStateFiniteExact.toExact] using hcondition
            simp only [condition, hcondition, if_pos, evaluateDeclsHOLExact,
              hconditionExact, if_pos]
            let nextState :=
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
            have htail := ih nextState
            simpa [nextState, toExact_updateCode] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [evaluateDeclsHOLExact, PanPropsEvalStateFiniteExact.toExact,
              condition, hconditionFalse]
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsPanPropsHOLFinite]
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · have hconditionExact :
                ((state.toExact.eshapes exceptionName).isNone &&
                  isWfShapeExactHOL state.toExact.structs shape) = true := by
              simpa [condition, PanPropsEvalStateFiniteExact.toExact] using hcondition
            simp only [condition, hcondition, if_pos, evaluateDeclsHOLExact,
              hconditionExact, if_pos]
            let nextState :=
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
            have htail := ih nextState
            simpa [nextState, toExact_updateEshape] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [evaluateDeclsHOLExact, PanPropsEvalStateFiniteExact.toExact,
              condition, hconditionFalse]

/-- Kernel-checked success-and-failure bridge from the PanProps-local
    evaluator adapter to the canonical tagged PanSem finite-support
    `evaluateDeclsHOLFinite`. The state codec is a field-for-field roundtrip;
    this equation equates the complete `Option` result after converting every
    successful result state, so the PanProps tagged invariants below are about
    the canonical evaluator rather than a similar duplicate. -/
theorem evaluateDeclsPanPropsHOLFinite_toCanonical {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (program : List (DeclHOL width)) :
    (evaluateDeclsPanPropsHOLFinite state program).map
      PanPropsEvalStateFiniteExact.toPanSemFinite =
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program := by
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using
      (inferInstance : DecidablePred state.memaddrs)
  induction program generalizing state with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simpa [evaluateDeclsPanPropsHOLFinite,
            PanSemStateFiniteExact.evaluateDeclsHOLFinite] using ih state
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite,
            PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state.toPanSemFinite).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite,
              PanPropsEvalStateFiniteExact.toPanSemFinite] using
              (inferInstance : DecidablePred state.memaddrs)
          have heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression =
              PanSemStateFiniteExact.evalHOLFinite
                (PanSemStateFiniteExact.emptyLocalsHOLFinite state.toPanSemFinite)
                expression := rfl
          rw [heval]
          cases hevalCanonical : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state.toPanSemFinite)
              expression with
          | none => simp
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [if_pos hshape]
                let nextState :=
                  { state with globals := state.globals.update (name, value) }
                have htail := ih nextState
                simpa [nextState, PanPropsEvalStateFiniteExact.toPanSemFinite,
                  PanSemStateFiniteExact.setGlobalHOLFinite]
                  using htail
              · simp [hshape]
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite,
            PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          have hconditionCanonical :
              (declaration.params.all
                  (fun parameter => isWfShapeExactHOL state.toPanSemFinite.structs parameter.2) &&
                isWfShapeExactHOL state.toPanSemFinite.structs declaration.returnShape) =
                  condition := rfl
          by_cases hcondition : condition = true
          · simp only [condition, hconditionCanonical, hcondition, if_pos]
            let nextState :=
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
            have htail := ih nextState
            simpa [nextState, PanPropsEvalStateFiniteExact.toPanSemFinite] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse, hconditionCanonical]
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsPanPropsHOLFinite,
            PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          have hconditionCanonical :
              ((state.toPanSemFinite.eshapes.lookup exceptionName).isNone &&
                isWfShapeExactHOL state.toPanSemFinite.structs shape) = condition := rfl
          by_cases hcondition : condition = true
          · simp only [condition, hconditionCanonical, hcondition, if_pos]
            let nextState :=
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
            have htail := ih nextState
            simpa [nextState, PanPropsEvalStateFiniteExact.toPanSemFinite] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse, hconditionCanonical]

private theorem panMemLoad32HOL_monoDomain {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain1 domain2 : RiscV.Word width → Prop)
    [DecidablePred domain1] [DecidablePred domain2]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hsubset : ∀ current, domain1 current → domain2 current)
    {value : RiscV.Word 32}
    (hload : panMemLoad32HOL memory domain1 bigEndian address = some value) :
    panMemLoad32HOL memory domain2 bigEndian address = some value := by
  unfold panMemLoad32HOL at hload ⊢
  by_cases haligned : address.toNat % 4 = 0
  · simp only [if_pos haligned] at hload ⊢
    cases hmemory : memory (panByteAlignHOL (width := width) address) with
    | word word =>
        simp only [hmemory] at hload ⊢
        by_cases hdomain : domain1 (panByteAlignHOL (width := width) address)
        · simp only [if_pos hdomain] at hload
          have hdomain2 := hsubset _ hdomain
          simp only [if_pos hdomain2]
          exact hload
        · simp [hdomain] at hload
  · simp [haligned] at hload

private theorem evalHOLExactMemaddrsMono {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs]
    (hsubset : ∀ address, state.memaddrs address → memaddrs address) :
    ∀ expression value,
      evalHOLExact state expression = some value →
        evalHOLExact { state with memaddrs := memaddrs } expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields => ∀ values,
        evalListFieldsHOLExact state fields = some values →
          evalListFieldsHOLExact { state with memaddrs := memaddrs } fields = some values)
      (motive_3 := fun expressions => ∀ values,
        evalListHOLExact state expressions = some values →
          evalListHOLExact { state with memaddrs := memaddrs } expressions = some values)
  case case4 fields ih =>
    intro value hEval
    cases hFields : evalListHOLExact state fields with
    | none => simp [evalHOLExact, hFields] at hEval
    | some values =>
        simp only [evalHOLExact, hFields] at hEval
        cases hEval
        simp [evalHOLExact, ih values hFields]
  case case15 shape address hShape word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hLoad : memLoadHOLExact shape word state.memaddrs state.memory state.structs =
        some value := by
      simpa [evalHOLExact, hShape, hAddress] using hEval
    have hLoad' := memLoadHOLExactSwapMemaddrs.1 shape word state.memaddrs
      state.memory state.structs value memaddrs ⟨hLoad, hsubset⟩
    simpa [evalHOLExact, hShape, hAddress'] using hLoad'
  case case18 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : Option.map (fun loaded =>
        .val (.word (BitVec.ofNat width loaded.toNat)))
        (panMemLoad32HOL state.memory state.memaddrs state.be word) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    cases hSource : panMemLoad32HOL state.memory state.memaddrs state.be word with
    | none => simp [hSource] at hRead
    | some loaded =>
        have hValue : ValueHOL.val (.word (BitVec.ofNat width loaded.toNat)) = value := by
          simpa [hSource] using hRead
        have hLoad' := panMemLoad32HOL_monoDomain state.memory state.memaddrs
          memaddrs state.be word hsubset hSource
        simpa [evalHOLExact, hAddress', hLoad'] using hValue
  all_goals
    try intro result hEval
    simp_all [evalHOLExact, evalListHOLExact, evalListFieldsHOLExact,
      panMemLoadByteHOL]

/-- Exact port of HOL `eval_swap_memaddrs`
    (`cakeml/pancake/semantics/panPropsScript.sml:1703-1715`). It keeps HOL's
    conjunction premise and record-update conclusion. The state uses the local
    finite-support carrier and the qualifier records precisely its four HOL
    finite-map fields. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memaddrs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalSwapMemaddrsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (state.evalHOL expression = some value ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
          ({ state with memaddrs := memaddrs }.evalHOL expression = some value) := by
  intro state hmemaddrs expression value memaddrs hmemaddrs2 h
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hmemaddrs
  have hEval : evalHOLExact state.toExact expression = some value := by
    simpa [evalHOL] using h.1
  have hWidened := evalHOLExactMemaddrsMono state.toExact memaddrs h.2
    expression value hEval
  simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact] using hWidened

private theorem panMemLoad32HOL_agreeMemory {width : Nat} [NeZero width]
    (memory1 memory2 : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hagree : ∀ current, domain current → memory1 current = memory2 current) :
    panMemLoad32HOL memory1 domain bigEndian address =
      panMemLoad32HOL memory2 domain bigEndian address := by
  unfold panMemLoad32HOL
  by_cases haligned : address.toNat % 4 = 0
  · simp only [if_pos haligned]
    by_cases hdomain : domain (panByteAlignHOL (width := width) address)
    · have hmemory := hagree _ hdomain
      rw [hmemory]
    · simp [hdomain]
  · simp [haligned]

private theorem panMemLoadByteHOL_agreeMemory {width : Nat} [NeZero width]
    (memory1 memory2 : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hagree : ∀ current, domain current → memory1 current = memory2 current) :
    panMemLoadByteHOL memory1 domain bigEndian address =
      panMemLoadByteHOL memory2 domain bigEndian address := by
  unfold panMemLoadByteHOL
  let aligned := panByteAlignHOL (width := width) address
  by_cases hdomain : domain aligned
  · have hmemory := hagree aligned hdomain
    simp [aligned, hdomain, hmemory]
  · simp [aligned, hdomain]

private theorem evalHOLExactSwapMemory {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] (memory : RiscV.Word width → HolWordLab width)
    (hagree : ∀ address, state.memaddrs address → state.memory address = memory address) :
    ∀ expression value,
      evalHOLExact state expression = some value →
        evalHOLExact { state with memory := memory } expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields => ∀ values,
        evalListFieldsHOLExact state fields = some values →
          evalListFieldsHOLExact { state with memory := memory } fields = some values)
      (motive_3 := fun expressions => ∀ values,
        evalListHOLExact state expressions = some values →
          evalListHOLExact { state with memory := memory } expressions = some values)
  case case4 fields ih =>
    intro value hEval
    cases hFields : evalListHOLExact state fields with
    | none => simp [evalHOLExact, hFields] at hEval
    | some values =>
        simp only [evalHOLExact, hFields] at hEval
        cases hEval
        simp [evalHOLExact, ih values hFields]
  case case15 shape address hShape word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hLoad : memLoadHOLExact shape word state.memaddrs state.memory state.structs =
        some value := by
      simpa [evalHOLExact, hShape, hAddress] using hEval
    have hLoad' := memLoadHOLExactSwapMemory.1 shape word state.memaddrs
      state.memory state.structs value memory ⟨hLoad, hagree⟩
    simpa [evalHOLExact, hShape, hAddress'] using hLoad'
  case case18 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : (panMemLoad32HOL state.memory state.memaddrs state.be word).map
        (fun loaded => .val (.word (BitVec.ofNat width loaded.toNat))) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    have hRead' := panMemLoad32HOL_agreeMemory state.memory memory state.memaddrs
      state.be word hagree
    rw [hRead'] at hRead
    simpa [evalHOLExact, hAddress'] using hRead
  case case20 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
        (fun loaded => .val (.word (BitVec.ofNat width loaded.toNat))) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    have hRead' := panMemLoadByteHOL_agreeMemory state.memory memory state.memaddrs
      state.be word hagree
    rw [hRead'] at hRead
    simpa [evalHOLExact, hAddress'] using hRead
  all_goals
    try intro result hEval
    simp_all [evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]

/-- Exact finite-support port of HOL `eval_swap_memory`
    (`panPropsScript.sml:1734-1742`). It preserves HOL's successful evaluation
    and pointwise memory-agreement premise, replacing only the state's memory.
    The local carrier owns the four finite-map fields named by the qualifier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memory"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalSwapMemoryHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (expression : ExpHOL width)
      (value : ValueHOL width) (memory : RiscV.Word width → HolWordLab width),
      (state.evalHOL expression = some value ∧
        (∀ address, state.memaddrs address → state.memory address = memory address)) →
        ({ state with memory := memory }.evalHOL expression = some value) := by
  intro state hmemaddrs expression value memory h
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hmemaddrs
  have hEval : evalHOLExact state.toExact expression = some value := by
    simpa [evalHOL] using h.1
  have hSame := evalHOLExactSwapMemory state.toExact memory h.2 expression value hEval
  simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact] using hSame

private theorem evaluateDeclsPanPropsMemaddrsMono {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (memaddrs : RiscV.Word width → Prop)
    [DecidablePred memaddrs] (program : List (DeclHOL width))
    (result : PanPropsEvalStateFiniteExact width σ)
    (hEval : evaluateDeclsPanPropsHOLFinite state program = some result)
    (hsubset : ∀ address, state.memaddrs address → memaddrs address) :
    evaluateDeclsPanPropsHOLFinite { state with memaddrs := memaddrs } program =
      some { result with memaddrs := memaddrs } := by
  induction program generalizing state result with
  | nil =>
      simp [evaluateDeclsPanPropsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval ⊢
          exact ih state result hEval hsubset
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have hevalWidened := evalSwapMemaddrsHOLFinite
                  ({ state with locals := HolFiniteMapExact.empty }) expression value memaddrs
                  ⟨heval, hsubset⟩
                let nextState :=
                  { state with globals := state.globals.update (name, value) }
                have htail := ih nextState result hEval hsubset
                simp only [evaluateDeclsPanPropsHOLFinite, hevalWidened, if_pos hshape]
                exact htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval hsubset
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval hsubset
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval

 /-- Exact finite-support port of HOL `evaluate_decls_memaddrs_mono`
    (`panPropsScript.sml:1766-1778`). The quantified state, declaration list,
    successful result, replacement domain, conjunctive success/subset premise,
    and updated-result conclusion follow HOL's order and shape. The local
    evaluator follows `evaluate_decls_def` (`panSemScript.sml:814-837`) clause
    for clause. `PanPropsEvalStateFiniteExact` supplies the reviewed canonical
    finite-map representation for the four `|->` fields; the qualifier records
    only that representation. `[NeZero width]` models HOL's positive word
    dimension, and `DecidablePred` supplies executable decisions for HOL word
    set membership. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_memaddrs_mono"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsMemaddrsMonoHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (evaluateDeclsPanPropsHOLFinite state program = some result ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
        evaluateDeclsPanPropsHOLFinite { state with memaddrs := memaddrs } program =
          some { result with memaddrs := memaddrs } := by
  intro state hstate program result memaddrs hmemaddrs h
  exact evaluateDeclsPanPropsMemaddrsMono state memaddrs program result h.1 h.2

/-- Exact finite-support port of HOL `evaluate_decls_swap_memaddrs`
    (`panPropsScript.sml:1718`). It preserves the source quantifier order and
    premise: successful declaration evaluation together with inclusion of the
    original address domain in the replacement domain. The conclusion changes
    only `memaddrs` in the initial and successful result states. The four
    finite-map fields are the reviewed canonical representation recorded by
    the qualifier. Although this proof carrier has a separate Lean structure
    name, `evaluateDeclsPanPropsHOLFinite_toCanonical` proves a field-for-field
    state codec and equality of complete success/failure results with the
    canonical tagged `PanSemStateFiniteExact.evaluateDeclsHOLFinite`.
    `[DecidablePred memaddrs]` supplies Lean computation evidence for the
    replacement HOL set. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memaddrs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsSwapMemaddrsHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (evaluateDeclsPanPropsHOLFinite state program = some result ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
        evaluateDeclsPanPropsHOLFinite { state with memaddrs := memaddrs } program =
          some { result with memaddrs := memaddrs } := by
  intro state hstate program result memaddrs hmemaddrs h
  exact evaluateDeclsPanPropsMemaddrsMono state memaddrs program result h.1
    (fun address hsource => h.2 address hsource)

private theorem evaluateDeclsPanPropsMemorySwap {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (memory : RiscV.Word width → HolWordLab width)
    (program : List (DeclHOL width))
    (result : PanPropsEvalStateFiniteExact width σ)
    (hEval : evaluateDeclsPanPropsHOLFinite state program = some result)
    (hagree : ∀ address, state.memaddrs address → state.memory address = memory address) :
    evaluateDeclsPanPropsHOLFinite { state with memory := memory } program =
      some { result with memory := memory } := by
  induction program generalizing state result with
  | nil =>
      simp [evaluateDeclsPanPropsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval ⊢
          exact ih state result hEval hagree
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have hevalMemory := evalSwapMemoryHOLFinite
                  ({ state with locals := HolFiniteMapExact.empty }) expression value memory
                  ⟨heval, hagree⟩
                let nextState :=
                  { state with globals := state.globals.update (name, value) }
                have htail := ih nextState result hEval hagree
                simpa [evaluateDeclsPanPropsHOLFinite, hshape, hevalMemory,
                  nextState] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval hagree
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval hagree
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval

/-- HOL `evaluate_decls_swap_locals`
    (`panPropsScript.sml:1645`) over the reviewed finite-support state.
    The finite-map qualifier records the four HOL `|->` fields. The theorem's
    premise and conclusion match HOL: a successful declaration evaluation
    remains successful after replacing `locals`, and the resulting state has
    exactly that replacement. The PanProps proof carrier has a separate Lean
    structure name, so `evaluateDeclsPanPropsHOLFinite_toCanonical` proves a
    field-for-field state codec and equality of complete success/failure
    results with the canonical tagged `PanSemStateFiniteExact.evaluateDeclsHOLFinite`.
    The declaration initializer clause clears locals before evaluating, while
    the other clauses preserve the field. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_locals"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsSwapLocalsHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (locals : HolFiniteMapExact MlS (ValueHOL width)),
      evaluateDeclsPanPropsHOLFinite state program = some result →
        evaluateDeclsPanPropsHOLFinite { state with locals := locals } program =
          some { result with locals := locals } := by
  intro state hstate program result locals hEval
  induction program generalizing state result with
  | nil =>
      simp [evaluateDeclsPanPropsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval ⊢
          exact ih state result hEval
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                let nextState :=
                  { state with globals := state.globals.update (name, value) }
                have htail := ih nextState result hEval
                simpa [evaluateDeclsPanPropsHOLFinite, hshape, heval, nextState]
                  using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [evaluateDeclsPanPropsHOLFinite, condition, hcondition,
              if_pos] at hEval ⊢
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [evaluateDeclsPanPropsHOLFinite, condition, hcondition,
              if_pos] at hEval ⊢
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval
          · simp [evaluateDeclsPanPropsHOLFinite, condition, hcondition] at hEval

/-- Exact finite-support port of HOL `evaluate_decls_swap_memory`
    (`panPropsScript.sml:1750-1763`). It preserves HOL's quantified state,
    declaration list, result state, replacement memory, conjunctive premise,
    and conclusion. The declaration evaluator has a checked `toExact` bridge
    to PanSem's established evaluator; the finite-map qualifier records only
    its four HOL `|->` fields. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memory"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsSwapMemoryHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memory : RiscV.Word width → HolWordLab width),
      (evaluateDeclsPanPropsHOLFinite state program = some result ∧
        (∀ address, state.memaddrs address → state.memory address = memory address)) →
        evaluateDeclsPanPropsHOLFinite { state with memory := memory } program =
          some { result with memory := memory } := by
  intro state hstate program result memory h
  exact evaluateDeclsPanPropsMemorySwap state memory program result h.1 h.2

/-- `OPT_MMAP eval` over the same finite-support carrier. -/
def evalListHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact (by
    simpa [PanPropsEvalStateFiniteExact.toExact] using h)

/-- PanProps proof support that assembles the finite-map `lookup_code` result
    needed by `lookup_code_wf_shape_invariant_step`. The underlying HOL
    `lookup_code_def` is in `panSemScript.sml:458-467`; this helper is untagged
    because it is an invariant-proof wrapper in the PanProps counterpart. -/
def lookupCodeHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (fname : MlS)
    (arguments : List (ValueHOL width)) :
    Option (ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) :=
  match state.code.lookup fname with
  | none => none
  | some (parameters, body, returnShape) =>
      if (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true then
        some (body,
          HolFiniteMapExact.empty.updateList ((parameters.map Prod.fst).zip arguments),
          returnShape)
      else none

/-- Exact port of HOL `panProps$eval_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:126`). The conjunction
    preserves HOL's successful-evaluation, `FEVERY locals`, `FEVERY globals`
    hypothesis order. Finite-map fields use the reviewed canonical
    `HolFiniteMapExact` translation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_is_wf_shape_v"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalIsWfShapeValueHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width),
      state.evalHOL expression = some value ∧
        (∀ name bound, state.locals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) ∧
        (∀ name bound, state.globals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) →
        isWfShapeValueHOLExact state.structs value = true := by
  intro state hdec expression value h
  have hEval := h.1
  have hlocals := h.2.1
  have hglobals := h.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  apply evalHOLExact_isWfShapeValueHOLExact state.toExact hlocals hglobals expression value
  simpa [evalHOL] using hEval

private theorem snd_mem_of_mem_zip {α β : Type} {left : List α} {right : List β}
    {pair : α × β} (h : pair ∈ left.zip right) : pair.2 ∈ right := by
  induction left generalizing right pair with
  | nil => simp at h
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons head' tail' =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with heq | htail
          · cases heq
            simp
          · exact List.mem_cons_of_mem head' (ih htail)

private theorem evalListHOLExact_mem_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (hlocals : ∀ name value, state.locals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (hglobals : ∀ name value, state.globals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true) :
    ∀ expressions values,
      state.evalListHOL expressions = some values →
        ∀ value, value ∈ values → isWfShapeValueHOLExact state.structs value = true := by
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using
      (inferInstance : DecidablePred state.memaddrs)
  intro expressions
  induction expressions with
  | nil =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact [] = some values at hEval
      simp [evalListHOLExact] at hEval
      cases hEval
      simp at hmem
  | cons expression rest ih =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact (expression :: rest) = some values at hEval
      cases hExpression : evalHOLExact state.toExact expression with
      | none => simp [evalListHOLExact, hExpression] at hEval
      | some head =>
          cases hRest : evalListHOLExact state.toExact rest with
          | none => simp [evalListHOLExact, hExpression, hRest] at hEval
          | some tail =>
              have hSomeValues : some (head :: tail) = some values := by
                simpa only [evalListHOLExact, hExpression, hRest] using hEval
              have hValues : head :: tail = values := Option.some.inj hSomeValues
              subst values
              simp only [List.mem_cons] at hmem
              rcases hmem with hHead | hmem
              · subst value
                have hExpressionFinite : state.evalHOL expression = some head := by
                  simpa [evalHOL] using hExpression
                exact evalIsWfShapeValueHOL state expression head
                  ⟨hExpressionFinite, hlocals, hglobals⟩
              · exact ih tail (by simpa [evalListHOL] using hRest) value hmem

/-- HOL `lookup_code_wf_shape_invariant_step` proof dependency: evaluated
    arguments are well-formed, so every value installed into the callee's
    finite locals map is well-formed. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "lookup_code_wf_shape_invariant_step"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem lookupCodeWfShapeInvariantStep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (argexps : List (ExpHOL width)) (args : List (ValueHOL width))
      (fname : MlS) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      state.evalListHOL argexps = some args ∧
        lookupCodeHOLFinite state fname args = some (prog, newlocals, returnShape) ∧
        (∀ name value, state.locals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) ∧
        (∀ name value, state.globals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) →
        (∀ name value, newlocals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) := by
  intro state hdec argexps args fname prog newlocals returnShape h
  have hArgs := h.1
  have hLookup := h.2.1
  have hlocals := h.2.2.1
  have hglobals := h.2.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  cases hCode : state.code.lookup fname with
  | none => simp [lookupCodeHOLFinite, hCode] at hLookup
  | some codeEntry =>
      rcases codeEntry with ⟨parameters, body, declaredReturn⟩
      by_cases hValid : (parameters.map Prod.fst).Nodup ∧
          parameters.length = args.length ∧
          ((parameters.zip args).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
      · have hResult :
            some (body, HolFiniteMapExact.empty.updateList
              ((parameters.map Prod.fst).zip args), declaredReturn) =
              some (prog, newlocals, returnShape) := by
          simpa [lookupCodeHOLFinite, hCode, hValid] using hLookup
        have hTuple := Option.some.inj hResult
        have hMap : HolFiniteMapExact.empty.updateList
            ((parameters.map Prod.fst).zip args) = newlocals :=
          congrArg Prod.fst (congrArg Prod.snd hTuple)
        have hMapLookup := congrArg HolFiniteMapExact.lookup hMap
        intro name value hValue
        have hFold :
            FUPDATE_LIST (FEMPTY : FiniteMap MlS (ValueHOL width))
              ((parameters.map Prod.fst).zip args) name = some value := by
          rw [← hMapLookup] at hValue
          change FUPDATE_LIST (fun _ => none)
            ((parameters.map Prod.fst).zip args) name = some value
          simpa [HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FEMPTY] using hValue
        have hEntries := flookupFupdateList_mem_or_base
          (FEMPTY : FiniteMap MlS (ValueHOL width))
          ((parameters.map Prod.fst).zip args) name value (by
            simpa [FLOOKUP] using hFold)
        rcases hEntries with ⟨entry, hentry, _, hentryValue⟩ | hbase
        · subst value
          exact evalListHOLExact_mem_isWf state hlocals hglobals argexps args hArgs
            entry.2 (snd_mem_of_mem_zip hentry)
        · simp [FLOOKUP, FEMPTY] at hbase
      · have hLookup' := hLookup
        simp [lookupCodeHOLFinite, hCode] at hLookup'
        have hValid' : (parameters.map Prod.fst).Nodup ∧
            parameters.length = args.length ∧
            ((parameters.zip args).all
              (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
          refine ⟨hLookup'.1.1, hLookup'.1.2.1, List.all_eq_true.mpr ?_⟩
          intro pair hpair
          exact hLookup'.1.2.2 pair.1.1 pair.1.2 pair.2 hpair
        exact False.elim (hValid hValid')

/-- Flapjack-specific finite-carrier rendering of HOL's local update
    `s with locals := s.locals |+ (n, w)`. The finite carrier's `locals` field
    is a `HolFiniteMapExact`, so the HOL `FUPDATE` (`|+`) is the
    equality-based `HolFiniteMapExact.updateEq`. Untagged adapter, mirroring
    `emptyLocalsForStructsSimps`. -/
def updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with locals := state.locals.updateEq (name, word) }

/-- Projection of the finite-map local update to the canonical broad
    `FUPDATE_HOL` state. -/
@[simp] theorem updateLocalsForVarsSimps_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width) :
    (updateLocalsForVarsSimps state name word).toExact =
      { state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, word) } := rfl

/-- Updating `locals` changes no other state component, so the address-set
    decision procedure is inherited. -/
instance updateLocalsForVarsSimpsDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width)
    [DecidablePred state.memaddrs] :
    DecidablePred (updateLocalsForVarsSimps state name word).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

/-- Finite-carrier evaluation after `updateLocalsForVarsSimps` is the broad
    exact evaluation over the canonical `FUPDATE_HOL` state. -/
@[simp] theorem evalHOL_updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) (expression : ExpHOL width) :
    (updateLocalsForVarsSimps state name word).evalHOL expression =
      @evalHOLExact width σ _ { state.toExact with
        locals := FUPDATE_HOL state.toExact.locals (name, word) } h expression := rfl

/-- Finite-carrier `OPT_MMAP eval` after `updateLocalsForVarsSimps` is the broad
    exact list step over the canonical `FUPDATE_HOL` state. -/
@[simp] theorem evalListHOL_updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) (expressions : List (ExpHOL width)) :
    (updateLocalsForVarsSimps state name word).evalListHOL expressions =
      @evalListHOLExact width σ _ { state.toExact with
        locals := FUPDATE_HOL state.toExact.locals (name, word) } h expressions := rfl

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1042`): binding a fresh local
    name `n` to `w` leaves `eval e` unchanged when `n` does not occur in
    `var_exp e`. The quantifier order is HOL's `s e v n w`; HOL's `v` does not
    occur in the hypothesis or conclusion, so HOL type inference gives it a
    fresh independent type variable (distinct from the locals value type of the
    live `w`), and the Lean statement binds it fully polymorphically as
    `{β : Type} (_value : β)`. The
    state is the reviewed PanProps finite-map carrier: `updateLocalsForVarsSimps`
    renders HOL's `locals |+ (n, w)` through `HolFiniteMapExact.updateEq`, and
    `evalHOL` delegates to the exact broad evaluator through `toExact`. The four
    `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the reviewed
    canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier (canonical witness
    `holFmapAsFiniteSupportWitness` in this module). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem updateLocalsNotVarsEvalEqEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) {β : Type} (_value : β) (name : MlS)
      (word : ValueHOL width),
      name ∉ varExpHOL expression →
        (updateLocalsForVarsSimps state name word).evalHOL expression = state.evalHOL expression := by
  intro state hdec expression β _value name word h
  rw [evalHOL_updateLocalsForVarsSimps]
  exact evalHOLExact_updLocals_not_mem state.toExact name word expression h

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1060`): a fresh local binding
    preserves a successful evaluation and its value. Quantifier order is HOL's
    `s e v n w`; the fresh-name premise and the `SOME`-success hypothesis are
    conjoined as in the source. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem updateLocalsNotVarsEvalEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width) (name : MlS)
      (word : ValueHOL width),
      (name ∉ varExpHOL expression ∧ state.evalHOL expression = some value) →
        (updateLocalsForVarsSimps state name word).evalHOL expression = some value := by
  intro state hdec expression value name word h
  rw [updateLocalsNotVarsEvalEqEqHOLFinite state expression value name word h.1, h.2]

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq_NONE`
    (`cakeml/pancake/semantics/panPropsScript.sml:1069`): a fresh local binding
    preserves a failing evaluation. Quantifier order is HOL's `s e v n w`; as in
    the source, the dead `v` gets a fresh independent HOL type variable and is
    bound fully polymorphically as `{β : Type} (_value : β)`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_NONE"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem updateLocalsNotVarsEvalEqNoneHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) {β : Type} (_value : β) (name : MlS)
      (word : ValueHOL width),
      (name ∉ varExpHOL expression ∧ state.evalHOL expression = none) →
        (updateLocalsForVarsSimps state name word).evalHOL expression = none := by
  intro state hdec expression β _value name word h
  rw [updateLocalsNotVarsEvalEqEqHOLFinite state expression _value name word h.1, h.2]

/-- Exact finite-support port of HOL `panProps$eval_fresh_var`
    (`cakeml/pancake/semantics/panPropsScript.sml:1078`): binding an absent name
    to any word leaves evaluation unchanged. Same content as
    `updateLocalsNotVarsEvalEqEqHOLFinite` with HOL's dead `v` dropped, matching
    the source's `s e n w` quantifier list. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_fresh_var"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalFreshVarHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (name : MlS) (word : ValueHOL width),
      name ∉ varExpHOL expression →
        (updateLocalsForVarsSimps state name word).evalHOL expression = state.evalHOL expression := by
  intro state hdec expression name word h
  rw [evalHOL_updateLocalsForVarsSimps]
  exact evalHOLExact_updLocals_not_mem state.toExact name word expression h

/-- Exact finite-support port of HOL
    `panProps$OPT_MMAP_update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1088`): a fresh local binding
    preserves a successful `OPT_MMAP (eval ·)` over a list of expressions.
    `evalListHOL` is the repository's exact `OPT_MMAP` rendering over the
    finite-support carrier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem optMmapUpdateLocalsNotVarsEvalEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expressions : List (ExpHOL width)) (values : List (ValueHOL width)) (name : MlS)
      (word : ValueHOL width),
      (name ∉ (expressions.map varExpHOL).flatten ∧
        state.evalListHOL expressions = some values) →
        (updateLocalsForVarsSimps state name word).evalListHOL expressions = some values := by
  intro state hdec expressions values name word h
  rw [evalListHOL_updateLocalsForVarsSimps,
    evalListHOLExact_updLocals_not_mem state.toExact name word expressions h.1]
  exact h.2

/-! ## HOL `evaluate_decls_functions`, `evaluate_decls_eshapes`,
    `evaluate_decls_only_functions`

The ports below inspect only the final state's `code`/`eshapes` (or the whole
final state under an `EVERY is_function` premise); none of them evaluates a
declaration in an abstract result state, so each is stated over the reviewed
finite-map carrier exactly as its HOL source. -/

/-- `|++` after `|+` is `|++` with the entry prepended (`FUPDATE_LIST_cons` on
    the finite-support carrier). Untagged finite-map helper. -/
private theorem updateList_cons {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  rfl

/-- `|++` of the empty list is the identity (`FUPDATE_LIST_nil` on the
    finite-support carrier). Untagged finite-map helper. -/
private theorem updateList_nil {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) : map.updateList [] = map := by
  apply HolFiniteMapExact.ext
  rfl

/-- Exact finite-support port of HOL `panProps$evaluate_decls_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1518`):
    `evaluate_decls s pan_code = SOME s' ==> s'.code = s.code |++ functions
    pan_code`. The quantifier order `s pan_code s'`, the successful-evaluation
    premise, and the code conclusion follow the source. `functionsHOL` is the
    reviewed word-indexed `functions` port and `HolFiniteMapExact.updateList` is
    the canonical finite-support rendering of HOL `|++`. The four `|->` fields
    (`locals`, `globals`, `code`, `eshapes`) are the reviewed canonical
    `HolFiniteMapExact` translation recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness`). `[NeZero
    width]` models HOL's positive word dimension and `DecidablePred
    state.memaddrs` is computation evidence for the HOL word-set guard.

    PanProps-counterpart exact port (bead flapjack-4ac.4.84, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_functions"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsFunctionsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsHOLFinite state program = some result →
        result.code = state.code.updateList (functionsHOL program) := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result hEval
      injection hEval with hEq
      subst hEq
      simp [functionsHOL, updateList_nil]
  | cons declaration rest ih =>
      intro result hEval
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          simpa [functionsHOL] using ih state result hEval
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have htail := ih
                  { state with globals := state.globals.update (name, value) } result hEval
                simpa [functionsHOL] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) } result hEval
            rw [htail]
            simp [functionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) } result hEval
            simpa [functionsHOL] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval

/-- Exact finite-support port of HOL `panProps$evaluate_decls_eshapes`
    (`cakeml/pancake/semantics/panPropsScript.sml:1409`):
    `evaluate_decls s ds = SOME s' ==> s'.eshapes = s.eshapes |++ exceptions
    ds`. Quantifier order, premise, and conclusion follow the source;
    `exceptionsHOL` is the reviewed `exceptions` port and
    `HolFiniteMapExact.updateList` renders HOL `|++`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.75, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_eshapes"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsEshapesHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsHOLFinite state program = some result →
        result.eshapes = state.eshapes.updateList (exceptionsHOL program) := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result hEval
      injection hEval with hEq
      subst hEq
      simp [exceptionsHOL, updateList_nil]
  | cons declaration rest ih =>
      intro result hEval
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          simpa [exceptionsHOL] using ih state result hEval
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have htail := ih
                  { state with globals := state.globals.update (name, value) } result hEval
                simpa [exceptionsHOL] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) } result hEval
            simpa [exceptionsHOL] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) } result hEval
            rw [htail]
            simp [exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval

/-- Exact finite-support port of HOL `panProps$evaluate_decls_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1528`): under `EVERY
    is_function pan_code`, a successful declaration evaluation changes only
    `code`, appending the function entries. The premise is rendered as `program.all
    isFunctionHOL = true`, the exact `EVERY is_function` reading over the
    reviewed `DeclHOL` carrier; the conclusion is HOL's record update with
    `|++`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.85, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_functions"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsOnlyFunctionsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all isFunctionHOL = true →
      evaluateDeclsPanPropsHOLFinite state program = some result →
        result = { state with code := state.code.updateList (functionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show functionsHOL ([] : List (DeclHOL width)) = [] from rfl, updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | function declaration =>
          simp only [List.all_cons, isFunctionHOL, Bool.true_and] at hall
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])
      | decl shape name expression =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])
      | exnDecl exceptionName shape =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])

section
open Classical

/-- Exact finite-support port of HOL `panProps$evaluate_decls_append`
    (`cakeml/pancake/semantics/panPropsScript.sml:1540`): evaluating `ds1 ++ ds2`
    is the monadic bind of evaluating `ds1` and then `ds2` in the resulting
    state. HOL's `case ... of NONE => NONE | SOME s' => ...` is rendered as
    `Option.bind`. The finite-map qualifier records only the four HOL `|->`
    fields. The nested evaluation on HOL's existential result state uses Lean's
    classical decidability for the `memaddrs` word-set guard; `Decidable`
    instances are subsingleton, so this adds no side condition and does not
    change the evaluator's value relative to HOL's total classical logic.

    PanProps-counterpart exact port (bead flapjack-4ac.4.86, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_append"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsAppendHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) (ds1 ds2 : List (DeclHOL width)),
      evaluateDeclsPanPropsHOLFinite state (ds1 ++ ds2) =
        Option.bind (evaluateDeclsPanPropsHOLFinite state ds1)
          (fun state' => evaluateDeclsPanPropsHOLFinite state' ds2) := by
  intro state ds1 ds2
  induction ds1 generalizing state with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [List.cons_append, evaluateDeclsPanPropsHOLFinite]
          exact ih state
      | decl shape name expression =>
          simp only [List.cons_append, evaluateDeclsPanPropsHOLFinite]
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => rfl
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [if_pos hshape]
                exact ih { state with globals := state.globals.update (name, value) }
              · simp [hshape]
      | function declaration =>
          simp only [List.cons_append, evaluateDeclsPanPropsHOLFinite]
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]
      | exnDecl exceptionName shape =>
          simp only [List.cons_append, evaluateDeclsPanPropsHOLFinite]
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]

end

/-! ## HOL `evaluate_decls_exns_wf`, `evaluate_decls_only_exn_decls`,
    `exns_wf_evaluate_decls`, `evaluate_decls_only_funs_and_exn_decls`

The four ports below prove properties of the final exception table (and, for the
last, the final exception table and code) under evaluation; none evaluates a
declaration in an abstract result state, so each is stated over the reviewed
finite-map carrier exactly as its HOL source. -/

/-- `lookup` after a single `update` at a distinct key is unchanged
    (`FLOOKUP_UPDATE` on the finite-support carrier). Untagged finite-map
    helper. -/
private theorem lookup_update_ne {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) (key : α)
    (h : entry.1 ≠ key) :
    (map.update entry).lookup key = map.lookup key := by
  simp only [HolFiniteMapExact.lookup_update, FUPDATE, beq_eq_false_iff_ne.mpr h,
    Bool.false_eq_true, if_false]

/-- Tail freshness survives prepending a distinct exception binding. Untagged
    finite-map helper. -/
private theorem all_isNone_update_forward {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hne : name ∉ entries.map Prod.fst)
    (hfresh : entries.all (fun entry => (state.eshapes.lookup entry.1).isNone) = true) :
    entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true := by
  rw [List.all_eq_true] at hfresh ⊢
  intro entry hentry
  have hkey : name ≠ entry.1 := by
    intro h
    exact hne (List.mem_map.mpr ⟨entry, hentry, h.symm⟩)
  rw [lookup_update_ne state.eshapes (name, shape) entry.1 hkey]
  exact hfresh entry hentry

/-- Tail freshness about the updated table implies freshness about the original
    table when the prepended key is absent from the tail. Untagged finite-map
    helper. -/
private theorem all_isNone_update_backward {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hne : name ∉ entries.map Prod.fst)
    (hfresh : entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true) :
    entries.all (fun entry => (state.eshapes.lookup entry.1).isNone) = true := by
  rw [List.all_eq_true] at hfresh ⊢
  intro entry hentry
  have hkey : name ≠ entry.1 := by
    intro h
    exact hne (List.mem_map.mpr ⟨entry, hentry, h.symm⟩)
  have h := hfresh entry hentry
  rw [lookup_update_ne state.eshapes (name, shape) entry.1 hkey] at h
  exact h

/-- A key freshly bound in the exception table cannot occur in the tail update
    list when the tail is fresh for the updated table. Untagged finite-map
    helper. -/
private theorem notMem_fst_of_all_isNone_update {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hfresh : entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true) :
    name ∉ entries.map Prod.fst := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨entry, hentry, hkey⟩ := hmem
  rw [List.all_eq_true] at hfresh
  have hlook := hfresh entry hentry
  have hsome : ((state.eshapes.update (name, shape)).lookup name).isNone = true := by
    simpa [hkey] using hlook
  have hval : (state.eshapes.update (name, shape)).lookup name = some shape := by
    rw [HolFiniteMapExact.lookup_update, FUPDATE]
    simp
  rw [hval] at hsome
  simp at hsome

/-- Exact finite-support port of HOL `panProps$evaluate_decls_only_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1436`): if every declaration is
    an exception declaration, a successful evaluation leaves the whole state
    unchanged except for the exception table, which becomes
    `s.eshapes |++ exceptions ds`. Quantifier order `s ds s'`, the
    `EVERY is_exn_decl` premise rendered as `program.all isExnDeclHOL = true`,
    the successful-evaluation premise, and HOL's record update with
    `exceptionsHOL` follow the source.

    PanProps-counterpart exact port (bead flapjack-4ac.4.77, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_exn_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsOnlyExnDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all isExnDeclHOL = true →
      evaluateDeclsPanPropsHOLFinite state program = some result →
        result = { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show exceptionsHOL ([] : List (DeclHOL width)) = [] from rfl, updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isExnDeclHOL, Bool.true_and] at hall
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hall hEval
            rw [htail]
            simp [exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])

/-- Exact finite-support port of HOL `panProps$evaluate_decls_exns_wf`
    (`cakeml/pancake/semantics/panPropsScript.sml:1419`): a successful declaration
    evaluation guarantees that the exception ids are all distinct, that every
    exception shape is absent from the original exception table, and that every
    exception shape is well formed in the original structure context. HOL's
    `s'` is used by the success hypothesis, so it is retained.
    `ALL_DISTINCT (MAP FST ...)` is rendered as `Nodup` of the projected id
    list; `FLOOKUP s.eshapes eid = NONE` as the Bool `... .isNone = true`, the
    same key comparison the evaluator's own guard performs; and
    `is_wf_shape s.structs` as the tagged `isWfShapeExactHOL`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.76, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_exns_wf"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsExnsWfHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsHOLFinite state program = some result →
        ((exceptionsHOL program).map Prod.fst).Nodup ∧
        (exceptionsHOL program).all
          (fun entry => (state.eshapes.lookup entry.1).isNone) = true ∧
        (exceptionsHOL program).all
          (fun entry => isWfShapeExactHOL state.structs entry.2) = true := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result hEval
      simp [exceptionsHOL]
  | cons declaration rest ih =>
      intro result hEval
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have hcondRaw : ((state.eshapes.lookup exceptionName).isNone &&
                isWfShapeExactHOL state.structs shape) = true := by
              simpa [condition] using hcondition
            rw [Bool.and_eq_true] at hcondRaw
            obtain ⟨hfreshHead, hwfHead⟩ := hcondRaw
            have hih := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval
            obtain ⟨hnodupTail, hfreshTail, hwfTail⟩ := hih
            refine ⟨?_, ?_, ?_⟩
            · rw [exceptionsHOL, List.map_cons, List.nodup_cons]
              exact ⟨notMem_fst_of_all_isNone_update state exceptionName shape
                (exceptionsHOL rest) hfreshTail, hnodupTail⟩
            · rw [exceptionsHOL, List.all_cons, Bool.and_eq_true]
              exact ⟨hfreshHead, all_isNone_update_backward state exceptionName shape
                (exceptionsHOL rest)
                (notMem_fst_of_all_isNone_update state exceptionName shape
                  (exceptionsHOL rest) hfreshTail) hfreshTail⟩
            · rw [exceptionsHOL, List.all_cons, Bool.and_eq_true]
              exact ⟨hwfHead, by simpa using hwfTail⟩
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          simpa [exceptionsHOL] using ih state result hEval
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          cases heval : evalHOL { state with locals := HolFiniteMapExact.empty } expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have htail := ih
                  { state with globals := state.globals.update (name, value) } result hEval
                simpa [exceptionsHOL] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval
            simpa [exceptionsHOL] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval

/-- Exact finite-support port of HOL `panProps$exns_wf_evaluate_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1448`): the converse
    characterization. Under `EVERY is_exn_decl ds` together with the three
    well-formedness conditions (distinct ids, ids absent from the table,
    well-formed shapes), the evaluation succeeds and yields exactly the state
    with the exception table updated by `exceptions ds`. Premises are rendered
    with the same Bool `all`/`isNone`/`isWfShapeExactHOL` vocabulary as
    `evaluateDeclsExnsWfHOLFinite`. The quantifier order is HOL's `s ds s'`;
    HOL's `s'` does not occur in any hypothesis or in the conclusion, so HOL
    type inference gives it a fresh independent type variable, and the Lean
    statement binds it fully polymorphically as `{γ : Type} (_result : γ)`
    rather than at the narrowed state type.

    PanProps-counterpart exact port (bead flapjack-4ac.4.78, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "exns_wf_evaluate_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem exnsWfEvaluateDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) {γ : Type} (_result : γ),
      program.all isExnDeclHOL = true →
      ((exceptionsHOL program).map Prod.fst).Nodup →
      (exceptionsHOL program).all
        (fun entry => (state.eshapes.lookup entry.1).isNone) = true →
      (exceptionsHOL program).all
        (fun entry => isWfShapeExactHOL state.structs entry.2) = true →
      evaluateDeclsPanPropsHOLFinite state program =
        some { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro γ _result _ _ _ _
      rfl
  | cons declaration rest ih =>
      intro γ _result hall hnodup hfresh hwf
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isExnDeclHOL, Bool.true_and] at hall
          rw [exceptionsHOL] at hnodup hfresh hwf
          rw [List.map_cons, List.nodup_cons] at hnodup
          rw [List.all_cons, Bool.and_eq_true] at hfresh
          rw [List.all_cons, Bool.and_eq_true] at hwf
          obtain ⟨hnotmem, hnodupTail⟩ := hnodup
          obtain ⟨hfreshHead, hfreshTail⟩ := hfresh
          obtain ⟨hwfHead, hwfTail⟩ := hwf
          have hcondition : ((state.eshapes.lookup exceptionName).isNone &&
              isWfShapeExactHOL state.structs shape) = true := by
            rw [Bool.and_eq_true]
            exact ⟨hfreshHead, hwfHead⟩
          simp only [evaluateDeclsPanPropsHOLFinite, if_pos hcondition]
          have htail := ih
            { state with eshapes := state.eshapes.update (exceptionName, shape) }
            _result hall hnodupTail
            (all_isNone_update_forward state exceptionName shape (exceptionsHOL rest)
              hnotmem hfreshTail)
            (by simpa using hwfTail)
          rw [htail]
          simp [exceptionsHOL, updateList_cons]
      | name name fields =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | decl shape name expression =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | function declaration =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])

/-- Exact finite-support port of HOL
    `panProps$evaluate_decls_only_funs_and_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1561`): under
    `EVERY (λd. is_function d ∨ is_exn_decl d) ds`, a successful evaluation
    changes only `code` and `eshapes`, appending `functions ds` and
    `exceptions ds`. The premise is rendered as the Bool
    `program.all (fun d => isFunctionHOL d || isExnDeclHOL d) = true`, the exact
    `EVERY` disjunction over the reviewed `DeclHOL` carrier, and the conclusion
    is HOL's two-field record update with `|++` on both maps.

    PanProps-counterpart exact port (bead flapjack-4ac.4.88, audit
    flapjack-4ac.6). The PanProps finite evaluator
    `evaluateDeclsPanPropsHOLFinite` is kernel-bridged to the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` by
    `evaluateDeclsPanPropsHOLFinite_toCanonical` (via the field-for-field state
    codec `toPanSemFinite`), so this invariant is about the canonical evaluator.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_funs_and_exn_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsOnlyFunsAndExnDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all
        (fun declaration => isFunctionHOL declaration || isExnDeclHOL declaration) = true →
      evaluateDeclsPanPropsHOLFinite state program = some result →
        result = { state with
          code := state.code.updateList (functionsHOL program)
          eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show functionsHOL ([] : List (DeclHOL width)) = [] from rfl,
        show exceptionsHOL ([] : List (DeclHOL width)) = [] from rfl]
      rw [updateList_nil, updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | function declaration =>
          simp only [List.all_cons, isFunctionHOL, isExnDeclHOL, Bool.true_or,
            Bool.true_and] at hall
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isFunctionHOL, isExnDeclHOL, Bool.false_or,
            Bool.true_and] at hall
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isFunctionHOL, isExnDeclHOL])
      | decl shape name expression =>
          simp only [evaluateDeclsPanPropsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isFunctionHOL, isExnDeclHOL])
set_option linter.unusedSimpArgs false in
/-- Exact finite-support port of HOL `panProps$evaluate_decls_names`
    (`cakeml/pancake/semantics/panPropsScript.sml:1552`):
    `!s decs. EVERY is_name decs ==> evaluate_decls s decs = SOME s`.
    HOL `EVERY is_name decs` renders as `decs.all isNameHOL = true` (the tagged
    `is_name_def` counterpart), and the state is the PanProps counterpart
    carrier `PanPropsEvalStateFiniteExact`, whose four `|->` fields (`locals`,
    `globals`, `code`, `eshapes`) are the reviewed canonical
    `HolFiniteMapExact` translation recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness` in this
    module). The PanProps proof carrier has a separate Lean structure name, so
    `evaluateDeclsPanPropsHOLFinite_toCanonical` proves a field-for-field state
    codec together with equality of complete success/failure results to the
    canonical tagged `PanSemStateFiniteExact.evaluateDeclsHOLFinite`; the
    PanProps statement is therefore about the canonical evaluator rather than a
    similar duplicate (coordinator HOLD 2026-09-26T16:46Z resolved by
    `flapjack-lqws`). `[NeZero width]` models HOL's positive word dimension and
    `DecidablePred state.memaddrs` is computation evidence for the HOL word-set
    guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_names"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsNamesHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (decs : List (DeclHOL width)) :
    decs.all (fun declaration => Flapjack.Pancake.PanLang.isNameHOL declaration) = true →
      evaluateDeclsPanPropsHOLFinite state decs = some state := by
  induction decs generalizing state with
  | nil => intro _; rfl
  | cons declaration rest ih =>
      intro hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hd, hrest⟩ := hall
      cases declaration with
      | name name fields =>
          simp only [evaluateDeclsPanPropsHOLFinite]
          exact ih state hrest
      | decl shape name expression =>
          rw [show Flapjack.Pancake.PanLang.isNameHOL
            (DeclHOL.decl shape name expression) = false from rfl] at hd
          exact (Bool.false_eq_true.mp hd).elim
      | function declaration =>
          rw [show Flapjack.Pancake.PanLang.isNameHOL
            (DeclHOL.function declaration) = false from rfl] at hd
          exact (Bool.false_eq_true.mp hd).elim
      | exnDecl exceptionName shape =>
          rw [show Flapjack.Pancake.PanLang.isNameHOL
            (DeclHOL.exnDecl exceptionName shape) = false from rfl] at hd
          exact (Bool.false_eq_true.mp hd).elim

/-- The PanProps finite-support `toPanSemFinite` codec is injective: its
    left inverse is `ofPanSemFinite`. Infrastructure for transporting canonical
    PanSem declarations back to the PanProps counterpart carrier. -/
theorem toPanSemFinite_injective {width : Nat} {σ : Type} [NeZero width] :
    Function.Injective (@toPanSemFinite width σ _) := by
  intro a b h
  have := congrArg ofPanSemFinite h
  simpa using this

/-- Injectivity of `Option.map toPanSemFinite`, used to transport a canonical
    `Option`-valued equation back to the PanProps carrier. -/
theorem optionMapToPanSemFinite_injective {width : Nat} {σ : Type} [NeZero width]
    {a b : Option (PanPropsEvalStateFiniteExact width σ)} :
    a.map toPanSemFinite = b.map toPanSemFinite → a = b := by
  intro h
  cases a with
  | none => cases b <;> simp_all
  | some x =>
      cases b with
      | none => simp_all
      | some y =>
          simp only [Option.map_some, Option.some.injEq] at h
          exact congrArg some (toPanSemFinite_injective h)

/-- Exact finite-support port of HOL `panProps$evaluate_decl_commute`
    (`cakeml/pancake/semantics/panPropsScript.sml:1472-1480`):
    `!s fi sh v' e ds. evaluate_decls s (Function fi::Decl sh v' e::ds) =
    evaluate_decls s (Decl sh v' e::Function fi::ds)`. Swapping an adjacent
    `Function`/`Decl` declaration leaves the evaluator unchanged because `Decl`
    clears the locals and updates only `globals`, while `Function` updates only
    `code` and the evaluator does not read `code`. The state is the PanProps
    counterpart carrier over the reviewed canonical `HolFiniteMapExact`
    translation (canonical witness `holFmapAsFiniteSupportWitness` in this
    module). This is stated over `evaluateDeclsPanPropsHOLFinite`, but the
    kernel codec `evaluateDeclsPanPropsHOLFinite_toCanonical` transports the
    canonical tagged PanSem `evaluateDeclsHOLFinite` equation back through the
    injective `toPanSemFinite`/`ofPanSemFinite` roundtrip, so it is about the
    canonical evaluator rather than a similar duplicate (coordinator HOLD
    2026-09-26T16:46Z resolved by `flapjack-lqws`). `[NeZero width]` models
    HOL's positive word dimension and `DecidablePred state.memaddrs` is
    computation evidence for the HOL word-set guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decl_commute"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evaluateDeclsDeclCommuteHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fi : FunDeclHOL width) (sh : ShapeHOL) (v' : MlS) (e : ExpHOL width)
    (ds : List (DeclHOL width)) :
    evaluateDeclsPanPropsHOLFinite state (.function fi :: .decl sh v' e :: ds)
      = evaluateDeclsPanPropsHOLFinite state (.decl sh v' e :: .function fi :: ds) := by
  letI : DecidablePred state.toPanSemFinite.memaddrs := toPanSemFiniteDecidableMemaddrs state
  have hcanon := PanSemStateFiniteExact.evaluateDeclsHOLFinite_declCommute
    state.toPanSemFinite fi sh v' e ds
  rw [← evaluateDeclsPanPropsHOLFinite_toCanonical state,
    ← evaluateDeclsPanPropsHOLFinite_toCanonical state] at hcanon
  exact optionMapToPanSemFinite_injective hcanon

end PanPropsEvalStateFiniteExact

end Flapjack
