import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.PanValueFlatten
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL

/-!
HOL counterpart module for `cakeml/pancake/semantics/panPropsScript.sml`.
The full generated semantic property library is not yet present; this module
starts with the value-well-formedness definition used by PanStructs
`compile_correct`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-! Equality-based first-match lookup for HOL `ALOOKUP` expressions. Lean's
    production `lookupInfo` intentionally takes `[BEq κ]`; this version keeps
    the HOL equality semantics explicit. -/
def panPropsALookupEq [DecidableEq κ] (key : κ) : List (κ × α) → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if decide (candidate = key) then some value else panPropsALookupEq key entries

theorem panPropsALookupEq_mapValues [DecidableEq κ] (key : κ)
    (entries : List (κ × α)) (convert : α → β) :
    panPropsALookupEq key (entries.map fun (name, value) => (name, convert value)) =
      (panPropsALookupEq key entries).map convert := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨name, value⟩
      by_cases hname : name = key
      · simp [panPropsALookupEq, hname]
      · simp [panPropsALookupEq, hname, ih]

theorem lookupInfo_eq_panPropsALookupEq [BEq κ] [LawfulBEq κ] [DecidableEq κ] (key : κ)
    (entries : List (κ × α)) :
    lookupInfo key entries = panPropsALookupEq key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨name, value⟩
      by_cases hname : name = key
      · simp [lookupInfo, panPropsALookupEq, hname]
      · simp [lookupInfo, panPropsALookupEq, hname, ih]

mutual
  /-- Bool-valued comparison for HOL `is_wf_shape_v_def`, using production
      `lookupInfo`. This is not currently tagged as an exact port: the HOL
      predicate uses HOL equality in `ALOOKUP`, while this declaration's
      lookup semantics are selected by `[BEq String]`; the equality adapter
      lemma only identifies lookup for lawful instances and does not establish
      that the production representation is the same HOL interface. Lean
      `StructInfo` also has an additional `shapedFields` cache absent from HOL.
      The separate Prop-valued convenience predicate in CompileCorrect is
      further from the HOL Bool statement.

      Executable-path disposition (bead `flapjack-4ac.4.4.1`): this value-level
      predicate has no call site on the executable compiler path. The RISC-V
      entrypoints (`compileFlapjackRiscVSourceRuntimeImageChecked` and siblings
      in `Flapjack/RiscV/PipelineDiagnostics.lean`) run `staticCheck`
      (`Flapjack/Pancake/PanStatic.lean:1794`), which checks declared shapes
      (`isWfShape`/`checkShape`/`shapedBased...`), not runtime value validity.
      `panIsWfShapeValueBool` occurs only as a proof-side precondition
      (`panStructEveryValueShapeWfBool`,
      `Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean:614`) over
      locals/globals, and the kernel-checked `panIsWfShapeValueHOL_toHOL`
      already connects it to the HOL-shaped `panIsWfShapeValueHOL`. The
      remaining gap to the exact `isWfShapeValueHOLExact` is the carrier
      (`String`/`StructContextHOL` vs `MlStringHOL`/`StructContextExact`),
      tracked by bead `flapjack-pxn.18.3.5.8`.

      The HOL side is also proof-only: a repository-wide search of the
      read-only CakeML/Pancake sources finds `panProps$is_wf_shape_v` only in
      `cakeml/pancake/semantics/panPropsScript.sml` (its own definition and
      proof lemmas such as `is_wf_shape_of_v`, `mem_load_is_wf_shape_v`,
      `eval_is_wf_shape_v`, `pan_primop_is_wf_shape_v`) and in
      `cakeml/pancake/proofs/*ProofScript.sml`; no executable Pancake compile
      script (`pan_to_crepScript.sml`, `pan_globalsScript.sml`, ...) calls it.
      So there is no production call site on the HOL side either, and this
      child bead is closed as a documented no-production-callsite disposition;
      the exact tagged port `isWfShapeValueHOLExact` remains `reviewed_exact`. -/
  def panIsWfShapeValueBool (structs : StructContext) : PanValue α → Bool
    | .word _ => true
    | .rStruct values => panIsWfShapeValuesBool structs values
    | .nStruct name fields =>
        (lookupInfo name structs).isSome &&
          panIsWfShapeValueFieldsBool structs fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panIsWfShapeValuesBool (structs : StructContext) : List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panIsWfShapeValueBool structs value && panIsWfShapeValuesBool structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panIsWfShapeValueFieldsBool (structs : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panIsWfShapeValueBool structs value && panIsWfShapeValueFieldsBool structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! ## Exact `is_wf_shape_v` over the exact `ValueHOL`/`StructContextExact`
    carriers

HOL `panProps$is_wf_shape_v` (`cakeml/pancake/semantics/panPropsScript.sml:24-34`)
is total over the exact `v` datatype (`panSemScript.sml:22`) and a
`(stcname # struct_info) list` context, where `stcname = fldname = mlstring`.
The production `panIsWfShapeValueHOL`/`panIsWfShapeValueBool` above use the
`String`-keyed production carriers, so they are not exact.  `ValueHOL width`
(`PanSem/ValueHOL.lean`, tagged `v`) and `StructContextExact`
(`PanLang/Decl.lean`) are the exact carriers, with `structContextLookupHOL` the
first-match `ALOOKUP` and `isWfShapeValuesHOLExact` the `EVERY` fold.  Direct
original-HOL rows are pinned in `scripts/hol-probes/pan_structs_value_validity_probe.out`
and reproduced by `Flapjack/Test/PanStructsValueValidityParity.lean`. -/

/-- The `MAP SND` view of an exact field list does not increase `sizeOf`. -/
theorem sizeOfValueHOLMapSndLe {width : Nat} [NeZero width]
    (fields : List (MlStringHOL × ValueHOL width)) :
    sizeOf (fields.map Prod.snd) ≤ sizeOf fields := by
  induction fields with
  | nil => simp
  | cons pair pairs ih =>
      obtain ⟨name, value⟩ := pair
      simp only [List.map_cons]
      simp
      omega

/-- The exact field list is strictly smaller than the enclosing `NStruct`
    value. -/
theorem sizeOfValueHOLFieldsLtNStruct {width : Nat} [NeZero width]
    (name : MlStringHOL) (fields : List (MlStringHOL × ValueHOL width)) :
    sizeOf fields < sizeOf (.nStruct name fields : ValueHOL width) := by
  simp
  omega

/-! Exact port of HOL `panProps$is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:24-34`):
    `is_wf_shape_v sctxt (Val v) = T`,
    `is_wf_shape_v sctxt (RStruct vs) = EVERY (is_wf_shape_v sctxt) vs`,
    `is_wf_shape_v sctxt (NStruct nm nm_vs) =`
    `(ALOOKUP sctxt nm <> NONE) /\ EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`.
    Over the exact `ValueHOL width` value carrier and the exact MlString-keyed
    `StructContextExact` context. -/
mutual
  /-- Exact port of HOL `panProps$is_wf_shape_v`.  `structContextLookupHOL` is
      `ALOOKUP`, `isSome` is the Bool rendering of `<> NONE`, and
      `isWfShapeValuesHOLExact` is the `EVERY` fold over `MAP SND`. -/
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def"]
  def isWfShapeValueHOLExact {width : Nat} [NeZero width]
      (context : Flapjack.Pancake.PanLang.StructContextExact) : ValueHOL width → Bool
    | .val _ => true
    | .rStruct values => isWfShapeValuesHOLExact context values
    | .nStruct name fields =>
        (Flapjack.Pancake.PanLang.structContextLookupHOL name context).isSome &&
          isWfShapeValuesHOLExact context (fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by
    all_goals first
      | sizeOf_list_dec
      | decreasing_trivial
      | (have h := sizeOfValueHOLMapSndLe fields
         have h2 := sizeOfValueHOLFieldsLtNStruct name fields
         omega)

  /- `EVERY (is_wf_shape_v sctxt) vs` over an exact value list. -/
  def isWfShapeValuesHOLExact {width : Nat} [NeZero width]
      (context : Flapjack.Pancake.PanLang.StructContextExact) : List (ValueHOL width) → Bool
    | [] => true
    | value :: values =>
        isWfShapeValueHOLExact context value && isWfShapeValuesHOLExact context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Untagged support: the exact value-level well-formedness predicate implies
    that the exact `shape_of` image is well-formed (`is_wf_shape_of_v`
    `panPropsScript.sml:38`). -/
private theorem isWfShapeValueHOLExact_shapeOf_val {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width) :
    isWfShapeValueHOLExact context value = true →
      Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) = true := by
  induction value using isWfShapeValueHOLExact.induct
    (motive2 := fun values =>
      isWfShapeValuesHOLExact context values = true →
        Flapjack.Pancake.PanLang.isWfShapesExactHOL context (values.map shapeOfHOLExact) = true) with
  | case1 value =>
      simp [shapeOfHOLExact]
  | case2 values ih =>
      intro h
      simp only [isWfShapeValueHOLExact.eq_2] at h
      simpa [shapeOfHOLExact, Flapjack.Pancake.PanLang.isWfShapeExactHOL] using ih h
  | case3 name fields _ =>
      simp only [isWfShapeValueHOLExact.eq_3, Bool.and_eq_true]
      intro h
      simpa [shapeOfHOLExact, Flapjack.Pancake.PanLang.isWfShapeExactHOL] using h.1
  | case4 =>
      rfl
  | case5 value values ihValue ihValues =>
      rename_i h
      have hp : isWfShapeValueHOLExact context value = true ∧
          isWfShapeValuesHOLExact context values = true := by
        simpa [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true] using h
      simp only [List.map_cons, Flapjack.Pancake.PanLang.isWfShapesExactHOL.eq_2,
        Bool.and_eq_true]
      exact ⟨ihValue hp.1, ihValues hp.2⟩

/-- Exact port of HOL `panProps$is_wf_shape_of_v`
    (`panPropsScript.sml:38`): `!sctxt v. is_wf_shape_v sctxt v ==>
    is_wf_shape sctxt (shape_of v)`, over the exact `ValueHOL width` value
    carrier and MlString-keyed `StructContextExact` context.  The Bool-valued
    predicates are rendered as `= true`, matching the accepted
    `flattenHOL_length_eq_sizeOfShapeHOL` style; no extra hypotheses. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_of_v"]
theorem isWfShapeValueHOLExact_shapeOfHOLExact {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width)
    (h : isWfShapeValueHOLExact context value = true) :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) = true :=
  isWfShapeValueHOLExact_shapeOf_val context value h

/-- Exact port of HOL `panProps$pan_primop_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:162`):
    `!sctxt pop args value. pan_primop pop args = SOME value ==>
    is_wf_shape_v sctxt value`.  Both `pan_primop` and `is_wf_shape_v` are the
    already-reviewed exact ports `panPrimopHOLExact` and
    `isWfShapeValueHOLExact` over `ValueHOL width`; the Bool predicate is
    rendered as `= true`, matching the accepted port style. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "pan_primop_is_wf_shape_v"]
theorem panPrimopHOLExact_isWfShapeValueHOLExact {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (operator : PrimOp)
    (values : List (ValueHOL width)) (value : ValueHOL width)
    (h : panPrimopHOLExact operator values = some value) :
    isWfShapeValueHOLExact context value = true := by
  unfold panPrimopHOLExact at h
  split at h
  · simp only [Option.some.injEq] at h
    subst value
    simp only [isWfShapeValueHOLExact.eq_1, isWfShapeValueHOLExact.eq_2,
      isWfShapeValuesHOLExact.eq_1, isWfShapeValuesHOLExact.eq_2]
    rfl
  · simp at h

/-- `[local]` step of HOL `panProps$is_wf_shape_v_nil_step1`
    (`cakeml/pancake/semantics/panPropsScript.sml:48-54`): with the struct
    context empty, `is_wf_shape` on the `shape_of` image implies
    `is_wf_shape_v` on the value.  Over the exact `ValueHOL width` and
    MlString-keyed `StructContextExact` carriers; the Bool predicate is
    rendered as `= true`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_nil_step1"]
theorem isWfShapeValueHOLExact_nil_step1 {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width)
    (h : context = [] ∧
      Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) = true) :
    isWfShapeValueHOLExact context value = true := by
  obtain ⟨hctx, hshape⟩ := h
  subst hctx
  induction value using isWfShapeValueHOLExact.induct
    (motive2 := fun values =>
      Flapjack.Pancake.PanLang.isWfShapesExactHOL
          ([] : Flapjack.Pancake.PanLang.StructContextExact)
          (values.map shapeOfHOLExact) = true →
        isWfShapeValuesHOLExact
          ([] : Flapjack.Pancake.PanLang.StructContextExact) values = true) with
  | case1 value => simp only [isWfShapeValueHOLExact.eq_1]
  | case2 values ih =>
      have hshape' : Flapjack.Pancake.PanLang.isWfShapesExactHOL
          ([] : Flapjack.Pancake.PanLang.StructContextExact)
          (values.map shapeOfHOLExact) = true := by
        simpa [shapeOfHOLExact, Flapjack.Pancake.PanLang.isWfShapeExactHOL] using hshape
      simpa only [isWfShapeValueHOLExact.eq_2] using ih hshape'
  | case3 name fields _ =>
      simp [shapeOfHOLExact] at hshape
  | case4 => simp only [isWfShapeValuesHOLExact.eq_1]
  | case5 value values ihValue ihValues =>
      rename_i hshape'
      have hp : Flapjack.Pancake.PanLang.isWfShapeExactHOL
            ([] : Flapjack.Pancake.PanLang.StructContextExact)
            (shapeOfHOLExact value) = true ∧
          Flapjack.Pancake.PanLang.isWfShapesExactHOL
            ([] : Flapjack.Pancake.PanLang.StructContextExact)
            (values.map shapeOfHOLExact) = true := by
        simpa [List.map_cons, Flapjack.Pancake.PanLang.isWfShapesExactHOL.eq_2,
          Bool.and_eq_true] using hshape'
      rw [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true]
      exact ⟨ihValue hp.1, ihValues hp.2⟩

/-- Exact port of HOL `panProps$is_wf_shape_v_nil`
    (`cakeml/pancake/semantics/panPropsScript.sml:56-61`): with the context
    empty, `is_wf_shape` on the `shape_of` image is equivalent to
    `is_wf_shape_v` on the value.  The forward direction is
    `isWfShapeValueHOLExact_nil_step1`, the backward direction is the tagged
    `is_wf_shape_of_v` port. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_nil" 56]
theorem isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil
    {width : Nat} [NeZero width]
    (context : Flapjack.Pancake.PanLang.StructContextExact) (hctx : context = [])
    (value : ValueHOL width) :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL context (shapeOfHOLExact value) =
      isWfShapeValueHOLExact context value := by
  subst hctx
  rw [Bool.eq_iff_iff]
  constructor
  · intro hshape
    exact isWfShapeValueHOLExact_nil_step1 [] value ⟨rfl, hshape⟩
  · intro hvalue
    exact isWfShapeValueHOLExact_shapeOfHOLExact [] value hvalue

/-- Exact port of HOL `panProps$is_wf_shape_v_drop`
    (`cakeml/pancake/semantics/panPropsScript.sml:63-71`):
    `!sctxt v. is_wf_shape_v (DROP k sctxt) v ==> is_wf_shape_v sctxt v`.
    The context is the exact MlString-keyed `StructContextExact`; `DROP` is
    `List.drop`, and `structContextLookupHOL_append` plays the role of
    `ALOOKUP_APPEND`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_drop"]
theorem isWfShapeValueHOLExact_drop {width : Nat} [NeZero width]
    (taken : Nat) (context : Flapjack.Pancake.PanLang.StructContextExact) (value : ValueHOL width)
    (h : isWfShapeValueHOLExact (context.drop taken) value = true) :
    isWfShapeValueHOLExact context value = true := by
  induction value using isWfShapeValueHOLExact.induct
    (motive2 := fun values =>
      isWfShapeValuesHOLExact (context.drop taken) values = true →
        isWfShapeValuesHOLExact context values = true) with
  | case1 value => simp only [isWfShapeValueHOLExact.eq_1]
  | case2 values ih =>
      have h' : isWfShapeValuesHOLExact (context.drop taken) values = true := by
        simpa only [isWfShapeValueHOLExact.eq_2] using h
      simpa only [isWfShapeValueHOLExact.eq_2] using ih h'
  | case3 name fields ihFields =>
      simp only [isWfShapeValueHOLExact.eq_3, Bool.and_eq_true] at h ⊢
      obtain ⟨hlook, hflds⟩ := h
      constructor
      · have happ : Flapjack.Pancake.PanLang.structContextLookupHOL name context =
            (match Flapjack.Pancake.PanLang.structContextLookupHOL name (context.take taken) with
              | some info => some info
              | none => Flapjack.Pancake.PanLang.structContextLookupHOL name (context.drop taken)) := by
          have h2 := Flapjack.Pancake.PanLang.structContextLookupHOL_append name
            (context.take taken) (context.drop taken)
          rwa [List.take_append_drop taken context] at h2
        rw [happ]
        cases htk : Flapjack.Pancake.PanLang.structContextLookupHOL name (context.take taken) with
        | none => simp [hlook]
        | some info => simp
      · exact ihFields hflds
  | case4 => simp only [isWfShapeValuesHOLExact.eq_1]
  | case5 value values ihValue ihValues =>
      rename_i h5
      simp only [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true] at h5 ⊢
      exact ⟨ihValue h5.1, ihValues h5.2⟩

/-- `isWfShapeValuesHOLExact` is preserved when the struct context is a `DROP`
    (list form of `isWfShapeValueHOLExact_drop`). -/
theorem isWfShapeValuesHOLExact_drop {width : Nat} [NeZero width] (taken : Nat)
    (context : Flapjack.Pancake.PanLang.StructContextExact) (values : List (ValueHOL width))
    (h : isWfShapeValuesHOLExact (context.drop taken) values = true) :
    isWfShapeValuesHOLExact context values = true := by
  induction values with
  | nil => simp only [isWfShapeValuesHOLExact.eq_1]
  | cons value values ih =>
      simp only [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true] at h ⊢
      exact ⟨isWfShapeValueHOLExact_drop taken context value h.1, ih h.2⟩

/-- Exact port of HOL `panProps$mem_load_is_wf_shape_v` (`panPropsScript.sml:90-108`):
    `mem_load`, `mem_loads` and `mem_load_flds` return only values that are
    well-shaped with respect to the struct context. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "mem_load_is_wf_shape_v"]
theorem memLoadHOLExact_isWfShapeValueHOLExact {width : Nat} [NeZero width]
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) :
    (∀ (shape : Flapjack.Pancake.PanLang.ShapeHOL) (address : BitVec width)
        (context : StructContextHOLM) (value : ValueHOL width),
        memLoadHOLExact shape address domain memory context = some value →
          isWfShapeValueHOLExact context value = true) ∧
    (∀ (shapes : List Flapjack.Pancake.PanLang.ShapeHOL) (address : BitVec width)
        (context : StructContextHOLM) (values : List (ValueHOL width)),
        memLoadsHOLExact shapes address domain memory context = some values →
          isWfShapeValuesHOLExact context values = true) ∧
    (∀ (fields : List (MlStringHOLM × Flapjack.Pancake.PanLang.ShapeHOL))
        (address : BitVec width) (context : StructContextHOLM)
        (values : List (MlStringHOLM × ValueHOL width)),
        memLoadFldsHOLExact fields address domain memory context = some values →
          isWfShapeValuesHOLExact context (values.map Prod.snd) = true) := by
  have hshape : ∀ (shape : Flapjack.Pancake.PanLang.ShapeHOL) (address : BitVec width)
      (context : StructContextHOLM), ∀ value : ValueHOL width,
        memLoadHOLExact shape address domain memory context = some value →
          isWfShapeValueHOLExact context value = true := by
    apply memLoadHOLExact.induct (domain := domain) (memory := memory)
      (motive1 := fun shape address context => ∀ value : ValueHOL width,
        memLoadHOLExact shape address domain memory context = some value →
          isWfShapeValueHOLExact context value = true)
      (motive2 := fun fields address context =>
        ∀ values : List (MlStringHOLM × ValueHOL width),
          memLoadFldsHOLExact fields address domain memory context = some values →
            isWfShapeValuesHOLExact context (values.map Prod.snd) = true)
      (motive3 := fun shapes address context => ∀ values : List (ValueHOL width),
        memLoadsHOLExact shapes address domain memory context = some values →
          isWfShapeValuesHOLExact context values = true)
    · intro address context hdom value h
      rw [memLoadHOLExact.eq_1, if_pos hdom] at h
      simp only [Option.some.injEq] at h
      subst value
      simp only [isWfShapeValueHOLExact.eq_1]
    · intro address context hndom value h
      rw [memLoadHOLExact.eq_1, if_neg hndom] at h
      simp at h
    · intro address context shapes values hloads ih3 value h
      rw [memLoadHOLExact.eq_2, hloads] at h
      simp only [Option.some.injEq] at h
      subst value
      simpa only [isWfShapeValueHOLExact.eq_2] using ih3 values hloads
    · intro address context shapes hloads ih3 value h
      rw [memLoadHOLExact.eq_2, hloads] at h
      simp at h
    · intro address name value h
      rw [memLoadHOLExact.eq_3] at h
      simp at h
    · intro address candidate info rest fields hflds ih2 value h
      rw [memLoadHOLExact.eq_4, if_pos rfl, hflds] at h
      simp only [Option.some.injEq] at h
      subst value
      simp only [isWfShapeValueHOLExact.eq_3, Bool.and_eq_true]
      exact ⟨by simp [Flapjack.Pancake.PanLang.structContextLookupHOL],
        isWfShapeValuesHOLExact_drop 1 ((candidate, info) :: rest) (fields.map Prod.snd)
          (ih2 fields hflds)⟩
    · intro address candidate info rest hflds ih2 value h
      rw [memLoadHOLExact.eq_4, if_pos rfl, hflds] at h
      simp at h
    · intro address name candidate info rest hne ih1 value h
      rw [memLoadHOLExact.eq_4, if_neg hne] at h
      exact isWfShapeValueHOLExact_drop 1 ((candidate, info) :: rest) value (ih1 value h)
    · intro address context values h
      rw [memLoadFldsHOLExact.eq_1] at h
      simp only [Option.some.injEq] at h
      subst values
      simp only [List.map_nil, isWfShapeValuesHOLExact.eq_1]
    · intro address context field shape rest value values hflds hload ih1 ih2 vs h
      rw [memLoadFldsHOLExact.eq_2, hload, hflds] at h
      simp only [Option.some.injEq] at h
      subst vs
      rw [List.map_cons]
      simp only [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true]
      exact ⟨ih1 value hload, ih2 values hflds⟩
    · intro address context field shape rest hcontr ih1 ih2 vs h
      rw [memLoadFldsHOLExact.eq_2] at h
      split at h
      · rename_i value values hload hflds
        exact (hcontr value values hload hflds).elim
      · simp at h
    · intro address context values h
      rw [memLoadsHOLExact.eq_1] at h
      simp only [Option.some.injEq] at h
      subst values
      simp only [isWfShapeValuesHOLExact.eq_1]
    · intro address context shape rest value values hloads hload ih1 ih3 vs h
      rw [memLoadsHOLExact.eq_2, hload, hloads] at h
      simp only [Option.some.injEq] at h
      subst vs
      simp only [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true]
      exact ⟨ih1 value hload, ih3 values hloads⟩
    · intro address context shape rest hcontr ih1 ih3 vs h
      rw [memLoadsHOLExact.eq_2] at h
      split at h
      · rename_i value values hload hloads
        exact (hcontr value values hload hloads).elim
      · simp at h
  have hloads : ∀ (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
      (address : BitVec width) (context : StructContextHOLM),
      ∀ values : List (ValueHOL width),
        memLoadsHOLExact shapes address domain memory context = some values →
          isWfShapeValuesHOLExact context values = true := by
    intro shapes
    induction shapes with
    | nil =>
        intro address context values h
        rw [memLoadsHOLExact.eq_1] at h
        simp only [Option.some.injEq] at h
        subst values
        simp only [isWfShapeValuesHOLExact.eq_1]
    | cons shape rest ih =>
        intro address context values h
        rw [memLoadsHOLExact.eq_2] at h
        split at h
        · rename_i head tail hload hrest
          simp only [Option.some.injEq] at h
          subst values
          simp only [isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true]
          exact ⟨hshape shape address context head hload,
            ih (address + bytesInWordHOL width * BitVec.ofNat width
                (Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape))
              context tail hrest⟩
        · simp at h
  have hflds : ∀ (fields : List (MlStringHOLM × Flapjack.Pancake.PanLang.ShapeHOL))
      (address : BitVec width) (context : StructContextHOLM),
      ∀ values : List (MlStringHOLM × ValueHOL width),
        memLoadFldsHOLExact fields address domain memory context = some values →
          isWfShapeValuesHOLExact context (values.map Prod.snd) = true := by
    intro fields
    induction fields with
    | nil =>
        intro address context values h
        rw [memLoadFldsHOLExact.eq_1] at h
        simp only [Option.some.injEq] at h
        subst values
        simp only [List.map_nil, isWfShapeValuesHOLExact.eq_1]
    | cons pair rest ih =>
        obtain ⟨field, shape⟩ := pair
        intro address context values h
        rw [memLoadFldsHOLExact.eq_2] at h
        split at h
        · rename_i head tail hload hrest
          simp only [Option.some.injEq] at h
          subst values
          simp only [List.map_cons, isWfShapeValuesHOLExact.eq_2, Bool.and_eq_true]
          exact ⟨hshape shape address context head hload,
            ih (address + bytesInWordHOL width * BitVec.ofNat width
                (Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape))
              context tail hrest⟩
        · simp at h
  exact ⟨hshape, hloads, hflds⟩

/-! Exact port of HOL `panProps$every_exp` (`panPropsScript.sml:1311-1333`) and
    `panProps$exps_of` (`panPropsScript.sml:1336-1358`) over the exact
    MlString/width-indexed `ExpHOL width`/`ProgHOL width` carriers.

    `every_exp P e` conjoins the leaf predicate `P` on `e` with the recursive
    predicate on its immediate sub-expressions; the HOL `EVERY` folds are
    rendered as the structural helpers `everyExpListHOL` (for `exp list`) and
    `everyExpFieldListHOL` (for the `MAP SND` field list of `NStruct`), matching
    the `isWfShapesExactHOL` convention.  `exps_of` returns the list of all
    expressions occurring in a program, mirroring the HOL clauses in order. -/
mutual
  /-- Exact port of HOL `panProps$every_exp`. -/
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "every_exp_def"]
  def everyExpHOL {width : Nat} [NeZero width]
      (P : Flapjack.Pancake.PanLang.ExpHOL width → Bool) :
      Flapjack.Pancake.PanLang.ExpHOL width → Bool
    | .const w => P (.const w)
    | .var vk v => P (.var vk v)
    | .rstruct es => P (.rstruct es) && everyExpListHOL P es
    | .rfield i e => P (.rfield i e) && everyExpHOL P e
    | .nstruct nm nm_es => P (.nstruct nm nm_es) && everyExpFieldListHOL P nm_es
    | .nfield i e => P (.nfield i e) && everyExpHOL P e
    | .load sh e => P (.load sh e) && everyExpHOL P e
    | .load32 e => P (.load32 e) && everyExpHOL P e
    | .loadByte e => P (.loadByte e) && everyExpHOL P e
    | .op bop es => P (.op bop es) && everyExpListHOL P es
    | .panop op es => P (.panop op es) && everyExpListHOL P es
    | .cmp c e1 e2 => P (.cmp c e1 e2) && everyExpHOL P e1 && everyExpHOL P e2
    | .shift sh e1 e2 => P (.shift sh e1 e2) && everyExpHOL P e1 && everyExpHOL P e2
    | .baseAddr => P .baseAddr
    | .topAddr => P .topAddr
    | .bytesInWord => P .bytesInWord

  /- `EVERY (every_exp P) es` over an exact expression list. -/
  def everyExpListHOL {width : Nat} [NeZero width]
      (P : Flapjack.Pancake.PanLang.ExpHOL width → Bool) :
      List (Flapjack.Pancake.PanLang.ExpHOL width) → Bool
    | [] => true
    | e :: es => everyExpHOL P e && everyExpListHOL P es

  /- `EVERY (every_exp P) (MAP SND nm_es)` over a field list. -/
  def everyExpFieldListHOL {width : Nat} [NeZero width]
      (P : Flapjack.Pancake.PanLang.ExpHOL width → Bool) :
      List (MlS × Flapjack.Pancake.PanLang.ExpHOL width) → Bool
    | [] => true
    | (_, e) :: es => everyExpHOL P e && everyExpFieldListHOL P es
end

/-- Exact port of HOL `panProps$exps_of`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "exps_of_def"]
def expsOfHOL {width : Nat} [NeZero width] :
    Flapjack.Pancake.PanLang.ProgHOL width → List (Flapjack.Pancake.PanLang.ExpHOL width)
  | .raise _ e => [e]
  | .dec _ _ e p => e :: expsOfHOL p
  | .seq p q => expsOfHOL p ++ expsOfHOL q
  | .ite e p q => e :: (expsOfHOL p ++ expsOfHOL q)
  | .while e p => e :: expsOfHOL p
  | .call none _ es => es
  | .call (some (_, some (_, _, ep))) _ es => es ++ expsOfHOL ep
  | .call (some (_, none)) _ es => es
  | .decCall _ _ _ es p => es ++ expsOfHOL p
  | .store e1 e2 => [e1, e2]
  | .store32 e1 e2 => [e1, e2]
  | .storeByte e1 e2 => [e1, e2]
  | .return e => [e]
  | .extCall _ e1 e2 e3 e4 => [e1, e2, e3, e4]
  | .assign _ _ e => [e]
  | .primitive _ _ es => es
  | .shMemLoad _ _ _ e => [e]
  | .shMemStore _ e1 e2 => [e1, e2]
  | _ => []

/-- Exact port of HOL `panProps$localised_exp` (`panPropsScript.sml:1362-1364`)
    over the MlString/width-indexed `ExpHOL width` carrier.

    HOL defines `localised_exp = every_exp (\e. case e of Var tp _ => tp = Local
    | _ => T)`, so the only rejecting pattern is a variable with a global
    destination. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "localised_exp_real_def"]
def localisedExpHOL {width : Nat} [NeZero width] :
    Flapjack.Pancake.PanLang.ExpHOL width → Bool :=
  everyExpHOL (fun e =>
    match e with
    | .var .local _ => true
    | .var .global _ => false
    | _ => true)

/-- Exact port of HOL `panProps$nameless_exp` (`panPropsScript.sml:1371-1373`)
    over the MlString/width-indexed `ExpHOL width` carrier.

    HOL defines `nameless_exp = every_exp (\e. case e of NStruct _ _ => F |
    NField _ _ => F | _ => T)`, so structural name introduction is rejected. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "nameless_exp_real_def"]
def namelessExpHOL {width : Nat} [NeZero width] :
    Flapjack.Pancake.PanLang.ExpHOL width → Bool :=
  everyExpHOL (fun e =>
    match e with
    | .nstruct _ _ => false
    | .nfield _ _ => false
    | _ => true)

/-- Exact port of HOL `panProps$localised_prog` (`panPropsScript.sml:1380-1406`)
    over the MlString/width-indexed `ProgHOL width` carrier, clause for clause.

    HOL's `EVERY localised_exp args` folds are rendered as
    `everyExpListHOL localisedExpHOL`; `localised_exp` is the exact
    `localisedExpHOL` defined above. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "localised_prog_def"]
def localisedProgHOL {width : Nat} [NeZero width] :
    Flapjack.Pancake.PanLang.ProgHOL width → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .dec _ _ value body => localisedExpHOL value && localisedProgHOL body
  | .seq first second => localisedProgHOL first && localisedProgHOL second
  | .ite condition thenBranch elseBranch =>
      localisedExpHOL condition && localisedProgHOL thenBranch &&
        localisedProgHOL elseBranch
  | .while condition body => localisedExpHOL condition && localisedProgHOL body
  | .store address value | .store32 address value | .storeByte address value
  | .shMemStore _ address value => localisedExpHOL address && localisedExpHOL value
  | .extCall _ configuration configurationLength array arrayLength =>
      localisedExpHOL configuration && localisedExpHOL configurationLength &&
        localisedExpHOL array && localisedExpHOL arrayLength
  | .raise _ value | .return value => localisedExpHOL value
  | .shMemLoad _ .local _ address => localisedExpHOL address
  | .shMemLoad _ .global _ _ => false
  | .call info _ arguments =>
      everyExpListHOL localisedExpHOL arguments &&
        (match info with
         | some (_, some (_, _, handler)) => localisedProgHOL handler
         | _ => true) &&
        (match info with
         | some (some (.global, _), _) => false
         | _ => true)
  | .decCall _ _ _ arguments body =>
      everyExpListHOL localisedExpHOL arguments && localisedProgHOL body
  | .assign .local _ value => localisedExpHOL value
  | .assign .global _ _ => false
  | .primitive _ _ arguments => everyExpListHOL localisedExpHOL arguments

/-- Exact port of the `[local]` HOL helper `panProps$opt_mmap_eq_some_helper`
    (`panPropsScript.sml:1575-1582`): if two maps agree on every element that
    the first maps successfully, the second succeeds with the same result.

    HOL's `OPT_MMAP` is the repository's `List.mapM` for `Option` (cf. the
    tagged `OPT_MMAP_MEM_IMP`); the statement is fully polymorphic, so there is
    no carrier side condition. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "opt_mmap_eq_some_helper" 1575]
theorem optMmapEqSomeHelper {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α) (zs : List β), xs.mapM f = some zs →
      (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) → xs.mapM g = some zs
  | [], zs, h, _ => h
  | x :: xs, zs, h, hfg => by
      rw [List.mapM_cons] at h ⊢
      cases hx : f x with
      | none => simp [hx] at h
      | some a =>
          have hga : g x = some a := hfg x (by simp) a hx
          rw [hga]
          simp at h ⊢
          cases hys : List.mapM f xs with
          | none => simp [hys] at h
          | some ys =>
              have hz : zs = a :: ys := by simpa [hys, hx] using h.symm
              subst hz
              rw [optMmapEqSomeHelper f g xs ys hys
                    (fun z hz' b hb => hfg z (by simp [hz']) b hb)]
              rfl

/-- The `MAP SND` view of a field list does not increase `sizeOf`, which
    justifies the well-founded recursion of `panIsWfShapeValueHOL` (HOL's
    `EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`). -/
theorem panSizeOfMapSndLe (fields : List (FieldName × PanValue α)) :
    sizeOf (fields.map Prod.snd) ≤ sizeOf fields := by
  induction fields with
  | nil => simp
  | cons pair pairs ih =>
      obtain ⟨field, value⟩ := pair
      simp only [List.map_cons]
      simp
      omega

/-- The context argument of a struct value is strictly larger in `sizeOf` than
    its field list. -/
theorem sizeOfFieldsLtNStruct (name : StructName)
    (fields : List (FieldName × PanValue α)) :
    sizeOf fields < sizeOf (PanValue.nStruct name fields) := by
  simp
  omega

/-
Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `panProps$is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:24`). The HOL clauses are
    reproduced literally: a scalar is `T`; `RStruct vs` is
    `EVERY (is_wf_shape_v sctxt) vs`; `NStruct nm nm_vs` is
    `(ALOOKUP sctxt nm <> NONE) /\
      EVERY (is_wf_shape_v sctxt) (MAP SND nm_vs)`.

    `lookupInfo` is the first-match association-list lookup, i.e. the exact
    `alist$ALOOKUP` counterpart, and under `[LawfulBEq String]` its `==`
    reflects HOL's `=`; `isSome` is the Bool rendering of `<> NONE`. The
    context is the HOL-shaped `StructContextHOL` (struct_info `fields` and
    `size` only), so the per-field predicate is `EVERY` over `MAP SND`, as HOL
    has it, rather than a fold over `(FieldName × PanValue)` pairs. The direct
    original-HOL rows are pinned in
    `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/
mutual
  -- FLAPJACK-SPECIFIC (not an exact HOL port): stated over the production
  -- `PanValue` carrier (whose `nStruct` names are `FieldName` = `String`) and a
  -- `StructContextHOL` keyed by `StructName` = `String`, while HOL
  -- `panPropsScript.sml` uses `fldname`/`stcname` = `mlstring`. The exact
  -- MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8` /
  -- `flapjack-0lj`.
  def panIsWfShapeValueHOL [LawfulBEq String] (context : StructContextHOL) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panIsWfShapeValuesHOL context values
    | .nStruct name fields =>
        (lookupInfo name context).isSome &&
          panIsWfShapeValuesHOL context (fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by
    all_goals first
      | sizeOf_list_dec
      | decreasing_trivial
      | (have h := panSizeOfMapSndLe fields
         have h2 := sizeOfFieldsLtNStruct name fields
         omega)

  def panIsWfShapeValuesHOL [LawfulBEq String] (context : StructContextHOL) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panIsWfShapeValueHOL context value && panIsWfShapeValuesHOL context values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! ## Adapter to the production cache-augmented struct context

Clause-by-clause relation between the exact HOL-shaped `is_wf_shape_v` port
over `StructContextHOL` and the production `panIsWfShapeValueBool` over the
cache-augmented `StructContext`. The context adapter is the projection
`StructContext.toHOL`, which drops the production-only `shapedFields` cache and
preserves first-match lookup shadowing. -/
mutual
  theorem panIsWfShapeValueHOL_toHOL [LawfulBEq String] (context : StructContext)
      (value : PanValue α) :
      panIsWfShapeValueHOL context.toHOL value = panIsWfShapeValueBool context value := by
    cases value with
    | word word => simp [panIsWfShapeValueHOL, panIsWfShapeValueBool]
    | rStruct values =>
        simp only [panIsWfShapeValueHOL, panIsWfShapeValueBool]
        exact panIsWfShapeValuesHOL_toHOL context values
    | nStruct name fields =>
        simp only [panIsWfShapeValueHOL, panIsWfShapeValueBool, lookupInfo_toHOL_isSome]
        rw [panIsWfShapeValuesHOL_mapSnd_toHOL context fields]

  theorem panIsWfShapeValuesHOL_toHOL [LawfulBEq String] (context : StructContext)
      (values : List (PanValue α)) :
      panIsWfShapeValuesHOL context.toHOL values = panIsWfShapeValuesBool context values := by
    cases values with
    | nil => simp [panIsWfShapeValuesHOL, panIsWfShapeValuesBool]
    | cons value values =>
        simp only [panIsWfShapeValuesHOL, panIsWfShapeValuesBool]
        rw [panIsWfShapeValueHOL_toHOL context value,
          panIsWfShapeValuesHOL_toHOL context values]

  theorem panIsWfShapeValuesHOL_mapSnd_toHOL [LawfulBEq String] (context : StructContext)
      (fields : List (FieldName × PanValue α)) :
      panIsWfShapeValuesHOL context.toHOL (fields.map Prod.snd)
        = panIsWfShapeValueFieldsBool context fields := by
    cases fields with
    | nil => simp [panIsWfShapeValuesHOL, panIsWfShapeValueFieldsBool]
    | cons field fields =>
        obtain ⟨fieldName, value⟩ := field
        simp only [List.map_cons, panIsWfShapeValuesHOL, panIsWfShapeValueFieldsBool]
        rw [panIsWfShapeValueHOL_toHOL context value,
          panIsWfShapeValuesHOL_mapSnd_toHOL context fields]
end

/-- HOL `fdoms_eq_flookup_some_none` (`panPropsScript.sml:276`): if two finite
    maps have the same domain, every defined lookup in the first is also defined
    in the second. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "fdoms_eq_flookup_some_none"]
theorem fdoms_eq_flookup_some_none {α : Type} {β : Type} (fm fm' : FiniteMap α β) (n : α)
    (v : β) (_vPrime : β) (hdom : FDOM fm = FDOM fm') (hv : FLOOKUP fm n = some v) :
    ∃ v', FLOOKUP fm' n = some v' := by
  have hmem : FDOM fm' n := by
    rw [← hdom]
    change fm n ≠ none
    change fm n = some v at hv
    rw [hv]
    exact Option.some_ne_none v
  change fm' n ≠ none at hmem
  cases h' : fm' n with
  | none => rw [h'] at hmem; exact absurd rfl hmem
  | some v' => exact ⟨v', by change fm' n = some v'; rw [h']⟩

/-- HOL `OPT_MMAP_MEM_IMP` (`panPropsScript.sml:115`): if `OPT_MMAP f xs` succeeds
    with `ys`, every element of `ys` is the image under `f` of an element of `xs`.
    Pure option/list lemma (no Boolean key-equality carrier); `List.mapM` is the
    repository's documented `OPT_MMAP` carrier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_MEM_IMP"]
theorem OPT_MMAP_MEM_IMP {α : Type} {β : Type} (f : α → Option β) (xs : List α)
    (ys : List β) (y : β) (h : xs.mapM f = some ys) (hy : y ∈ ys) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil] at h
      change some [] = some ys at h
      rw [Option.some.injEq] at h
      subst h
      simp at hy
  | cons a as ih =>
      rw [List.mapM_cons] at h
      change (Option.bind (f a) (fun b => Option.bind (as.mapM f) (fun rest => some (b :: rest)))) = some ys at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨b, hfa, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨rest, hta, h⟩ := h
      change some (b :: rest) = some ys at h
      rw [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hy with hyb | hyr
      · subst hyb
        exact ⟨a, List.mem_cons_self, hfa⟩
      · obtain ⟨x, hx, hfx⟩ := ih rest hta hyr
        exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- Cake `list_rel_flatten_with_shape_length`
    (`cakeml/pancake/semantics/panPropsScript.sml:549`), a prerequisite of the
    PanToCrep Call case `call_preserve_state_code_locals_rel`
    (`pan_to_crepProofScript.sml:2440`):

    `LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
     size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
     EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
     LIST_REL (\sh arg. sh = shape_of arg) sh args /\
     EVERY is_wf_shape_v_nil args ==>
     LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)`.

    Representation notes (why this is not `@[hol]`-tagged): Cake's `LIST_REL`
    (`shapes` paired pointwise with `args`) is rendered here as the indexed
    `List.get` equality (the toolchain in this repository does not expose
    `List.Forall₂`); `EL n args = v` is the indexed `arguments[n]'hn = value`;
    `flat`/`with_shape`/`size_of_shape`/`shape_of`/`is_wf_shape_v_nil` are
    `panValueFlatten`/`withShape`/`Shape.shapeSize`/`panValueShape`/
    `panValueIsWf []` respectively. -/
theorem listRelFlattenWithShapeLength (shapes : List Shape) (names : List Nat)
    (arguments : List (PanValue α)) (value : PanValue α) (n : Nat)
    (hnames : names.length = (arguments.map panValueFlatten).flatten.length)
    (hsize : Shape.shapeSize (.comb shapes) =
      (arguments.map panValueFlatten).flatten.length)
    (hn : n < arguments.length)
    (hget : arguments[n]'hn = value)
    (hlen : arguments.length = shapes.length)
    (hrel : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes.get ⟨i, hsi⟩ =
        panValueShape ([] : StructContext) (arguments.get ⟨i, hai⟩))
    (hwf : arguments.all
      (fun argument => panValueIsWf ([] : StructContext) argument) = true) :
    ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length =
      (panValueFlatten value).length := by
  have hvalues : names.length = Shape.shapeSize (.comb shapes) :=
    hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hshape : shapes[n]'hnshapes = panValueShape ([] : StructContext) value := by
    have h := hrel n hnshapes hn
    rw [List.get_eq_getElem, List.get_eq_getElem] at h
    rw [hget] at h
    exact h
  have hwfval : panValueIsWf ([] : StructContext) value = true := by
    have hall := List.all_eq_true.mp hwf
    exact hall value (by rw [← hget]; exact List.getElem_mem hn)
  have hflat := panValueFlatten_length_eq_shapeSize value
    (panValueIsWf_isWfShape_panValueShape ([] : StructContext) value hwfval)
  rw [withShape_getElem_length shapes names n hvalues hnshapes, hshape]
  exact hflat.symm

/-- Flattening offset helper: the `n'`-th element of the `n`-th group of a
    list-of-lists is the element at the sum of the preceding group lengths plus
    `n'`. -/
theorem getElem?_flatten_take_sum {α : Type} {l : List (List α)} {n n' : Nat}
    (hn : n < l.length) (hn' : n' < (l[n]'hn).length) :
    l.flatten[((l.take n).map List.length).sum + n']? = (l[n]'hn)[n']? := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a rest ih =>
      cases n with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
            List.flatten_cons, List.getElem_cons_zero] at hn' ⊢
          rw [List.getElem?_append, if_pos hn']
      | succ k =>
          rw [List.take_cons (Nat.succ_pos k), Nat.succ_sub_one]
          simp only [List.map_cons, List.sum_cons, List.flatten_cons,
            List.getElem_cons_succ] at hn' ⊢
          rw [List.getElem?_append, if_neg (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
          exact ih (n := k) (by simpa using hn) (by simpa using hn')

/-- Port of Cake `list_rel_flatten_with_shape_flookup`
    (`cakeml/pancake/semantics/panPropsScript.sml:585`), a prerequisite of the
    Pan-to-Crep Call case.  Representation differences (documented, no exact
    HOL tag): HOL `LIST_REL`/`shape_of`/`is_wf_shape_v_nil`/`EL` are rendered
    here as the indexed `get` equality, `panValueShape []`, `panValueIsWf []`
    and `getElem`; HOL `FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))` is
    `FUPDATE_LIST FEMPTY (names.zip ((arguments.map panValueFlatten).flatten))`. -/
theorem listRelFlattenWithShapeFlookup (shapes : List Shape) (names : List Nat)
    (arguments : List (PanValue α)) (value : PanValue α) (n n' : Nat)
    (hdistinct : names.Nodup)
    (hnames : names.length = (arguments.map panValueFlatten).flatten.length)
    (hsize : Shape.shapeSize (.comb shapes) = (arguments.map panValueFlatten).flatten.length)
    (hn : n < arguments.length)
    (hget : arguments[n]'hn = value)
    (hlen : arguments.length = shapes.length)
    (hrel : ∀ i (hsi : i < shapes.length) (hai : i < arguments.length),
      shapes.get ⟨i, hsi⟩ = panValueShape ([] : StructContext) (arguments.get ⟨i, hai⟩))
    (hwf : arguments.all (fun argument => panValueIsWf ([] : StructContext) argument) = true)
    (hgroup : ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length =
      (panValueFlatten value).length)
    (hn' : n' < ((withShape shapes names)[n]'(by rw [withShape_length]; omega)).length) :
    FLOOKUP (FUPDATE_LIST FEMPTY (names.zip ((arguments.map panValueFlatten).flatten)))
        (((withShape shapes names)[n]'(by rw [withShape_length]; omega))[n']'hn') =
      some ((panValueFlatten value)[n']'(by rw [← hgroup]; exact hn')) := by
  have hvalues : names.length = Shape.shapeSize (.comb shapes) := hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hgroupSize : Shape.shapeSize (shapes[n]'hnshapes) = (panValueFlatten value).length :=
    (withShape_getElem_length shapes names n hvalues hnshapes).symm.trans hgroup
  have hn'val : n' < (panValueFlatten value).length := by rw [← hgroup]; exact hn'
  have hident : Shape.shapeSize (.comb (shapes.take n)) =
      ((arguments.take n).map panValueFlatten).flatten.length := by
    apply shapeSize_comb_eq_flatten_length_of_getElem (shapes.take n) (arguments.take n)
    · rw [List.length_take, List.length_take, hlen]
    · intro i hi
      have hin : i < n := Nat.lt_of_lt_of_le hi (List.length_take_le n arguments)
      have hians : i < arguments.length := by omega
      have hish : i < shapes.length := by omega
      rw [List.getElem?_take, if_pos hin, List.getElem?_take, if_pos hin,
        List.getElem?_eq_some_iff.mpr ⟨hish, rfl⟩,
        List.getElem?_eq_some_iff.mpr ⟨hians, rfl⟩]
      simp only [Option.map_some]
      have hr := hrel i hish hians
      rw [List.get_eq_getElem, List.get_eq_getElem] at hr
      rw [hr]
    · intro arg hmem
      have hall := List.all_eq_true.mp hwf arg (List.mem_of_mem_take hmem)
      exact panValueIsWf_isWfShape_panValueShape ([] : StructContext) arg hall
  have hboundSize : Shape.shapeSize (.comb (shapes.take n)) + n' <
      Shape.shapeSize (.comb shapes) := by
    have hsplit := shapeSize_comb_append (shapes.take n) (shapes.drop n)
    rw [List.take_append_drop] at hsplit
    have hdrop := shapeSize_drop_head_le shapes n hnshapes
    omega
  have hbound : Shape.shapeSize (.comb (shapes.take n)) + n' < names.length := by
    rw [hnames, ← hsize]; exact hboundSize
  have hbound' : Shape.shapeSize (.comb (shapes.take n)) + n' <
      (arguments.map panValueFlatten).flatten.length := by rw [← hnames]; exact hbound
  have hgroupElem :
      ((withShape shapes names)[n]'(by rw [withShape_length]; omega))[n']'hn' =
        names[Shape.shapeSize (.comb (shapes.take n)) + n']'hbound := by
    rw [withShape_getElem_getElem shapes names n n' hvalues hnshapes
      (by rw [hgroupSize]; exact hn'val) hn']
  have hflat? : ((arguments.map panValueFlatten).flatten)[
      Shape.shapeSize (.comb (shapes.take n)) + n']? = (panValueFlatten value)[n']? := by
    rw [hident, List.length_flatten, List.map_take,
      getElem?_flatten_take_sum (l := arguments.map panValueFlatten) (n := n) (n' := n')
        (by rw [List.length_map]; exact hn) (by rw [List.getElem_map, hget]; exact hn'val)]
    rw [List.getElem_map, hget]
  have hflatElem : ((arguments.map panValueFlatten).flatten)[
      Shape.shapeSize (.comb (shapes.take n)) + n']'hbound' =
      (panValueFlatten value)[n']'(by rw [← hgroup]; exact hn') := by
    have hsome : ((arguments.map panValueFlatten).flatten)[
        Shape.shapeSize (.comb (shapes.take n)) + n']? =
        some ((panValueFlatten value)[n']'(by rw [← hgroup]; exact hn')) := by
      rw [hflat?, List.getElem?_eq_some_iff.mpr ⟨by rw [← hgroup]; exact hn', rfl⟩]
    obtain ⟨_, hfe⟩ := List.getElem?_eq_some_iff.mp hsome
    exact hfe
  rw [hgroupElem]
  exact (FLOOKUP_FUPDATE_LIST_zip_getElem names ((arguments.map panValueFlatten).flatten)
    FEMPTY (Shape.shapeSize (.comb (shapes.take n)) + n') hdistinct hnames hbound).trans
    (congrArg some hflatElem)

/-- Exact port of HOL `all_distinct_alist_no_overlap`
    (`cakeml/pancake/semantics/panPropsScript.sml:476`): a duplicate-free slot
    list laid out by `withShape` makes the zipped finite map overlap-free.
    HOL `alist_to_fmap (ZIP (vs, ZIP (sh, with_shape sh ns)))` is Lean's
    right-folded `alistToFmap`, including when `vs` contains duplicates. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_no_overlap"]
theorem allDistinctAlistNoOverlap {α : Type} [BEq α] [LawfulBEq α]
    (sh : List Shape) (ns : List Nat) (vs : List α)
    (hdistinct : ns.Nodup) (hlen1 : ns.length = Shape.shapeSize (.comb sh))
    (hlen2 : vs.length = sh.length) :
    noOverlap (alistToFmap (vs.zip (sh.zip (withShape sh ns)))) := by
  constructor
  · intro x a xs hlk
    obtain ⟨e, hmem, hke, hve⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) x (a, xs) hlk
    have he : e = (x, (a, xs)) := Prod.ext hke hve
    subst he
    obtain ⟨n, hn, _hj, _hfst, hsnd⟩ :=
      mem_zip_getElem vs (sh.zip (withShape sh ns)) (x, (a, xs)) hmem
    have hnsh : n < sh.length := by rw [← hlen2]; exact hn
    have hz := hsnd
    rw [List.getElem_zip] at hz
    have hshapeget :
        (withShape sh ns)[n]'(by rw [withShape_length]; exact hnsh) = xs :=
      congrArg Prod.snd hz
    exact hshapeget ▸ all_distinct_withShape sh ns n hdistinct hnsh hlen1
  · intro x y a b xs ys hx hy hinter
    rcases hinter with ⟨z, hzxs, hzys⟩
    obtain ⟨e, hme, hke, hve⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) x (a, xs) hx
    obtain ⟨f, hmf, hkf, hvf⟩ :=
      flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) y (b, ys) hy
    have he : e = (x, (a, xs)) := Prod.ext hke hve
    subst he
    have hf : f = (y, (b, ys)) := Prod.ext hkf hvf
    subst hf
    by_cases hxy : x = y
    · exact hxy
    · have hdisj :=
        listDisjoint_of_mem_zip_withShape vs sh ns (x, (a, xs)) (y, (b, ys))
          hlen2 (by rw [withShape_length]) hdistinct hlen1 hme hmf hxy
      exact (hdisj z hzxs hzys).elim


/-- Exact port of HOL `all_distinct_alist_ctxt_max`
    (`cakeml/pancake/semantics/panPropsScript.sml:517`): every slot recorded in
    the compiled context is bounded by `MAX_LIST ns`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "all_distinct_alist_ctxt_max"]
theorem allDistinctAlistCtxtMax {α : Type} [BEq α] [LawfulBEq α]
    (sh : List Shape) (ns : List Nat) (vs : List α)
    (_hdistinct : ns.Nodup) (hlen1 : ns.length = Shape.shapeSize (.comb sh))
    (hlen2 : vs.length = sh.length) :
    ctxtMax (maxList ns) (alistToFmap (vs.zip (sh.zip (withShape sh ns)))) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro v a xs hlk x hx
  obtain ⟨e, hmem, hke, hve⟩ :=
    flookupAlistToFmap_mem (vs.zip (sh.zip (withShape sh ns))) v (a, xs) hlk
  have he : e = (v, (a, xs)) := Prod.ext hke hve
  subst he
  obtain ⟨n, hn, _hj, _hfst, hsnd⟩ :=
    mem_zip_getElem vs (sh.zip (withShape sh ns)) (v, (a, xs)) hmem
  have hnsh : n < sh.length := by rw [← hlen2]; exact hn
  have hz := hsnd
  rw [List.getElem_zip] at hz
  have hshapeget :
      (withShape sh ns)[n]'(by rw [withShape_length]; exact hnsh) = xs :=
    congrArg Prod.snd hz
  have hxmem : x ∈ ns := by
    rw [← hshapeget] at hx
    exact mem_of_withShape_mem sh ns n x (by rw [withShape_length]; exact hnsh) hlen1 hx
  exact maxList_ge_of_mem ns x hxmem

/-! ## Exact `res_var` / `shape_of` lemmas over the exact carriers

`panPropsScript.sml` states four small properties of HOL `shape_of`
(`panPropsScript.sml:14`) and `res_var` (`panPropsScript.sml:220-240`) over the
exact `panSem` carriers.  The exact Lean counterparts are `shapeOfHOLExact`
(`PanSem/ValueHOL.lean`, tagged `shape_of_def`) and `resVarHOLExact`
(`PanSem/LocalUpdatesExact.lean`, tagged `res_var_def`), so these lemmas are
ported over those definitions rather than the production generic carriers used
by the `panValueShape`/`panValueResVar` bridges. -/

/-- Exact port of HOL `panProps$shape_of_val` (`panPropsScript.sml:14`):
    `shape_of (Val x) = One`.  The `Val` payload is ignored, so the
    `HolWordLab` carrier does not affect the result. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "shape_of_val"]
theorem shapeOfHOLExact_val {width : Nat} [NeZero width] (value : HolWordLab width) :
    shapeOfHOLExact (.val value : ValueHOL width) =
      Flapjack.Pancake.PanLang.ShapeHOL.one := by
  simp [shapeOfHOLExact]

/-- Function-backed rendering of HOL `panProps$FLOOKUP_pan_res_var_thm`
    (`panPropsScript.sml:236`). Untagged because HOL's `lc` is a finite map,
    while this Lean statement quantifies over every `MlS → Option _` function. -/
theorem resVarHOLExact_flookup {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (m n : MlS) (v : Option (ValueHOL width)) :
    resVarHOLExact locals (m, v) n = if n = m then v else locals n := by
  rcases v with _ | value <;> simp [resVarHOLExact]

/-- Function-backed rendering of HOL `panProps$flookup_res_var_diff_eq_org`
    (`panPropsScript.sml:228`); untagged because its lookup-function input
    ranges beyond HOL finite maps. -/
theorem resVarHOLExact_flookup_of_ne {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (n m : MlS) (v : Option (ValueHOL width)) (h : n ≠ m) :
    resVarHOLExact locals (n, v) m = locals m := by
  have h' : m ≠ n := fun hm => h hm.symm
  rcases v with _ | value <;> simp [resVarHOLExact, h']

/-- Function-backed rendering of HOL `panProps$flookup_res_var_some_eq_lookup`
    (`panPropsScript.sml:220`); untagged because the two lookup-function
    arguments range beyond HOL finite maps. -/
theorem resVarHOLExact_flookup_some_eq_lookup {width : Nat} [NeZero width]
    (lc lc' : MlS → Option (ValueHOL width))
    (v : MlS) (value : ValueHOL width)
    (h : resVarHOLExact lc (v, lc' v) v = some value) : lc' v = some value := by
  cases hv : lc' v with
  | none => simp [resVarHOLExact, hv] at h
  | some w =>
      have hw : some w = some value := by simpa [resVarHOLExact, hv] using h
      exact hw

/-! ## Exact `size_of_sh_with_ctxt_eq` over the exact carriers

`panPropsScript.sml:184` states that a shape that is well-formed under the empty
struct context has the same size with or without a context.  The exact Lean
counterparts are `sizeOfShapeWithContextHOL` (tagged `size_of_sh_with_ctxt_def`)
and `sizeOfShapeHOL` (tagged `size_of_shape_def`) over `ShapeHOL`, with the
context-less well-formedness rendered as `isWfShapeExactHOL [] shape = true`
(HOL `is_wf_shape_nil` is the overload `is_wf_shape []`). -/

open Flapjack.Pancake.PanLang

/- Untagged support: context-free well-formed shapes have the same
    with-context size as their plain `size_of_shape` size, for every context. -/
mutual
  theorem sizeOfShapeWithContextHOL_eq_nil : ∀ (shape : ShapeHOL),
      isWfShapeExactHOL ([] : StructContextExact) shape = true →
      ∀ context, sizeOfShapeWithContextHOL context shape = sizeOfShapeHOL shape
    | .one, _ => by simp
    | .comb shapes, h => by
        simp only [isWfShapeExactHOL_comb] at h
        intro context
        simp [sizeOfShapeWithContextHOL_comb, sizeOfShapeHOL_comb,
          sizeOfShapesWithContextHOL_eq_nil shapes h context]
    | .named name, h => by
        simp [isWfShapeExactHOL_named, structContextLookupHOL_nil] at h
  theorem sizeOfShapesWithContextHOL_eq_nil : ∀ (shapes : List ShapeHOL),
      isWfShapesExactHOL ([] : StructContextExact) shapes = true →
      ∀ context, sizeOfShapesWithContextHOL context shapes = sizeOfShapesHOL shapes
    | [], _ => by simp
    | shape :: shapes, h => by
        simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        intro context
        simp [sizeOfShapesWithContextHOL_cons, sizeOfShapesHOL_cons,
          sizeOfShapeWithContextHOL_eq_nil shape h.1 context,
          sizeOfShapesWithContextHOL_eq_nil shapes h.2 context]
end

/-- Exact port of HOL `panProps$size_of_sh_with_ctxt_eq`
    (`panPropsScript.sml:184`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "size_of_sh_with_ctxt_eq"]
theorem sizeOfShapeWithContextHOL_eq (shape : ShapeHOL) (context : StructContextExact)
    (h : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    sizeOfShapeWithContextHOL context shape = sizeOfShapeHOL shape :=
  sizeOfShapeWithContextHOL_eq_nil shape h context

/-! ## Exact `length_flatten_eq_size_of_shape` over the exact carriers

`panPropsScript.sml:171` states that a value whose `shape_of` is well-formed under
the empty struct context has `LENGTH (flatten v) = size_of_shape (shape_of v)`.
The exact Lean counterparts are `flattenHOL` (tagged `flatten_def`),
`shapeOfHOLExact` (tagged `shape_of_def`), and `sizeOfShapeHOL` (tagged
`size_of_shape_def`) over `ValueHOL`, with the context-less well-formedness
rendered as `isWfShapeExactHOL [] shape = true` (HOL `is_wf_shape_nil` is the
overload `is_wf_shape []`). -/

/- Untagged support: the flattened word list of a value has length equal to the
    plain `size_of_shape` size of its shape, for values whose shape is
    well-formed under the empty struct context. -/
mutual
  theorem lengthFlattenHOL_eq_sizeOfShapeHOL {width : Nat} [NeZero width]
      : ∀ (v : ValueHOL width),
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true →
        (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v)
    | .val w, _ => by simp [flattenHOL, shapeOfHOLExact]
    | .rStruct fields, h => by
        simp only [shapeOfHOLExact, isWfShapeExactHOL_comb] at h
        simp only [flattenHOL, shapeOfHOLExact, sizeOfShapeHOL_comb]
        exact lengthFlattenHOLs_eq_sizeOfShapesHOL fields h
    | .nStruct name fields, h => by
        simp [shapeOfHOLExact, isWfShapeExactHOL_named, structContextLookupHOL_nil] at h
  theorem lengthFlattenHOLs_eq_sizeOfShapesHOL {width : Nat} [NeZero width]
      : ∀ (vs : List (ValueHOL width)),
        isWfShapesExactHOL ([] : StructContextExact) (vs.map shapeOfHOLExact) = true →
        (vs.map flattenHOL).flatten.length = sizeOfShapesHOL (vs.map shapeOfHOLExact)
    | [], _ => by simp
    | v :: vs, h => by
        simp only [List.map_cons, isWfShapesExactHOL_cons, Bool.and_eq_true] at h
        have h1 := lengthFlattenHOL_eq_sizeOfShapeHOL v h.1
        have h2 := lengthFlattenHOLs_eq_sizeOfShapesHOL vs h.2
        simp [List.flatten_cons, List.length_append, h1, h2]
end

/-- Exact port of HOL `panProps$length_flatten_eq_size_of_shape`
    (`panPropsScript.sml:171`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "length_flatten_eq_size_of_shape"]
theorem flattenHOL_length_eq_sizeOfShapeHOL {width : Nat} [NeZero width]
    (v : ValueHOL width)
    (h : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v) :=
  lengthFlattenHOL_eq_sizeOfShapeHOL v h

/-! ## Exact `functions` append/filter lemmas over the exact declaration carrier

`panPropsScript.sml:1496-1516` groups three list identities about the
`panLang$functions` projection and the `is_function`/`is_decl` predicates.  The
exact Lean counterparts are `functionsHOL` (tagged `functions_def`),
`isDeclHOL` (tagged `is_decl_def`) and `isFunctionHOL` (tagged
`is_function_def`), all over the reviewed `List (DeclHOL width)` carrier, so
these statements transfer clause for clause with no extra hypotheses.  HOL's
`functions_eq_FILTER` (`panPropsScript.sml:1487`, bead `flapjack-4ac.4.80`) is
deliberately excluded: its `MAP` carries an `ARB` fallback whose rendering is
not yet reviewed (see `functions_eq_filterMap` in `Flapjack/Pancake/PanSimp.lean`
and the note in `Flapjack/Pancake/Proofs/PanGlobals.lean`). -/

/-- Exact port of HOL `panProps$functions_append`
    (`panPropsScript.sml:1496`): the function table of a concatenation is the
    concatenation of the function tables. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_append"]
theorem functionsHOL_append {width : Nat} [NeZero width]
    (prog1 prog2 : List (DeclHOL width)) :
    functionsHOL (prog1 ++ prog2) = functionsHOL prog1 ++ functionsHOL prog2 := by
  induction prog1 with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;> simp [functionsHOL, ih]

/-- Exact port of HOL `panProps$functions_FILTER`
    (`panPropsScript.sml:1502`): filtering a program to its function
    declarations leaves the function table unchanged. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER"]
theorem functionsHOL_filter_isFunction {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    functionsHOL (prog.filter isFunctionHOL) = functionsHOL prog := by
  induction prog with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [functionsHOL, isFunctionHOL, List.filter_cons, ih]

/-- Exact port of HOL `panProps$functions_FILTER'`
    (`panPropsScript.sml:1510`): a program filtered to its value declarations
    has an empty function table. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "functions_FILTER'"]
theorem functionsHOL_filter_isDecl {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    functionsHOL (prog.filter isDeclHOL) = [] := by
  induction prog with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [functionsHOL, isDeclHOL, List.filter_cons, ih]

end Flapjack
