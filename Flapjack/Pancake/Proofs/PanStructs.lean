import Flapjack.HolRef
import Flapjack.Pancake.PanStructs

/-!
Proof lemmas for CakeML Pancake's `pan_structs` theory.

The `afindi` results below are ports of declarations from
`cakeml/pancake/proofs/pan_structsProofScript.sml`. Helpers whose Lean
statements use different equality or indexing APIs are kept untagged and their
translation limits are documented at the declarations.
-/

namespace Flapjack

/-- Production-carrier analogue of HOL's local `compile_exps_eq_map`
    (`pan_structsProofScript.sml:11`): the production recursive helper used by
    `structCompileExp` maps the production single-expression compiler over the
    list. `List.map` represents HOL `MAP`; `[BEq String]` is the typeclass
    needed by the Lean implementation's lookup. Not an exact port; see the note
    below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag). HOL's
-- `compile_exps_eq_map` (`pan_structsProofScript.sml:11`) is over the record
-- `context` (`pan_structsScript.sml:15-21`) whose `structs` field is the
-- fields-only list `(stcname # (fldname # shape) list) list`, with
-- `stcname`/`fldname` = `mlstring`, and over the same mutually recursive
-- `compile_exp`/`compile_exps` pair (`pan_structsScript.sml:107-154`). This
-- Lean statement is over production `StructPassContext`
-- (`Flapjack/Pancake/PanStructs.lean:41-45`), whose `structs : StructContext`
-- has `StructInfo` entries carrying the production-only `shapedFields` cache
-- (HOL's `structs` field is a bare `(fldname # shape) list`, no `struct_info`)
-- and whose `locals`/`globals` are `InfoMap Shape`. The constructors therefore
-- differ in arity and field types, not only in name representation, and
-- `structCompileExp` passes the full `StructContext` to `structCompileShape`,
-- whereas HOL `compile_shape` consumes the fields-only `ctxt.structs`. A
-- `(names_as_string := ...)` qualifier does not authorize these carrier
-- differences. The exact MlString carriers are available and the faithful port
-- is tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
-- Oracle: `scripts/hol-probes/pan_structs_compile_exp_probe.out` row
-- `list_map=T`. Fixture:
-- `Flapjack.Test.PanStructsCompileExpParity.structCompileExps_eq_map_fixture`.
theorem structCompileExps_eq_map {α : Type} [BEq String] (context : StructPassContext) :
    (structCompileExp.structCompileExps (α := α) context :
      List (Exp α) → List (Exp α)) =
      fun expressions => expressions.map (structCompileExp context) := by
  funext expressions
  induction expressions with
  | nil => simp [structCompileExp.structCompileExps]
  | cons expression expressions ih =>
      simp [structCompileExp.structCompileExps, ih]

/-- Fuel-indexed analogue of HOL `compile_shapes_eq_map`
    (`pan_structsProofScript.sml:310`). The HOL statement has no fuel
    parameter and concerns mutually recursive `compile_shape`/`compile_shapes`.
    This auxiliary helper theorem is deliberately untagged; the production
    no-fuel theorem `structCompileShapes_eq_map` below establishes the exact
    HOL statement instead. -/
theorem structCompileShapesFuel_eq_map (fuel : Nat) (context : StructContext) :
    (structCompileShapeFuel.structCompileShapesFuel fuel context : List Shape → List Shape) =
      fun shapes => shapes.map (structCompileShapeFuel fuel context) := by
  funext shapes
  induction shapes with
  | nil => simp [structCompileShapeFuel.structCompileShapesFuel]
  | cons shape shapes ih =>
      simp [structCompileShapeFuel.structCompileShapesFuel, ih]

/-- No-fuel analogue of HOL `compile_shapes_eq_map`
    (`pan_structsProofScript.sml:310`), stated over the production compiler
    `structCompileShapeWF`. The production mutually recursive compiler
    decreases on the HOL context-suffix/syntax-size measure, so this statement
    keeps the source theorem's context and list arguments unchanged, but it is
    not an exact port of the HOL carriers (see the FLAPJACK-SPECIFIC note
    below). -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag). HOL's
-- `compile_shapes_eq_map` (`pan_structsProofScript.sml:310`) is stated over a
-- fields-only context `(stcname # (fldname # shape) list) list` with
-- `stcname`/`fldname` = `mlstring`, and its `compile_shapes`/`compile_shape`
-- both consume exactly that list. This Lean statement uses the production
-- carrier `StructContext = List (StructName × StructInfo)`, whose
-- `StructName` and `FieldName` are `String` and whose `StructInfo` adds the
-- production-only `shapedFields` cache (HOL `struct_info` is fields and size
-- only), so the context carrier differs in arity, not only in name
-- representation. This theorem only passes the context through, but a tag on
-- it would still record the compiled functions' carriers, and a
-- `(names_as_string := ...)` qualifier does not authorize the extra
-- `StructInfo` field. The exact MlString carriers are available and the
-- faithful port is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`). Fixture:
-- `Flapjack.Test.PanStructsCompileShapeParity.structCompileShapes_eq_map_fixture`.
theorem structCompileShapes_eq_map (context : StructContext) :
    (structCompileShapeWF.structCompileShapesWF context : List Shape → List Shape) =
      fun shapes => shapes.map (structCompileShapeWF context) := by
  funext shapes
  induction shapes with
  | nil => simp [structCompileShapeWF.structCompileShapesWF]
  | cons shape shapes ih =>
      simp [structCompileShapeWF.structCompileShapesWF, ih]

/-- Exact port of the local HOL `UNCURRY_EQ_o_SND`
    (`pan_structsProofScript.sml:552`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "UNCURRY_EQ_o_SND"]
theorem prod_uncurry_const_eq_comp_snd {α β γ : Type} (f : β → γ) :
    Function.uncurry (fun _ : α => f) = f ∘ Prod.snd := by
  funext p
  cases p
  rfl

/-- Exact port of HOL `map_uncurry_zip_again`
    (`pan_structsProofScript.sml:900`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_uncurry_zip_again"]
theorem list_zip_map_eq {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (xs.zip ys).map (fun p => (f p.1, g p.2)) = (xs.map f).zip (ys.map g) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.map_cons, List.length_cons] at h ⊢
          have h' : xs.length = ys.length := by omega
          rw [ih ys h']

/-! Helper for projecting one well-formed shape from a well-formed shape list. -/
theorem isWfShapeList_of_all {context : StructContext} {shapes : List Shape}
    (h : ∀ shape ∈ shapes, isWfShape context shape = true) :
    isWfShape.isWfShapeList context shapes = true := by
  induction shapes with
  | nil => simp [isWfShape.isWfShapeList]
  | cons s ss ih =>
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨h s (by simp), ih (fun t ht => h t (by simp [ht]))⟩

/-- Production invariant corresponding clause-for-clause to HOL
    `pan_structsProofScript.sml:struct_infos_ok_def`. It remains untagged:
    HOL takes `(stcname # struct_info) list`, where names and field names are
    `mlstring` and each `struct_info` contains only fields and size. This
    predicate takes production `StructContext`, whose names and field names
    are `String`, whose `Shape.named` also carries `String`, and whose
    `StructInfo` adds the production-only `shapedFields` cache. The body uses
    production String equality in nodup checks and `isWfShape` lookups. Thus a
    `names_as_string` qualifier would not address the different context and
    record carriers; the exact `MlS`/`ShapeHOL`/`StructContextExact` carriers
    are available for a faithful counterpart. The identifier carrier work is
    tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). There are no additional hypotheses, and the
    four invariant clauses otherwise follow HOL's distinct field names,
    distinct structure names, suffix shape well-formedness, and context-based
    size calculation. -/
def structInfosOk (context : StructContext) : Prop :=
  (∀ entry ∈ context, (entry.2.fields.map Prod.fst).Nodup) ∧
  (context.map Prod.fst).Nodup ∧
  (∀ (i : Nat) (name : StructName) (info : StructInfo),
      context[i]? = some (name, info) →
      ∀ shape ∈ info.fields.map Prod.snd,
        isWfShape (context.drop (i + 1)) shape = true) ∧
  (∀ entry ∈ context,
      entry.2.size =
        shapeSizeWithContext context (.comb (entry.2.fields.map Prod.snd)))

/-- HOL's mutual `is_wf_shape_compile_shape`
    (`pan_structsProofScript.sml:298`): compiling a shape, or a list of
    shapes, removes every `Named` constructor, so the result is well formed in
    any outer structure context. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag). HOL states
-- this mutual theorem over fields-only contexts `(stcname # (fldname # shape)
-- list) list`, with `stcname`/`fldname` = `mlstring`, and `compile_shape`
-- consumes exactly that list. This Lean statement is keyed by the production
-- carriers: `isWfShape`/`structCompileShapeWF` both take
-- `StructContext = List (StructName × StructInfo)`, whose `StructName` and
-- `FieldName` are `String` and whose `StructInfo` adds the production-only
-- `shapedFields` cache (HOL `struct_info` is fields and size only). The
-- wf-context and the compile-context are therefore a different carrier, not
-- just a different name representation, and `structCompileShapeWF` receives
-- the full cache-augmented context rather than HOL's fields projection
-- `MAP (λ(nm,info).(nm,info.fields)) ctxt`; the `[BEq String]` argument is
-- production `String` equality in the `Named` lookup. So a
-- `(names_as_string := ...)` qualifier does not apply. The exact
-- MlString/`ShapeHOL`/`StructContextExact` carriers are available for a
-- faithful port, which is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`). Fixture:
-- `Flapjack.Test.PanStructsCompileShapeParity.structCompileShapeWF_isWfShape_fixture`.
theorem structCompileShapeWF_isWfShape [BEq String]
    (outer : StructContext) :
    (∀ (context : StructContext) (shape : Shape),
      isWfShape outer (structCompileShapeWF context shape) = true) ∧
    (∀ (context : StructContext) (shapes : List Shape),
      isWfShape.isWfShapeList outer
        (structCompileShapeWF.structCompileShapesWF context shapes) = true) := by
  have hshape : ∀ (context : StructContext) (shape : Shape),
      isWfShape outer (structCompileShapeWF context shape) = true := by
    intro context shape
    apply structCompileShapeWF.induct
      (motive1 := fun context shapes =>
        isWfShape.isWfShapeList outer
          (structCompileShapeWF.structCompileShapesWF context shapes) = true)
      (motive2 := fun context shape =>
        isWfShape outer (structCompileShapeWF context shape) = true)
    · intro context
      simp [structCompileShapeWF.structCompileShapesWF, isWfShape.isWfShapeList]
    · intro context shape shapes ihShape ihShapes
      simp only [structCompileShapeWF.structCompileShapesWF,
        isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨ihShape, ihShapes⟩
    · intro context
      simp [structCompileShapeWF, isWfShape]
    · intro context shapes ih
      simp only [structCompileShapeWF, isWfShape]
      exact ih
    · intro context name info suffix hlookup ih
      rw [structCompileShapeWF.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
      exact ih
    · intro context name hlookup
      rw [structCompileShapeWF.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
  constructor
  · exact hshape
  · intro context shapes
    rw [structCompileShapes_eq_map]
    induction shapes with
    | nil => simp [isWfShape.isWfShapeList]
    | cons shape shapes ih =>
        simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true]
        exact ⟨hshape context shape, ih⟩

/-! Lean support lemma used by HOL `is_wf_shape_drop` and PanValues: lookup
    success in a suffix implies lookup success in the original context. -/
theorem lookupInfo_isSome_drop (name : String) (context : StructContext)
    (n : Nat) :
    (lookupInfo name (context.drop n)).isSome = true →
      (lookupInfo name context).isSome = true := by
  induction context generalizing n with
  | nil => cases n <;> simp [lookupInfo]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      cases n with
      | zero => simp
      | succ m =>
          simp only [List.drop_succ_cons]
          intro h
          have hrest := ih m h
          by_cases hc : candidate == name
          · simp [lookupInfo, hc]
          · simp only [lookupInfo, hc]
            exact hrest

/-- Production-carrier analogue of HOL `is_wf_shape_drop`
    (`pan_structsProofScript.sml:114`): a shape well formed in a context
    suffix remains well formed in the full context. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): this statement quantifies over
-- production `StructContext`/`Shape`, whose names use unrestricted `String`
-- and whose struct records include the production-only `shapedFields` cache.
-- HOL uses `StructContextExact`/`ShapeHOL` with `mlstring` names. There is no
-- NameRanged premise, so `names_as_string` cannot bridge arbitrary inputs;
-- the exact-carrier replacement is tracked by flapjack-pxn.18.3.5.8.
theorem isWfShape_drop [BEq String] (context : StructContext) (shape : Shape)
    (n : Nat) :
    isWfShape (context.drop n) shape = true → isWfShape context shape = true :=
  (isWfShape.induct
    (motive1 := fun shapes => ∀ (context : StructContext) (n : Nat),
      isWfShape.isWfShapeList (context.drop n) shapes = true →
        isWfShape.isWfShapeList context shapes = true)
    (motive2 := fun shape => ∀ (context : StructContext) (n : Nat),
      isWfShape (context.drop n) shape = true → isWfShape context shape = true)
    (by intro context n _; simp [isWfShape.isWfShapeList])
    (by
      intro shape shapes ih1 ih2 context n h
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at h ⊢
      exact ⟨ih1 context n h.1, ih2 context n h.2⟩)
    (by intro context n _; simp [isWfShape])
    (by
      intro shapes ih context n h
      have h' : isWfShape.isWfShapeList (context.drop n) shapes = true := by
        simpa [isWfShape] using h
      simpa [isWfShape] using ih context n h')
    (by
      intro name context n h
      simp only [isWfShape, isWfShapeHOL_named, lookupInfo_toHOL_isSome] at h ⊢
      exact lookupInfo_isSome_drop name context n h))
    shape context n

/-! Lean list-lookup adaptation of Cake's local `alookup_drop_helper`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:78`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "alookup_drop_helper"]
theorem lookup_drop_helper [BEq α] [LawfulBEq α]
    (n : Nat) (xs : List (α × β)) (key : α) (value : β)
    (hlookup : List.lookup key (xs.drop n) = some value)
    (hnodup : (xs.map Prod.fst).Nodup) :
    key ∉ (xs.take n).map Prod.fst ∧ List.lookup key xs = some value := by
  have hmem_drop : key ∈ (xs.drop n).map Prod.fst := by
    obtain ⟨l₁, l₂, heq, _⟩ :=
      (List.lookup_eq_some_iff (l := xs.drop n) (k := key) (b := value)).mp hlookup
    exact List.mem_map.mpr ⟨(key, value), by rw [heq]; simp, rfl⟩
  have hmap : xs.map Prod.fst =
      (xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst := by
    rw [← List.map_append, List.take_append_drop]
  have hnodup' : ((xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst).Nodup := by
    rw [← hmap]; exact hnodup
  have hnot_mem : key ∉ (xs.take n).map Prod.fst := by
    intro hk
    exact (List.nodup_append.mp hnodup').2.2 key hk key hmem_drop rfl
  refine ⟨hnot_mem, ?_⟩
  have htake_none : List.lookup key (xs.take n) = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    rw [bne_iff_ne]
    intro hkp
    exact hnot_mem (List.mem_map.mpr ⟨p, hp, hkp.symm⟩)
  have h1 := List.lookup_append (l₁ := xs.take n) (l₂ := xs.drop n) (k := key)
  rw [htake_none] at h1
  simp only [Option.none_or] at h1
  rw [← List.take_append_drop n xs, h1]
  exact hlookup

/-! Lean support lemma used to extract a shape premise from a well-formed
    shape list. -/
theorem isWfShape_of_mem {context : StructContext} {shapes : List Shape} {shape : Shape}
    (h : isWfShape.isWfShapeList context shapes = true) (hmem : shape ∈ shapes) :
    isWfShape context shape = true := by
  induction shapes with
  | nil => simp at hmem
  | cons s ss ih =>
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact h.1
      · exact ih h.2 hmem'

/-! Lean support lemmas connecting `lookupInfo` with the generic list lookup
    used in HOL's local `alookup_drop_helper`. -/
theorem lookupInfo_eq_lookup [BEq String] [LawfulBEq String]
    (name : String) (entries : InfoMap α) :
    lookupInfo name entries = List.lookup name entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨candidate, value⟩ := entry
      simp only [lookupInfo, List.lookup_cons, ih]
      by_cases h : (candidate == name) = true
      · have h' : (name == candidate) = true := by
          rw [beq_iff_eq] at h ⊢
          exact h.symm
        simp [h, h']
      · have h' : (name == candidate) = false :=
          beq_eq_false_iff_ne.mpr (fun hc => h (beq_iff_eq.mpr hc.symm))
        simp [h, h']

theorem lookupInfo_drop_helper [BEq String] [LawfulBEq String] (n : Nat)
    (context : StructContext) (name : String) (info : StructInfo)
    (hlookup : lookupInfo name (context.drop n) = some info)
    (hnodup : (context.map Prod.fst).Nodup) :
    lookupInfo name context = some info := by
  rw [lookupInfo_eq_lookup] at hlookup ⊢
  exact (lookup_drop_helper n context name info hlookup hnodup).2

/-- Production analogue of HOL `size_of_sh_with_ctxt_drop`
    (`pan_structsProofScript.sml:99`): a well-formed shape has the same
    context-sensitive size in a distinct-key context and its suffix. It is
    untagged because HOL's `sh_ctxt` is `StructContextExact` over `MlS`,
    `ShapeHOL`, and the exact fields/size-only struct record, whereas this
    theorem uses production `StructContext`/`Shape`: struct and named-shape
    identifiers use `String`, and production `StructInfo` has an additional
    `shapedFields` cache. The body uses String-keyed production lookup. A
    `names_as_string` qualifier cannot cover those context/record differences.
    The statement otherwise has HOL's two premises and equality conclusion;
    the exact context-sensitive size definition already exists as
    `sizeOfShapeWithContextHOL`, and the exact drop theorem is now ported as
    `sizeOfShapeWithContextHOL_drop` in the exact-carrier compile-correctness
    module. -/
theorem shapeSizeWithContext_drop (context : StructContext)
    (shape : Shape) (n : Nat)
    (h : isWfShape (context.drop n) shape = true)
    (hnodup : (context.map Prod.fst).Nodup) :
    shapeSizeWithContext (context.drop n) shape = shapeSizeWithContext context shape := by
  revert h hnodup
  induction shape using shapeSizeWithContext.induct with
  | case1 => intro _ _; simp only [shapeSizeWithContext]
  | case2 shapes ih =>
      intro h hnodup
      have hlist : isWfShape.isWfShapeList (context.drop n) shapes = true := by
        simpa [isWfShape] using h
      have hpoint : ∀ s ∈ shapes,
          shapeSizeWithContext (context.drop n) s = shapeSizeWithContext context s :=
        fun s hs => ih s hs (isWfShape_of_mem hlist hs) hnodup
      have hfold : ∀ (l : List Shape),
          (∀ s ∈ l, shapeSizeWithContext (context.drop n) s = shapeSizeWithContext context s) →
          ∀ acc, l.foldl (fun total shape => total + shapeSizeWithContext (context.drop n) shape) acc =
              l.foldl (fun total shape => total + shapeSizeWithContext context shape) acc := by
        intro l
        induction l with
        | nil => intro _ acc; rfl
        | cons s ss ihs =>
            intro hl acc
            simp only [List.foldl_cons]
            rw [hl s (by simp)]
            exact ihs (fun t ht => hl t (by simp [ht])) (acc + shapeSizeWithContext context s)
      have hsum : shapes.foldl
          (fun total shape => total + shapeSizeWithContext (context.drop n) shape) 0 =
          shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) 0 :=
        hfold shapes hpoint 0
      simp [shapeSizeWithContext, hsum]
  | case3 name =>
      intro h hnodup
      have hsome : (lookupInfo name (context.drop n)).isSome = true := by
        simpa [isWfShape] using h
      cases hlk : lookupInfo name (context.drop n) with
      | none => simp [hlk] at hsome
      | some info =>
          have hctx := lookupInfo_drop_helper n context name info hlk hnodup
          simp [shapeSizeWithContext, hlk, hctx]

/-- Production-carrier analogue of HOL `struct_infos_ok_drop`
    (`pan_structsProofScript.sml:169-196`): dropping a context prefix preserves
    distinct field and structure names, suffix well-formedness, and sizes. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag):
-- HOL `struct_infos_ok_drop` is
-- `struct_infos_ok sh_ctxt ==> struct_infos_ok (DROP n sh_ctxt)`, with `sh_ctxt`
-- the fields-only `(stcname # struct_info) list` whose `stcname`/`fldname` are
-- `mlstring` and whose `struct_info = <| fields; size |>` has no cache. This
-- statement is keyed by the production `StructContext = List (StructName × StructInfo)`,
-- whose `StructName`/`FieldName` are `String` and whose `StructInfo` carries the
-- extra `shapedFields` cache; that constructor-arity/field-type difference from
-- HOL's `struct_info` goes beyond name representation, so the
-- `(names_as_string := ...)` qualifier does not apply. The executable
-- `structInfosOk` predicate is likewise the production analogue (see its own
-- declaration-local note), not a tagged HOL port. The faithful MlString/ShapeHOL
-- carrier is tracked by flapjack-pxn.18.3.5.8 (parent flapjack-pxn.18.3.5.7.2).
-- Evidence: HOL oracle row in scripts/hol-probes/afindi_probe.out; Lean fixture
-- Flapjack.Test.PanStructsAfindiParity.structInfosOk_drop_fixture.
theorem structInfosOk_drop (n : Nat) (context : StructContext)
    (h : structInfosOk context) : structInfosOk (context.drop n) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hdrop_drop : ∀ (i : Nat) (shape : Shape),
      isWfShape (context.drop (n + i + 1)) shape = true →
        isWfShape ((context.drop n).drop (i + 1)) shape = true := by
    intro i shape hshape
    have hdrop : (context.drop n).drop (i + 1) = context.drop (n + i + 1) := by
      rw [List.drop_drop]
      rw [Nat.add_assoc]
    rwa [hdrop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro entry hentry
    exact h1 entry (List.mem_of_mem_drop hentry)
  · rw [List.map_drop]
    exact h2.drop
  · intro i name info hget shape hmem
    have hget' : context[n + i]? = some (name, info) := by
      rw [← List.getElem?_drop]
      exact hget
    exact hdrop_drop i shape (h3 (n + i) name info hget' shape hmem)
  · intro entry hentry
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hentry
    have hget : context[n + i]? = some entry := by
      rw [← List.getElem?_drop]
      rw [List.getElem?_eq_getElem hi]
      exact congrArg some heq
    obtain ⟨name, info⟩ := entry
    have hwfFields : isWfShape (context.drop n)
        (.comb (info.fields.map Prod.snd)) = true := by
      have hlist : isWfShape.isWfShapeList (context.drop n)
          (info.fields.map Prod.snd) = true := by
        refine isWfShapeList_of_all (fun shape hmem => ?_)
        have hshape := h3 (n + i) name info hget shape hmem
        exact isWfShape_drop (context.drop n) shape (i + 1)
          (hdrop_drop i shape hshape)
      simpa [isWfShape] using hlist
    have hsize := shapeSizeWithContext_drop context
      (.comb (info.fields.map Prod.snd)) n hwfFields h2
    have hctx := h4 (name, info) (List.mem_of_mem_drop hentry)
    rw [hsize]
    exact hctx

private theorem lookupInfoWithRest_suffix_drop (name : String)
    (context : StructContext) (info : StructInfo) (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    ∃ n, context.drop n = suffix := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        exact ⟨1, by simp⟩
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        obtain ⟨n, hn⟩ := ih hlookup
        refine ⟨n + 1, ?_⟩
        simpa [List.drop_succ_cons, Nat.succ_eq_add_one] using hn

private theorem lookupInfoWithRest_lookupInfo (name : String)
    (context : StructContext) (info : StructInfo) (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    lookupInfo name context = some info := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        simp [lookupInfo, hmatch]
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        simpa [lookupInfo, hmatch] using ih hlookup

private theorem lookupInfoWithRest_none_lookupInfo_none
    (name : String) (context : StructContext)
    (hlookup : lookupInfoWithRest name context = none) :
    lookupInfo name context = none := by
  induction context with
  | nil => simp [lookupInfo]
  | cons entry context ih =>
      obtain ⟨candidate, info⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        simpa [lookupInfo, hmatch] using ih hlookup

private theorem lookupInfoWithRest_mem [LawfulBEq String]
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    (name, info) ∈ context := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        have hname : candidate = name := LawfulBEq.eq_of_beq hmatch
        subst candidate
        simp
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

private theorem lookupInfoWithRest_fields_wf
    (name : String) (context : StructContext) (info : StructInfo)
    (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix))
    (hok : structInfosOk context) :
    isWfShape.isWfShapeList suffix (info.fields.map Prod.snd) = true := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      by_cases hmatch : candidate == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨rfl, rfl⟩
        obtain ⟨_, _, hfields, _⟩ := hok
        have hhead := hfields 0 candidate entryInfo (by simp)
        have htail : ((candidate, entryInfo) :: context).drop 1 = context := rfl
        rw [htail] at hhead
        exact isWfShapeList_of_all (fun shape hshape => hhead shape hshape)
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        exact ih hlookup (structInfosOk_drop 1 ((candidate, entryInfo) :: context) hok)

private theorem shapeSizeWithContext_fold_drop
    (context suffix : StructContext) (n : Nat) (shapes : List Shape)
    (hdrop : context.drop n = suffix)
    (hwf : isWfShape.isWfShapeList suffix shapes = true)
    (hnodup : (context.map Prod.fst).Nodup) (acc : Nat) :
    shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) acc =
      shapes.foldl (fun total shape => total + shapeSizeWithContext suffix shape) acc := by
  induction shapes generalizing acc with
  | nil => rfl
  | cons shape shapes ih =>
      have hparts : isWfShape.isWfShapeList suffix (shape :: shapes) = true := hwf
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at hparts
      have hshapeSuffix : isWfShape suffix shape = true := hparts.1
      have hshapeContext : isWfShape (context.drop n) shape = true := by
        rw [hdrop]
        exact hshapeSuffix
      have hsize := shapeSizeWithContext_drop context shape n hshapeContext hnodup
      rw [hdrop] at hsize
      have htail := ih hparts.2 (acc + shapeSizeWithContext suffix shape)
      simp only [List.foldl_cons]
      rw [← hsize]
      exact htail

/-- Size-preservation theorem for the Lean port of HOL's `mem_load_conversion`
    (`pan_structsProofScript.sml:512`). It compares Cake's context-sensitive
    shape size before and after the production `structCompileShapeWF`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag).
-- HOL `size_of_compile_shape` (`pan_structsProofScript.sml:512`) is stated over
-- `stcname`/`fldname` = `mlstring` and applies `compile_shape` to the fields
-- projection `MAP (λ(nm,info). (nm, info.fields)) ctxt`, i.e. a context
-- `(stcname # (fldname # shape) list) list` with neither `size` nor the
-- production cache. This theorem instead quantifies the production
-- `StructContext = List (StructName × StructInfo)`, where `StructName`/
-- `FieldName` = `String` and `StructInfo` carries the extra production-only
-- `shapedFields` cache, and it passes the full cache-augmented `StructInfo` to
-- `structCompileShapeWF` rather than HOL's fields projection. The carrier arity
-- and context term therefore differ beyond name representation, so the
-- `(names_as_string := ...)` qualifier does not apply and the tag stays
-- withdrawn. Faithful MlString/ShapeHOL port: `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`). Direct HOL evidence:
-- `scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`
-- (`size_of_compile_shape_comb`); Lean fixture
-- `Flapjack.Test.PanStructsCompileShapeParity`.
theorem structCompileShapeWF_size
    (context : StructContext) (shape : Shape)
    (hshape : isWfShape context shape = true) (hok : structInfosOk context) :
    shapeSizeWithContext [] (structCompileShapeWF context shape) =
      shapeSizeWithContext context shape := by
  have hsize : ∀ (context : StructContext) (shape : Shape),
      isWfShape context shape = true → structInfosOk context →
        shapeSizeWithContext [] (structCompileShapeWF context shape) =
          shapeSizeWithContext context shape := by
    intro context shape
    apply structCompileShapeWF.induct
      (motive1 := fun context shapes =>
        ∀ acc, isWfShape.isWfShapeList context shapes = true → structInfosOk context →
          shapes.foldl (fun total shape =>
            total + shapeSizeWithContext [] (structCompileShapeWF context shape)) acc =
          shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) acc)
      (motive2 := fun context shape =>
        isWfShape context shape = true → structInfosOk context →
          shapeSizeWithContext [] (structCompileShapeWF context shape) =
            shapeSizeWithContext context shape)
    · intro context acc hlist hok
      rfl
    · intro context shape shapes ihShape ihShapes acc hlist hok
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true] at hlist
      simp only [List.foldl_cons]
      rw [ihShape hlist.1 hok, ihShapes (acc + shapeSizeWithContext context shape)
        hlist.2 hok]
    · intro context hshape hok
      simp [structCompileShapeWF, shapeSizeWithContext]
    · intro context shapes ihShapes hshape hok
      have hlist : isWfShape.isWfShapeList context shapes = true := by
        simpa [isWfShape] using hshape
      rw [structCompileShapeWF.eq_def]
      change shapeSizeWithContext []
          (.comb (structCompileShapeWF.structCompileShapesWF context shapes)) =
        shapeSizeWithContext context (.comb shapes)
      rw [structCompileShapes_eq_map]
      simpa only [shapeSizeWithContext, List.foldl_map] using ihShapes 0 hlist hok
    · intro context name info suffix hlookup ihShapes hshape hok
      have hfieldsWf := lookupInfoWithRest_fields_wf name context info suffix hlookup hok
      have hdrop : ∃ n, context.drop n = suffix :=
        lookupInfoWithRest_suffix_drop name context info suffix hlookup
      obtain ⟨n, hdrop⟩ := hdrop
      have hokSuffix : structInfosOk suffix := by
        rw [← hdrop]
        exact structInfosOk_drop n context hok
      obtain ⟨_, hkeys, _, hsizes⟩ := hok
      have hmem := lookupInfoWithRest_mem name context info suffix hlookup
      have hinfoSize := hsizes (name, info) hmem
      have hfieldSizes := shapeSizeWithContext_fold_drop context suffix n
        (info.fields.map Prod.snd) hdrop hfieldsWf hkeys 0
      have htarget := ihShapes 0 hfieldsWf hokSuffix
      have hlookupInfo := lookupInfoWithRest_lookupInfo name context info suffix hlookup
      have htargetFields :
          (info.fields).foldl (fun total field =>
            total + shapeSizeWithContext [] (structCompileShapeWF suffix field.2)) 0 =
          (info.fields).foldl (fun total field =>
            total + shapeSizeWithContext suffix field.2) 0 := by
        simpa only [List.foldl_map] using htarget
      have hfieldSizesFields :
          (info.fields).foldl (fun total field =>
            total + shapeSizeWithContext context field.2) 0 =
          (info.fields).foldl (fun total field =>
            total + shapeSizeWithContext suffix field.2) 0 := by
        simpa only [List.foldl_map] using hfieldSizes
      have hinfoSizeFields : info.size =
          (info.fields).foldl (fun total field =>
            total + shapeSizeWithContext context field.2) 0 := by
        simpa only [shapeSizeWithContext, List.foldl_map] using hinfoSize
      have hcompiled : structCompileShapeWF context (.named name) =
          .comb (structCompileShapeWF.structCompileShapesWF suffix
            (info.fields.map Prod.snd)) := by
        rw [structCompileShapeWF.eq_def]
        dsimp only
        rw [hlookup]
      rw [hcompiled]
      rw [structCompileShapes_eq_map]
      simp only [shapeSizeWithContext, List.foldl_map]
      rw [htargetFields, hfieldSizesFields.symm, hinfoSizeFields.symm]
      simp [hlookupInfo]
    · intro context name hlookup hshape hok
      have hlookupInfo := lookupInfoWithRest_none_lookupInfo_none name context hlookup
      have hfalse : False := by simp [isWfShape, hlookupInfo] at hshape
      exact hfalse.elim
  exact hsize context shape hshape hok

/-- Production analogue of HOL `struct_infos_ok_append`
    (`pan_structsProofScript.sml:198`): a valid appended structure context
    remains valid in its suffix. It is untagged because HOL's contexts use
    `MlS` structure/field names, `ShapeHOL`, and a fields/size-only
    `struct_info`; this theorem uses production `String`-backed
    `StructContext`/`Shape` and cache-augmented `StructInfo.shapedFields`.
    The body relies on production String-keyed lookup through `structInfosOk`.
    `names_as_string` cannot cover the context/record difference. The single
    premise and conclusion otherwise match HOL exactly, and no name bytes are
    observable in this proposition. A faithful statement can use the exact
    `StructContextExact` carrier; name-carrier/bridge work is tracked by
    `flapjack-pxn.18.3.5.8`. -/
theorem structInfosOk_append (xs ys : StructContext)
    (h : structInfosOk (xs ++ ys)) : structInfosOk ys := by
  have hdrop := structInfosOk_drop xs.length (xs ++ ys) h
  rwa [List.drop_left] at hdrop

/-- Production analogue of HOL `struct_infos_ok_cons`
    (`pan_structsProofScript.sml:132`): adding a fresh structure with distinct
    fields, well-formed field shapes, and its computed size preserves the
    structure-context invariant. It remains untagged because HOL uses
    `MlS`/`ShapeHOL`/`StructContextExact` with the fields/size-only exact
    `struct_info`, while this statement uses String-backed production
    `StructName`, `Shape`, `StructContext`, and cache-augmented `StructInfo`.
    Its well-formedness and size premises also use production String-keyed
    lookup. The logical hypotheses and conclusion otherwise match HOL; no
    byte-observable name output is present. A faithful exact-carrier invariant
    and its cons/append theorems are tracked by
    `flapjack-pxn.18.3.5.8.18`. -/
theorem structInfosOk_cons (xs : StructContext) (nm : StructName) (info : StructInfo)
    (hxs : structInfosOk xs)
    (hflds : (info.fields.map Prod.fst).Nodup)
    (hfresh : nm ∉ xs.map Prod.fst)
    (hwf : ∀ shape ∈ info.fields.map Prod.snd, isWfShape xs shape = true)
    (hsize : info.size = shapeSizeWithContext xs (.comb (info.fields.map Prod.snd))) :
    structInfosOk ((nm, info) :: xs) := by
  obtain ⟨h1, h2, h3, h4⟩ := hxs
  have hkeys : (((nm, info) :: xs).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfresh, h2⟩
  have hdropOne : ∀ (shape : Shape),
      isWfShape xs shape = true →
      shapeSizeWithContext xs shape =
        shapeSizeWithContext ((nm, info) :: xs) shape := by
    intro shape hshape
    have hd := shapeSizeWithContext_drop ((nm, info) :: xs) shape 1
      (by simpa using hshape) hkeys
    simpa using hd
  refine ⟨?_, hkeys, ?_, ?_⟩
  · intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact hflds
    · exact h1 entry hentry
  · intro i name info' hget shape hmem
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        obtain ⟨rfl, rfl⟩ := hget
        have hdrop : ((nm, info) :: xs).drop (0 + 1) = xs := rfl
        rw [hdrop]
        exact hwf shape hmem
    | succ k =>
        simp only [List.getElem?_cons_succ] at hget
        have hdrop : ((nm, info) :: xs).drop (Nat.succ k + 1) = xs.drop (k + 1) := by
          rw [Nat.succ_eq_add_one, List.drop_succ_cons]
        rw [hdrop]
        exact h3 k name info' hget shape hmem
  · intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · have hlist : isWfShape.isWfShapeList xs (info.fields.map Prod.snd) = true :=
        isWfShapeList_of_all hwf
      have hwfComb : isWfShape xs (.comb (info.fields.map Prod.snd)) = true := by
        simpa [isWfShape] using hlist
      rw [← hdropOne (.comb (info.fields.map Prod.snd)) hwfComb]
      exact hsize
    · obtain ⟨name, info'⟩ := entry
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hentry
      have hget : xs[i]? = some (name, info') := by
        rw [List.getElem?_eq_getElem hi]
        exact congrArg some heq
      have hlist : isWfShape.isWfShapeList xs (info'.fields.map Prod.snd) = true :=
        isWfShapeList_of_all (fun shape hmem =>
          isWfShape_drop xs shape (i + 1) (h3 i name info' hget shape hmem))
      have hwfComb : isWfShape xs (.comb (info'.fields.map Prod.snd)) = true := by
        simpa [isWfShape] using hlist
      rw [← hdropOne (.comb (info'.fields.map Prod.snd)) hwfComb]
      exact h4 (name, info') hentry

/-- Production-carrier analogue of HOL's local `alookup_map_structs_ok`
    (`pan_structsProofScript.sml:243`): a found structure in a valid context
    has distinct field names. Not an exact port; see the note below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag). HOL keys
-- structure/field names by `stcname`/`fldname` = `mlstring`, its context is
-- `(stcname # struct_info) list` with `struct_info = <| fields; size |>` (exactly
-- fields and size; see the `alookup_map_structs_ok` oracle in
-- `scripts/hol-probes/afindi_probe.out`), and lookup is `ALOOKUP` over
-- `mlstring`. The Lean statement quantifies the production `StructContext =
-- List (StructName × StructInfo)` where `StructName`/`FieldName` = `String`,
-- `StructInfo` carries the extra `shapedFields` cache, and lookup is the
-- first-match `lookupInfo` requiring `[BEq String] [LawfulBEq String]`; the
-- record arity, lookup, and equality side conditions differ beyond the name
-- representation, so `(names_as_string := ...)` does not apply. The exact
-- MlString/exact-record carrier port is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`). Fixture:
-- `Flapjack.Test.PanStructsAfindiParity` instantiates this theorem on
-- `simpleContext`.
theorem lookupInfo_fields_nodup [BEq String] [LawfulBEq String] (name : String)
    (context : StructContext) (info : StructInfo)
    (hlookup : lookupInfo name context = some info)
    (hok : structInfosOk context) :
    (info.fields.map Prod.fst).Nodup := by
  induction context with
  | nil => simp [lookupInfo] at hlookup
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      simp only [lookupInfo] at hlookup
      by_cases hc : (candidate == name) = true
      · rw [if_pos hc] at hlookup
        have heq : entryInfo = info := Option.some.inj hlookup
        subst heq
        exact hok.1 (candidate, entryInfo) (by simp)
      · rw [if_neg hc] at hlookup
        exact ih hlookup (structInfosOk_drop 1 ((candidate, entryInfo) :: context) hok)

/-- Production-carrier analogue of HOL `fields_in_order_reorder_noop`
    (`pan_structsProofScript.sml:218-239`): selecting compiled fields in the
    original field-name order yields the compiled source expressions. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the field names, production
-- StructPassContext, and expression identifiers use unrestricted `String`,
-- while HOL uses `mlstring` names and its exact expression/context carriers.
-- The conclusion preserves compiled expression identifiers, so they are
-- byte-observable; there is no NameRanged premise and `names_as_string` cannot
-- bridge arbitrary inputs. Exact carrier work is tracked by
-- flapjack-pxn.18.3.5.8.
theorem fieldsInOrderReorderNoop [BEq String] [LawfulBEq String]
    (context : StructPassContext) (eflds : List (FieldName × Exp α))
    (infoFields : List (FieldName × Shape))
    (hNames : infoFields.map Prod.fst = eflds.map Prod.fst)
    (hNodup : (infoFields.map Prod.fst).Nodup) :
    structSelectFields infoFields (structCompileExp.structCompileFields context eflds) =
      eflds.map (fun field => structCompileExp context field.2) := by
  have lookup_append : ∀ (name : String) (prefixEntries entries : InfoMap (Exp α)),
      name ∉ prefixEntries.map Prod.fst →
      lookupInfo name (prefixEntries ++ entries) = lookupInfo name entries := by
    intro name prefixEntries entries hnot
    have hnone : List.lookup name prefixEntries = none := by
      rw [List.lookup_eq_none_iff]
      intro p hp
      rw [bne_iff_ne]
      intro hname
      exact hnot (List.mem_map.mpr ⟨p, hp, hname.symm⟩)
    calc
      lookupInfo name (prefixEntries ++ entries) =
          List.lookup name (prefixEntries ++ entries) :=
            lookupInfo_eq_lookup name (prefixEntries ++ entries)
      _ = List.lookup name entries := by rw [List.lookup_append, hnone]; simp
      _ = lookupInfo name entries := (lookupInfo_eq_lookup name entries).symm
  have select_append : ∀ (fields : List (FieldName × Shape))
      (prefixEntries entries : InfoMap (Exp α)),
      (∀ name ∈ fields.map Prod.fst, name ∉ prefixEntries.map Prod.fst) →
      structSelectFields fields (prefixEntries ++ entries) = structSelectFields fields entries := by
    intro fields
    induction fields with
    | nil => intro prefixEntries entries _; simp [structSelectFields]
    | cons field fields ih =>
        intro prefixEntries entries hdisjoint
        obtain ⟨name, shape⟩ := field
        have hlookup := lookup_append name prefixEntries entries (hdisjoint name (by simp))
        simp only [structSelectFields, hlookup]
        exact congrArg (fun tail : List (Exp α) =>
          match lookupInfo name entries with
          | some expression => expression :: tail
          | none => tail)
          (ih prefixEntries entries (fun other hmem =>
            hdisjoint other (by simp [hmem])))
  induction eflds generalizing infoFields with
  | nil =>
      cases infoFields with
      | nil => simp [structSelectFields]
      | cons field fields => simp at hNames
  | cons field eflds ih =>
      obtain ⟨name, expression⟩ := field
      cases infoFields with
      | nil => simp at hNames
      | cons field infoFields =>
          obtain ⟨infoName, shape⟩ := field
          simp only [List.map_cons, List.cons.injEq] at hNames
          rcases hNames with ⟨hHead, hNames⟩
          simp only [List.map_cons, List.nodup_cons] at hNodup
          have hFresh : infoName ∉ infoFields.map Prod.fst := hNodup.1
          have hFresh' : name ∉ infoFields.map Prod.fst := by
            simpa [hHead] using hFresh
          have hTailNames : infoFields.map Prod.fst = eflds.map Prod.fst := hNames
          have hTailNodup : (infoFields.map Prod.fst).Nodup := hNodup.2
          simp only [structSelectFields, structCompileExp.structCompileFields,
            hHead, lookupInfo, beq_self_eq_true, if_true]
          have hdisjoint : ∀ other ∈ infoFields.map Prod.fst,
              other ∉ [(name, structCompileExp context expression)].map Prod.fst := by
            intro other hmem
            have hne : other ≠ name := by
              intro heq
              subst heq
              exact hFresh' hmem
            simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false]
            exact hne
          change structCompileExp context expression ::
              structSelectFields infoFields
                ([(name, structCompileExp context expression)] ++
                  structCompileExp.structCompileFields context eflds) =
            structCompileExp context expression ::
              eflds.map (fun field => structCompileExp context field.2)
          rw [select_append infoFields [(name, structCompileExp context expression)]
            (structCompileExp.structCompileFields context eflds) hdisjoint]
          have htail := ih infoFields hTailNames hTailNodup
          simpa only [List.map_cons, Prod.snd] using
            congrArg (fun tail => structCompileExp context expression :: tail) htail

/-- Exact translation of HOL `opt_mmap_eq_every`
    (`pan_structsProofScript.sml:255`): if production `List.mapM` succeeds,
    every successful image satisfying `P` makes the result satisfy `P`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_every"]
theorem list_mapM_all_of_mem {α β : Type} (f : α → Option β) (P : β → Bool)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys)
    (hf : ∀ x y, x ∈ xs → f x = some y → P y = true) :
    ys.all P = true := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil] at h
      cases h
      simp
  | cons a as ih =>
      rw [List.mapM_cons] at h
      cases hx : f a with
      | none => simp [hx] at h
      | some b =>
          simp only [hx] at h
          cases hxs : as.mapM f with
          | none => simp [hxs] at h
          | some ys' =>
              simp only [hxs] at h
              have hb : b :: ys' = ys := by simpa using h
              subst hb
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨hf a b (by simp) hx,
                ih ys' hxs (fun x y hx' hfy => hf x y (by simp [hx']) hfy)⟩

/-- Exact port of HOL `dropWhile_MAP_helper`
    (`pan_structsProofScript.sml:542`): mapping commutes with `dropWhile` when
    the source and mapped predicates agree on every source element. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_MAP_helper"]
theorem dropWhile_map_helper {α β : Type} (P : α → Bool) (Q : β → Bool)
    (f : α → β) (xs : List α) (ys : List α)
    (h : xs.dropWhile P = ys)
    (hPQ : ∀ x ∈ xs, P x = Q (f x)) :
    (xs.map f).dropWhile Q = ys.map f := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.dropWhile_nil] at h
      subst h
      simp
  | cons x xs ih =>
      have hx : P x = Q (f x) := hPQ x (by simp)
      rw [List.dropWhile_cons] at h
      by_cases hP : P x = true
      · rw [if_pos hP] at h
        have hQ : Q (f x) = true := by rw [← hx]; exact hP
        rw [List.map_cons, List.dropWhile_cons, hQ]
        simp only [if_true]
        exact ih ys h (fun y hy => hPQ y (by simp [hy]))
      · rw [if_neg hP] at h
        have hPfalse : P x = false := by simpa using hP
        have hQ : Q (f x) = false := by rw [← hx]; exact hPfalse
        rw [← h, List.map_cons, List.dropWhile_cons, hQ]
        simp only [Bool.false_eq_true, if_false]

/-- Production-carrier analogue of HOL `old_exp_shapes_eq`
    (`pan_structsProofScript.sml:679-683`): the production old-shape list
    helper equals `List.map` of its single-expression helper. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the generic production `Exp α`,
-- `Shape`, and `StructPassContext` use unrestricted `String` identifiers;
-- HOL uses its expression/shape carriers with `mlstring` names. In
-- particular, `NStruct` returns its input name as a named shape, and no
-- NameRanged premise restricts that byte-observable value. `names_as_string`
-- cannot bridge arbitrary names; exact-carrier work is tracked by
-- flapjack-pxn.18.3.5.8.
theorem structOldExpShapes_eq_map {α : Type} (context : StructPassContext) :
    (structOldExpShape.structOldExpShapes (α := α) context :
      List (Exp α) → List Shape) =
      fun expressions => expressions.map (structOldExpShape context) := by
  funext expressions
  induction expressions with
  | nil => simp [structOldExpShape.structOldExpShapes]
  | cons expression expressions ih =>
      simp [structOldExpShape.structOldExpShapes, ih]

/-- Cake's `opt_mmap_eq_some_el`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:19`). The `getElem?`
    formulation is the total Lean translation of HOL's total `EL`: under the
    in-range premise, each optional lookup succeeds and supplies that element. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_some_el"]
theorem optMmapEqSomeEl {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔
      xs.length = ys.length ∧ ∀ n, n < ys.length → (xs[n]?).bind f = ys[n]? := by
  induction xs generalizing ys with
  | nil =>
      constructor
      · intro h
        cases h
        simp
      · intro h
        obtain ⟨hlen, _⟩ := h
        have : ys = [] := by simpa using hlen.symm
        subst this
        rfl
  | cons x xs ih =>
      rw [List.mapM_cons]
      constructor
      · intro h
        cases hx : f x with
        | none => simp [hx] at h
        | some b =>
            simp only [hx] at h
            cases hxs : xs.mapM f with
            | none => simp [hxs] at h
            | some ys' =>
                simp only [hxs] at h
                have hb : b :: ys' = ys := by simpa using h
                subst hb
                obtain ⟨hlen, hpt⟩ := (ih ys').mp hxs
                refine ⟨by simp [hlen], ?_⟩
                intro n hn
                cases n with
                | zero => simp [hx]
                | succ m =>
                    simp only [List.getElem?_cons_succ, List.length_cons] at hn ⊢
                    have hm : m < ys'.length := by omega
                    simpa using hpt m hm
      · intro h
        obtain ⟨hlen, hpt⟩ := h
        cases ys with
        | nil => simp at hlen
        | cons b ys' =>
            have hfx : f x = some b := by
              have := hpt 0 (by simp)
              simpa using this
            have htail : xs.length = ys'.length ∧
                ∀ n, n < ys'.length → (xs[n]?).bind f = ys'[n]? := by
              refine ⟨by simpa using hlen, ?_⟩
              intro n hn
              have := hpt (n + 1) (by simp; omega)
              simpa [List.getElem?_cons_succ] using this
            have hxs : xs.mapM f = some ys' := (ih ys').mpr htail
            simp [hfx, hxs]

/-! Faithful port of Cake `afindi_less_length`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:345`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_less_length"]
theorem afindi_less_length [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index → index < entries.length := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          have hlt := ih found hfound
          simp only [List.length_cons]
          omega

/-! Faithful Lean indexing form of Cake `afindi_EL`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:430`). Given the
    successful search, `getElem?` is `some` exactly at the in-range `EL` index. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_EL"]
theorem afindi_el_fst [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index →
        (entries[index]?).map Prod.fst = some key := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · rename_i hbeq
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.getElem?_cons_zero, Option.map_some]
        exact congrArg some hbeq.symm
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.getElem?_cons_succ]
          exact ih found hfound

/-! Faithful port of Cake `afindi_append`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:417`). The source uses
    `LENGTH xs + index`; this Lean statement writes the commuted Nat sum. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_append"]
theorem afindi_append [DecidableEq α] (key : α) (xs ys : List (α × β)) :
    afindi key (xs ++ ys) =
      (match afindi key xs with
        | none => (afindi key ys).map (fun index => index + xs.length)
        | some index => some index) := by
  induction xs with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi, hbeq]
      · simp only [List.cons_append, afindi, hbeq]
        rw [ih]
        cases ha : afindi key rest with
        | none =>
            cases hb : afindi key ys with
            | none => simp
            | some index => simp; omega
        | some index => simp

/-! Faithful port of Cake `afindi_MAP_eq`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:356`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_MAP_eq"]
theorem afindi_map_eq [DecidableEq α] (key : α) (f : α × β → α × γ)
    (entries : List (α × β))
    (hf : ∀ x y, (x, y) ∈ entries → (f (x, y)).1 = x) :
    afindi key (entries.map f) = afindi key entries := by
  induction entries with
  | nil => simp only [List.map_nil, afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      have hhead : (f (candidate, value)).1 = candidate :=
        hf candidate value (by simp)
      have htail : ∀ x y, (x, y) ∈ rest → (f (x, y)).1 = x :=
        fun x y hxy => hf x y (by simp [hxy])
      simp only [List.map_cons]
      rw [afindi_cons, afindi_cons, hhead, ih htail]

/-! Faithful API translation of Cake `dropWhile_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:334`). HOL's logical
    inequality predicate is expressed with `decide` for Lean's Bool-valued
    `List.dropWhile`; HOL `DROP` translates to `List.drop`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_afindi"]
theorem afindi_dropWhile [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.dropWhile (fun entry => decide (key ≠ entry.1)) =
      match afindi key entries with
      | none => []
      | some index => entries.drop index := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hb : key = candidate
      · simp [afindi_cons, hb]
      · have hdec : decide (key ≠ candidate) = true := by simp [hb]
        simp only [List.dropWhile_cons, afindi_cons, hdec, if_neg hb]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.drop_succ_cons]

/-! Faithful API translation of Cake `ALOOKUP_eq_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:405`). `List.lookup`
    translates `ALOOKUP`; the optional indexed projection translates HOL's
    `OPTION_MAP` of `SND ∘ EL`, with `afindi_less_length` ensuring successful
    indices are in range. Its synthesized `BEq` comes from `DecidableEq`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "ALOOKUP_eq_afindi"]
theorem afindi_lookup [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.lookup key =
      (afindi key entries).bind (fun index => (entries[index]?).map Prod.snd) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi_cons, hbeq]
      · have hbeq' : (key == candidate) = false := by
          simp [BEq.beq, hbeq]
        simp only [List.lookup_cons, hbeq', afindi_cons, if_neg hbeq]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.getElem?_cons_succ]

/-! Helper for Cake's local `map_fst_eq_alookup`: equal key lists imply
    identical `afindi` positions. This intermediate theorem is not a separate
    HOL declaration, so it has no `@[hol]` tag. -/
theorem afindi_eq_of_map_fst_eq [DecidableEq α] (key : α) :
    ∀ (xs : List (α × β)) (ys : List (α × γ)), xs.map Prod.fst = ys.map Prod.fst →
      afindi key xs = afindi key ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp only [List.map_nil] at h
      have hy : ys = [] := (List.map_eq_nil_iff.mp h.symm)
      subst hy
      simp [afindi]
  | cons x xs ih =>
      intro ys h
      obtain ⟨cx, vx⟩ := x
      cases ys with
      | nil => simp at h
      | cons y ys =>
          obtain ⟨cy, vy⟩ := y
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hhead, htail⟩ := h
          have hcy : cx = cy := hhead
          subst hcy
          by_cases hbc : key = cx
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_pos hbc, if_pos hbc]
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_neg hbc, if_neg hbc, ih ys htail]

/-- HOL `map_fst_eq_alookup` (`pan_structsProofScript.sml:278`) has key type
    `α`, xs value type `β`, and ys value type `γ`; the source syntax leaves all
    three polymorphic. The direct HOL type probe confirms
    `xs : (α × β) list`, `ys : (α × γ) list`, `nm : α`, and `v : β`. Lean keeps
    those independent carriers. Its `Option.map` projections are the list-index
    API form of HOL `SND (EL i ...)` under the explicit bounds. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_fst_eq_alookup"]
theorem map_fst_eq_lookup [DecidableEq α]
    (xs : List (α × β)) (ys : List (α × γ)) (nm : α) {v : β}
    (hlen : xs.map Prod.fst = ys.map Prod.fst)
    (hlookup : xs.lookup nm = some v) :
    ∃ i, afindi nm xs = some i ∧ afindi nm ys = some i ∧
      i < xs.length ∧ i < ys.length ∧
      (xs[i]?).map Prod.snd = some v ∧ (ys[i]?).map Prod.snd = ys.lookup nm := by
  have hafindi := afindi_eq_of_map_fst_eq nm xs ys hlen
  have hbridge := afindi_lookup nm xs
  rw [hlookup] at hbridge
  cases h : afindi nm xs with
  | none =>
      rw [h] at hbridge
      simp at hbridge
  | some i =>
      rw [h] at hbridge
      simp only [Option.bind_some] at hbridge
      have hxs : (xs[i]?).map Prod.snd = some v := hbridge.symm
      have hi_xs : i < xs.length := afindi_less_length nm xs i h
      have hys : afindi nm ys = some i := by rw [← hafindi]; exact h
      have hi_ys : i < ys.length := afindi_less_length nm ys i hys
      have hybridge := afindi_lookup nm ys
      rw [hys] at hybridge
      simp only [Option.bind_some] at hybridge
      refine ⟨i, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact hys
      · exact hi_xs
      · exact hi_ys
      · exact hxs
      · exact hybridge.symm

end Flapjack
