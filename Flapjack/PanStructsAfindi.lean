import Flapjack.Pancake.PanStatic
import Flapjack.Pancake.Proofs.PanStructs

/-!
Residual named-structure proof helpers retained from the earlier
`PanStructsAfindi` module. The executable `afindi` definition and its
declaration-level proof ports now live under `Flapjack/Pancake`.
-/

namespace Flapjack

/-- Cake `pan_structs` `map_uncurry_zip_again`: mapping an uncurried pair
constructor over a `zip` equals the `zip` of the two maps. -/
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

/-- Cake `pan_structs` `UNCURRY_EQ_o_SND`: an uncurried constant pair
function is the constant composed with `SND`. -/
theorem prod_uncurry_const_eq_comp_snd {α β γ : Type} (f : β → γ) :
    Function.uncurry (fun _ : α => f) = f ∘ Prod.snd := by
  funext p
  cases p
  rfl

/-! These helpers and the exact shape-size theorem now live in the Pancake
    proof counterpart. -/

/-- Cake's `dropWhile_eq_cons_IMP`
(`cakeml/pancake/semantics/panPropsScript.sml:74-86`): if `dropWhile P xs`
returns a nonempty list headed by `y`, then `y` is some element of `xs` at
which `P` first fails, and `drop` at that index yields the same tail. -/
theorem dropWhile_eq_cons_imp {α : Type} (P : α → Bool) (xs : List α)
    (y : α) (ys : List α) (h : xs.dropWhile P = y :: ys) :
    ∃ n, n < xs.length ∧ xs[n]? = some y ∧ P y = false ∧ xs.drop n = y :: ys := by
  induction xs generalizing y ys with
  | nil => simp at h
  | cons x rest ih =>
      cases hP : P x with
      | false =>
          simp only [List.dropWhile_cons, hP, Bool.false_eq_true, if_false] at h
          cases h
          exact ⟨0, by simp, by simp, hP, by simp⟩
      | true =>
          simp only [List.dropWhile_cons, hP, if_true] at h
          obtain ⟨n, hn, hget, hpy, hdrop⟩ := ih y ys h
          refine ⟨n + 1, by simpa using hn, ?_, hpy, ?_⟩
          · simpa [List.getElem?_cons_succ] using hget
          · simpa [List.drop_succ_cons] using hdrop

theorem lookupInfoWithRest_length_lt [BEq String] {name : String}
    {context : StructContext} {info : StructInfo} {rest : StructContext}
    (h : lookupInfoWithRest name context = some (info, rest)) :
    rest.length < context.length := by
  induction context with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry context ih =>
      obtain ⟨candidate, entryInfo⟩ := entry
      simp only [lookupInfoWithRest] at h
      by_cases hc : (candidate == name) = true
      · rw [if_pos hc] at h
        have hrest : context = rest := by
          simpa using congrArg Prod.snd (Option.some.inj h)
        subst hrest
        simp
      · rw [if_neg hc] at h
        have := ih h
        simp only [List.length_cons]
        omega

mutual
  /-- Counterpart of Cake's `pan_structs$compile_shape`
      (`cakeml/pancake/pan_structsScript.sml:37`): resolve every named shape in
      the struct context into the combination of its field shapes, using the
      remaining context for nested names. -/
  def compileShape [BEq String] (context : StructContext) (shape : Shape) : Shape :=
    match shape with
    | .one => .one
    | .comb shapes => .comb (compileShapes context shapes)
    | .named name =>
        match _hlookup : lookupInfoWithRest name context with
        | some (info, rest) =>
            .comb (compileShapes rest (info.fields.map Prod.snd))
        | none => .one
  termination_by (context.length, sizeOf shape)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (lookupInfoWithRest_length_lt (by assumption))
      | exact Prod.Lex.right _ (by decreasing_trivial)

  def compileShapes [BEq String] (context : StructContext) (shapes : List Shape) :
      List Shape :=
    match shapes with
    | [] => []
    | shape :: rest => compileShape context shape :: compileShapes context rest
  termination_by (context.length, sizeOf shapes)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (lookupInfoWithRest_length_lt (by assumption))
      | exact Prod.Lex.right _ (by decreasing_trivial)
end

/-- Counterpart of Cake's `compile_shapes_eq_map`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:310`). -/
theorem compileShapes_eq_map [BEq String] (context : StructContext)
    (shapes : List Shape) :
    compileShapes context shapes = shapes.map (compileShape context) := by
  induction shapes with
  | nil => simp [compileShapes]
  | cons shape rest ih => simp [compileShapes, ih]

/-- Counterpart of the first conjunct of Cake's `is_wf_shape_compile_shape`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:298`): a compiled shape
    is well formed in every context, because it contains no named shapes. -/
theorem compileShape_isWfShape_of [BEq String] (outer : StructContext)
    (context : StructContext) (shape : Shape) :
    isWfShape outer (compileShape context shape) = true := by
  have hmain : ∀ outer : StructContext, ∀ context shape,
      isWfShape outer (compileShape context shape) = true := by
    intro outer
    apply compileShape.induct
      (motive1 := fun context shape => isWfShape outer (compileShape context shape) = true)
      (motive2 := fun context shapes =>
        isWfShape.isWfShapeList outer (compileShapes context shapes) = true)
    · intro context
      simp [compileShape, isWfShape]
    · intro context shapes ih
      simp only [compileShape, isWfShape]
      exact ih
    · intro context name info rest hlookup ih
      rw [compileShape.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
      exact ih
    · intro context name hlookup
      rw [compileShape.eq_def]
      dsimp only
      rw [hlookup]
      simp [isWfShape]
    · intro context
      simp [compileShapes, isWfShape.isWfShapeList]
    · intro context shape rest ihHead ihTail
      simp only [compileShapes, isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨ihHead, ihTail⟩
  exact hmain outer context shape

/-- Cake's `is_wf_shape_compile_shape` at the shape level. -/
theorem compileShape_isWfShape [BEq String] (context : StructContext)
    (shape : Shape) : isWfShape context (compileShape context shape) = true :=
  compileShape_isWfShape_of context context shape

/-- Counterpart of the second conjunct of Cake's `is_wf_shape_compile_shape`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:298`). -/
theorem compileShapes_isWfShape [BEq String] (outer : StructContext)
    (context : StructContext) (shapes : List Shape) :
    isWfShape.isWfShapeList outer (compileShapes context shapes) = true := by
  rw [compileShapes_eq_map]
  induction shapes with
  | nil => simp [isWfShape.isWfShapeList]
  | cons shape rest ih =>
      simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨compileShape_isWfShape_of outer context shape, ih⟩

theorem isWfShapeList_of_all {context : StructContext} {shapes : List Shape}
    (h : ∀ shape ∈ shapes, isWfShape context shape = true) :
    isWfShape.isWfShapeList context shapes = true := by
  induction shapes with
  | nil => simp [isWfShape.isWfShapeList]
  | cons s ss ih =>
      simp only [isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨h s (by simp), ih (fun t ht => h t (by simp [ht]))⟩

/-- Cake `pan_structs` `struct_infos_ok`: the structure context records distinct
    field names, distinct structure names, well-formed field shapes (each
    resolved in the context suffix after its own entry) and matching sizes. -/
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

theorem structInfosOk_append (xs ys : StructContext)
    (h : structInfosOk (xs ++ ys)) : structInfosOk ys := by
  have hdrop := structInfosOk_drop xs.length (xs ++ ys) h
  rwa [List.drop_left] at hdrop

/-- Cake `pan_structs` `struct_infos_ok_cons`: prepending a fresh structure
    whose fields are distinct, whose shapes are well formed in the existing
    context and whose recorded size matches keeps the context well formed. -/
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

/-- Cake `pan_structs` `alookup_map_structs_ok`: a structure found in a
    well-formed context has distinct field names. -/
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

end Flapjack
