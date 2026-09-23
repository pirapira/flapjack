import Flapjack.Pancake.PanStatic
import Flapjack.Pancake.Proofs.PanStructs

/-!
Residual named-structure proof helpers retained from the earlier
`PanStructsAfindi` module. The executable `afindi` definition and its
declaration-level proof ports now live under `Flapjack/Pancake`.
-/

namespace Flapjack

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

end Flapjack
