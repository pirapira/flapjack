import Flapjack.PanProgramSemantics
import Flapjack.PanSimp

/-!
Counterpart of Cake's `decs_stcnames_compile_prog`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1334-1341`):

    !ctxt pan_code. decs_stcnames ctxt (compile_prog pan_code) =
                    decs_stcnames ctxt pan_code

Flapjack's `collectPanValueStructs` is the executable counterpart of Cake's
`decs_stcnames` (`cakeml/pancake/semantics/panSemScript.sml:839-859`), and
`panSimpDecls` is the counterpart of `pan_simp$compile_prog`.  Because
`pan_simp` rewrites only function bodies and leaves every other declaration
constructor untouched, it cannot change the struct-name context that
`collectPanValueStructs` accumulates. -/

namespace Flapjack

/-- Cons equation for `collectPanValueStructs`, mirroring Cake's
    `decs_stcnames_def`. -/
theorem collectPanValueStructs_cons (declaration : Decl α) (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (declaration :: declarations) context =
      (match declaration with
       | .name name fields =>
           if (lookupInfo name context).isSome then none
           else if !(fields.map (fun field => field.1)).Nodup then none
           else if !fields.all (fun field => isWfShape context field.2) then none
           else collectPanValueStructs declarations
                  ((name, panValueDeclStructInfo context fields) :: context)
       | _ => collectPanValueStructs declarations context) := by
  cases declaration <;> rw [collectPanValueStructs.eq_def]

/-- Cake's `decs_stcnames_compile_prog`: `pan_simp` preserves the
    struct-name context collected from a declaration list. -/
theorem collectPanValueStructs_panSimpDecls (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (panSimpDecls declarations) context =
      collectPanValueStructs declarations context := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      simp only [List.map_cons]
      cases declaration <;>
        simp [panSimpDecl, collectPanValueStructs_cons, ih]

/-! Cake's `OPT_MMAP` is `List.mapM` for `Option`, so the list-mapping helper
lemmas used by `compile_correct` (`cakeml/pancake/proofs/pan_simpProofScript.sml`)
have the following `List.mapM` counterparts.  These are the pieces needed to
transfer an `OPT_MMAP (eval s) es = SOME vs` hypothesis to a related state `t`
(`opt_mmap_eq_some_helper`, `OPT_MMAP_NONE`, `OPT_MMAP_NONE'`). -/

/-- Cake's `opt_mmap_eq_some_helper` (`pan_simpProofScript.sml:394`): if two
    functions agree on every element that the first maps successfully, then
    mapping the second succeeds with the same result. -/
theorem list_mapM_eq_some_of_eq_some {α β : Type} (f g : α → Option β) :
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
              rw [list_mapM_eq_some_of_eq_some f g xs ys hys
                    (fun z hz' b hb => hfg z (by simp [hz']) b hb)]
              rfl

/-- Cake's `OPT_MMAP_NONE` (`pan_simpProofScript.sml:500`): a failing map has
    a failing element. -/
theorem list_mapM_eq_none_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : xs.mapM f = none) : ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => exact ⟨x, by simp, hx⟩
      | some y =>
          cases hys : List.mapM f xs with
          | none =>
              obtain ⟨z, hz, hfz⟩ := ih hys
              exact ⟨z, by simp [hz], hfz⟩
          | some ys =>
              simp [hys] at h
              exact absurd hx (h y)

/-- Cake's `OPT_MMAP_NONE'` (`pan_simpProofScript.sml:509`): a failing element
    makes the whole map fail. -/
theorem list_mapM_eq_none_of_mem {α β : Type} (f : α → Option β) {x : α} {xs : List α}
    (hx : x ∈ xs) (hf : f x = none) : xs.mapM f = none := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mapM_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [hf]
      · cases hy : f y with
        | none => simp
        | some b => simp [ih hx']

end Flapjack
