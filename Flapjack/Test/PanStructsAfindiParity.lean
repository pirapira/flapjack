import Flapjack.PanStructsAfindi

namespace Flapjack.Test.PanStructsAfindiParity

/-! Direct parity for `pan_structs$afindi_def`
    (`pan_structsScript.sml:25`). -/
def entries : List (String × Nat) := [("a", 10), ("b", 20), ("c", 30)]

def parityGuard : Bool :=
  (afindi "a" ([] : List (String × Nat)) == none) &&
  (afindi "a" entries == some 0) &&
  (afindi "b" entries == some 1) &&
  (afindi "c" entries == some 2) &&
  (afindi "z" entries == none) &&
  (afindi "a" [("a", 10), ("b", 20), ("a", 30)] == some 0)

#eval parityGuard
#guard parityGuard

/-! Focused regressions for the ported Cake `pan_structs` `afindi` lemmas
    (`afindi_less_length`, `afindi_EL`, `afindi_append`, `afindi_MAP_eq`). -/

theorem afindi_less_length_fixture :
    afindi "b" entries = some 1 → (1 : Nat) < entries.length := by
  intro h
  exact afindi_less_length "b" entries 1 h

theorem afindi_el_fst_fixture : (entries[1]?).map Prod.fst = some "b" := by
  have h : afindi "b" entries = some 1 := by simp [afindi, entries]
  exact afindi_el_fst "b" entries 1 h

theorem afindi_append_fixture :
    afindi "d" (entries ++ [("d", 40)]) =
      (match afindi "d" entries with
        | none => (afindi "d" [("d", 40)]).map (fun index => index + entries.length)
        | some index => some index) := by
  exact afindi_append "d" entries [("d", 40)]

theorem afindi_append_value_fixture :
    afindi "d" (entries ++ [("d", 40)]) = some 3 := by
  simp [afindi, entries]

theorem afindi_map_eq_fixture :
    afindi "c" (entries.map (fun entry => (entry.1, entry.2 + 1))) =
      afindi "c" entries := by
  exact afindi_map_eq "c" (fun entry => (entry.1, entry.2 + 1)) entries
    (by intro x y _; rfl)

theorem afindi_dropWhile_fixture :
    entries.dropWhile (fun entry => !("b" == entry.1)) = entries.drop 1 := by
  rw [afindi_dropWhile]
  simp [afindi, entries]

theorem afindi_lookup_fixture :
    entries.lookup "b" = some 20 := by
  rw [afindi_lookup]
  simp [afindi, entries]
/-! Focused regressions for the ported Cake `pan_structs` `is_wf_shape_drop`
    lemma and its `lookupInfo` helper. -/

def context : StructContext :=
  [("t", { fields := [], size := 0 }),
   ("s", { fields := [("x", Shape.one)], size := 1 })]

theorem lookupInfo_isSome_drop_fixture :
    (lookupInfo "s" (context.drop 1)).isSome = true := by
  simp [context, lookupInfo]

theorem isWfShape_drop_fixture : isWfShape context (.named "s") = true := by
  have h : isWfShape (context.drop 1) (.named "s") = true := by
    simp [context, isWfShape, lookupInfo]
  exact isWfShape_drop (.named "s") context 1 h

/-! Focused regression for the ported Cake `pan_structs` `alookup_drop_helper`
    lemma. -/

theorem lookup_drop_helper_fixture :
    "b" ∉ (entries.take 1).map Prod.fst ∧ List.lookup "b" entries = some 20 :=
  lookup_drop_helper 1 entries "b" 20 (by decide) (by decide)

/-! Focused regression for the ported Cake `pan_structs`
    `map_uncurry_zip_again` lemma. -/

theorem list_zip_map_eq_fixture :
    (([1, 2] : List Nat).zip ([10, 20] : List Nat)).map
        (fun p => (p.1 + 1, p.2 * 2)) = ([2, 3] : List Nat).zip ([20, 40] : List Nat) :=
  list_zip_map_eq (fun n : Nat => n + 1) (fun n : Nat => n * 2) [1, 2] [10, 20] rfl

/-- Parity check for the Cake `UNCURRY_EQ_o_SND` lemma. -/
theorem prod_uncurry_const_eq_comp_snd_fixture :
    Function.uncurry (fun _ : Nat => (fun n : Nat => n + 1)) =
        (fun n : Nat => n + 1) ∘ Prod.snd :=
  prod_uncurry_const_eq_comp_snd (fun n : Nat => n + 1)

/-! Focused regressions for the ported Cake `pan_structs` `alookup_drop_helper`
    specialisation to `lookupInfo` and `size_of_sh_with_ctxt_drop`. -/

theorem lookupInfo_eq_lookup_fixture :
    lookupInfo "b" entries = List.lookup "b" entries :=
  lookupInfo_eq_lookup "b" entries

theorem lookupInfo_drop_helper_fixture :
    lookupInfo "s" context = some { fields := [("x", Shape.one)], size := 1 } :=
  lookupInfo_drop_helper 1 context "s" _ (by simp [context, lookupInfo]) (by decide)

theorem isWfShape_of_mem_fixture : isWfShape context (.named "s") = true :=
  isWfShape_of_mem (context := context) (shapes := [Shape.one, .named "s"])
    (by
      simp only [isWfShape.isWfShapeList.eq_def, isWfShape, context, lookupInfo]
      rfl) (by simp)

theorem shapeSizeWithContext_drop_fixture :
    shapeSizeWithContext (context.drop 1) (.named "s") =
      shapeSizeWithContext context (.named "s") := by
  have h : isWfShape (context.drop 1) (.named "s") = true := by
    simp [context, isWfShape, lookupInfo]
  exact shapeSizeWithContext_drop 1 context (.named "s") h (by decide)

/-! Focused regression for the ported Cake `size_of_sh_with_ctxt_eq`
    (`panPropsScript.sml:184`): for a shape well formed against the empty
    context the context-sensitive size is the context-free `shapeSize`. -/

theorem shapeSizeWithContext_eq_shapeSize_of_isWfShape_fixture :
    shapeSizeWithContext ([] : StructContext)
        (Shape.comb [Shape.one, Shape.one]) =
      Shape.shapeSize (Shape.comb [Shape.one, Shape.one]) :=
  shapeSizeWithContext_eq_shapeSize_of_isWfShape
    (Shape.comb [Shape.one, Shape.one])
    (by simp [isWfShape, isWfShape.isWfShapeList]) ([] : StructContext)

def shapeSizeWithContextGuard : Bool :=
  shapeSizeWithContext ([] : StructContext) (Shape.comb [Shape.one, Shape.one]) ==
    Shape.shapeSize (Shape.comb [Shape.one, Shape.one])

#eval shapeSizeWithContextGuard
#guard shapeSizeWithContextGuard

/-! Focused regression for the ported Cake `dropWhile_eq_cons_IMP`
    (`panPropsScript.sml:74`). -/

theorem dropWhile_eq_cons_imp_fixture :
    ∃ n, n < ([0, 1, 3] : List Nat).length ∧
      ([0, 1, 3] : List Nat)[n]? = some 3 ∧ (decide ((3 : Nat) < 2) = false) ∧
      ([0, 1, 3] : List Nat).drop n = [3] :=
  dropWhile_eq_cons_imp (fun n : Nat => n < 2) [0, 1, 3] 3 [] (by decide)

#check @dropWhile_eq_cons_imp

end Flapjack.Test.PanStructsAfindiParity
