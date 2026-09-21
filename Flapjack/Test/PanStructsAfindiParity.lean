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

end Flapjack.Test.PanStructsAfindiParity
