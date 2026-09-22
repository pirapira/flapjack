import Flapjack.CompileParamVarsBounds

/-!
Equations for the formal-parameter metadata produced by `compileParamVars`.

The compiler keeps both a name/shape/slot table and the flattened parameter
vector.  These projections are definitionally related, but naming the
equations avoids unfolding the allocator in callee-call correctness proofs.
-/

namespace Flapjack

/-! The third component of `compileParamVars` is the next free slot.  Cake's
    source-shaped `comp_func` uses the preceding slot as `vmax`, so keeping
    this equation explicit prevents the two context conventions from being
    conflated in correctness proofs. -/
theorem compileParamVars_next_offset
    (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).2.snd =
      offset + Shape.shapeSize (.comb (params.map Prod.snd)) := by
  induction params generalizing offset with
  | nil =>
      simp [compileParamVars, Shape.shapeSize]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars]
          rw [ih]
          simp [shapeSize_comb_cons, Nat.add_assoc]

theorem compileParamVars_preserves_parameter_shapes
    (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).1.map
        (fun entry => (entry.1, entry.2.1)) = params := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars, List.map_cons]
          rw [ih]

theorem compileParamVars_flattened_slots
    (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).2.1 =
      (compileParamVars params offset).1.flatMap (fun entry => entry.2.2) := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars]
          rw [ih]
          rfl

theorem lookupInfo_reverse_of_nodup
    [LawfulBEq String]
    (name : String) (entries : InfoMap β)
    (hnodup : entries.map Prod.fst |>.Nodup) :
    lookupInfo name entries = lookupInfo name entries.reverse := by
  have lookupInfo_none_of_not_mem : ∀ (entries : InfoMap β),
      name ∉ entries.map Prod.fst → lookupInfo name entries = none := by
    intro entries
    induction entries with
    | nil => simp [lookupInfo]
    | cons entry entries ih =>
        rcases entry with ⟨candidate, value⟩
        intro hnot
        have hcandidate : candidate ≠ name := by
          intro heq
          apply hnot
          simp [heq]
        have htail : name ∉ entries.map Prod.fst := by
          intro hmem
          apply hnot
          simp [hmem]
        simp [lookupInfo, hcandidate, ih htail]
  have lookupInfo_append_of_ne_local : ∀ (entries : InfoMap β)
      (newName : String) (value : β), name ≠ newName →
      lookupInfo name (entries ++ [(newName, value)]) = lookupInfo name entries := by
    intro entries
    induction entries with
    | nil =>
        intro newName value hne
        simp [lookupInfo, Ne.symm hne]
    | cons entry entries ih =>
        rcases entry with ⟨candidate, candidateValue⟩
        intro newName value hne
        by_cases hcandidate : candidate = name
        · subst candidate
          simp [lookupInfo]
        · simp [lookupInfo, hcandidate, ih newName value hne]
  have lookupInfo_append_new_local : ∀ (entries : InfoMap β)
      (value : β), lookupInfo name entries = none →
      lookupInfo name (entries ++ [(name, value)]) = some value := by
    intro entries
    induction entries with
    | nil =>
        intro value hnone
        simp [lookupInfo]
    | cons entry entries ih =>
        rcases entry with ⟨candidate, candidateValue⟩
        intro value hnone
        by_cases hcandidate : candidate = name
        · subst candidate
          simp [lookupInfo] at hnone
        · simp [lookupInfo, hcandidate] at hnone ⊢
          exact ih value hnone
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      have htail : entries.map Prod.fst |>.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hcandidate : candidate ∉ entries.map Prod.fst :=
        (List.nodup_cons.mp hnodup).1
      by_cases hname : candidate = name
      · have hnone : lookupInfo name entries.reverse = none := by
          apply lookupInfo_none_of_not_mem
          simpa [hname] using hcandidate
        calc
          lookupInfo name ((candidate, value) :: entries) = some value := by
            simp [lookupInfo, hname]
          _ = lookupInfo name ((candidate, value) :: entries).reverse := by
            rw [List.reverse_cons]
            simpa [hname] using
              (lookupInfo_append_new_local entries.reverse value hnone).symm
      · have hlookup := ih htail
        calc
          lookupInfo name ((candidate, value) :: entries) = lookupInfo name entries := by
            simp [lookupInfo, hname]
          _ = lookupInfo name entries.reverse := hlookup
          _ = lookupInfo name ((candidate, value) :: entries).reverse := by
            rw [List.reverse_cons]
            exact (lookupInfo_append_of_ne_local entries.reverse candidate value
              (Ne.symm hname)).symm

end Flapjack
