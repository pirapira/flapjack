import Flapjack.CompileCalleeParameterList

/-!
Structural freshness of compiler-generated callee parameter slots.

`compileParamVars` allocates each parameter range immediately after the
previous range.  The resulting lower-bound and pairwise-disjointness facts
are independent of the source values and can therefore be reused by the
callee-entry correctness theorem.
-/

namespace Flapjack

theorem lookupInfo_none_of_name_not_mem
    [LawfulBEq String]
    (name : String) (entries : InfoMap β)
    (hname : name ∉ entries.map Prod.fst) :
    lookupInfo name entries = none := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      simp only [List.map_cons, List.mem_cons] at hname
      by_cases hcandidate : candidate = name
      · exact False.elim (hname (Or.inl hcandidate.symm))
      · simp [lookupInfo, hcandidate]
        exact ih (fun hmem => hname (Or.inr hmem))

theorem lookupInfo_some_mem
    [LawfulBEq String]
    (name : String) (entries : InfoMap β) (value : β)
    (hlookup : lookupInfo name entries = some value) :
    (name, value) ∈ entries := by
  induction entries with
  | nil => simp [lookupInfo] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨candidate, candidateValue⟩
      by_cases hcandidate : candidate = name
      · subst candidate
        simp [lookupInfo] at hlookup
        cases hlookup
        simp
      · simp [lookupInfo, hcandidate] at hlookup
        have hmem := ih hlookup
        simp [hmem]

theorem lookupInfo_compileParamVars_none_of_name_not_mem
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat) (name : String)
    (hname : name ∉ params.map Prod.fst) :
    lookupInfo name (compileParamVars params offset).1 = none := by
  apply lookupInfo_none_of_name_not_mem
  intro hmem
  apply hname
  have hshapes := compileParamVars_preserves_parameter_shapes params offset
  have hnames :
      (compileParamVars params offset).1.map Prod.fst = params.map Prod.fst := by
    simpa [Function.comp_def] using congrArg (List.map Prod.fst) hshapes
  have hmem' : name ∈
      (compileParamVars params offset).1.map Prod.fst := by
    exact hmem
  rw [hnames] at hmem'
  exact hmem'

theorem lookupInfo_compileCalleeParameterList_none_of_name_not_mem
    [LawfulBEq String]
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (name : String) (hname : name ∉ params.map Prod.fst) :
    lookupInfo name
        ((compileCalleeParameterList params values offset).map
          (fun parameter =>
            (parameter.name, (parameter.shape, parameter.slots)))) = none := by
  rw [compileCalleeParameterList_metadata params values offset hlength]
  exact lookupInfo_compileParamVars_none_of_name_not_mem params offset name hname

theorem compileCalleeParameterList_slots_ge
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    ∀ parameter ∈ compileCalleeParameterList params values offset,
      ∀ slot ∈ parameter.slots, offset ≤ slot := by
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList]
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              intro parameter hparameter slot hslot
              simp only [compileCalleeParameterList, List.mem_cons] at hparameter
              rcases hparameter with rfl | hparameter
              · rcases List.mem_map.mp hslot with ⟨index, hindex, rfl⟩
                exact Nat.le_add_right offset index
              · have htailSlot := ih values
                  (offset + Shape.shapeSize shape) htail parameter hparameter
                  slot hslot
                exact Nat.le_trans
                  (by omega : offset ≤ offset + Shape.shapeSize shape)
                  htailSlot

theorem compileCalleeParameterList_slots_pairwise_disjoint
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    List.Pairwise
      (fun left right : CalleeParameter α =>
        (∀ slot ∈ left.slots, slot ∉ right.slots) ∧
        (∀ slot ∈ right.slots, slot ∉ left.slots))
      (compileCalleeParameterList params values offset) := by
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList]
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              simp only [compileCalleeParameterList, List.pairwise_cons]
              constructor
              · intro right hright
                constructor
                · intro slot hslot hrightSlot
                  rcases List.mem_map.mp hslot with ⟨index, hindex, rfl⟩
                  have hleftLt : offset + index <
                      offset + Shape.shapeSize shape := by
                    exact Nat.add_lt_add_left (List.mem_range.mp hindex) offset
                  have hrightGe := compileCalleeParameterList_slots_ge params values
                    (offset + Shape.shapeSize shape) htail right hright
                      (offset + index) hrightSlot
                  omega
                · intro rightSlot hrightSlot hslot
                  rcases List.mem_map.mp hslot with ⟨index, hindex, rfl⟩
                  have hleftLt : offset + index <
                      offset + Shape.shapeSize shape := by
                    exact Nat.add_lt_add_left (List.mem_range.mp hindex) offset
                  have hrightGe := compileCalleeParameterList_slots_ge params values
                    (offset + Shape.shapeSize shape) htail right hright
                      (offset + index) hrightSlot
                  omega
              · exact ih values (offset + Shape.shapeSize shape) htail

theorem compileCalleeParameterList_distinct_slots
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    ∀ parameter ∈ compileCalleeParameterList params values offset,
      CrepDistinctNames parameter.slots := by
  have hdistinctRange : ∀ (start count : Nat),
      CrepDistinctNames ((List.range count).map (fun index => start + index)) := by
    have happend : ∀ (entries : List Nat) (value : Nat),
        CrepDistinctNames entries → value ∉ entries →
        CrepDistinctNames (entries ++ [value]) := by
      intro entries value
      induction entries generalizing value with
      | nil =>
          intro _ _
          simp [CrepDistinctNames]
      | cons head tail ih =>
          intro hdistinct hnot
          rcases hdistinct with ⟨hhead, htail⟩
          have hheadValue : head ≠ value := by
            intro heq
            apply hnot
            simp [heq]
          have htailNot : value ∉ tail := by
            intro hmem
            apply hnot
            simp [hmem]
          have hheadNot : head ∉ tail ++ [value] := by
            intro hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hmem | heq
            · exact hhead hmem
            · exact hheadValue heq
          exact ⟨hheadNot, ih value htail htailNot⟩
    intro start count
    induction count with
    | zero => simp [CrepDistinctNames]
    | succ count ih =>
        have hnot : start + count ∉
            (List.range count).map (fun index => start + index) := by
          intro hmem
          obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hmem
          have hindexLt : index < count := List.mem_range.mp hindex
          omega
        simpa [List.range_succ, List.map_append] using
          happend ((List.range count).map (fun index => start + index))
            (start + count) ih hnot
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList]
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              intro parameter hparameter
              simp only [compileCalleeParameterList, List.mem_cons] at hparameter
              rcases hparameter with rfl | hparameter
              · exact hdistinctRange offset (Shape.shapeSize shape)
              · exact ih values (offset + Shape.shapeSize shape) htail
                  parameter hparameter

end Flapjack
