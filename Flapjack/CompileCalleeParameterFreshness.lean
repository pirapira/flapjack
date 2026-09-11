import Flapjack.CompileCalleeParameterList

/-!
Structural freshness of compiler-generated callee parameter slots.

`compileParamVars` allocates each parameter range immediately after the
previous range.  The resulting lower-bound and pairwise-disjointness facts
are independent of the source values and can therefore be reused by the
callee-entry correctness theorem.
-/

namespace Flapjack

theorem nodup_append_cons_not_mem
    {β : Type u} (previous tail : List β) (value : β)
    (h : (previous ++ value :: tail).Nodup) : value ∉ previous := by
  induction previous with
  | nil => simp
  | cons head previous ih =>
      have h' := List.nodup_cons.mp h
      intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst value
        exact h'.1 (by simp)
      · exact ih h'.2 hmem

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

theorem calleeParameterListFreshAppend_of_conditions_aux
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (previous remaining all : List (CalleeParameter α))
    (hcontext : context.vars = previous.map
      (fun parameter =>
        (parameter.name, (parameter.shape, parameter.slots))))
    (hdecomp : previous ++ remaining = all)
    (hnames : (previous.map CalleeParameter.name ++
      remaining.map CalleeParameter.name).Nodup)
    (hshape : ∀ parameter ∈ all,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hlength : ∀ parameter ∈ all,
      parameter.slots.length = parameter.values.length)
    (hdistinct : ∀ parameter ∈ all,
      CrepDistinctNames parameter.slots)
    (hflat : ∀ parameter ∈ all,
      panValueFlatWords parameter.value = parameter.values)
    (hseparate : ∀ left ∈ all, ∀ right ∈ all, left ≠ right →
      ∀ slot ∈ left.slots, slot ∉ right.slots) :
    CalleeParameterListFreshAppend structs context remaining := by
  induction remaining generalizing previous context with
  | nil => simp [CalleeParameterListFreshAppend]
  | cons parameter parameters ih =>
      have hnames' : (previous.map CalleeParameter.name ++ parameter.name ::
          parameters.map CalleeParameter.name).Nodup := by
        simpa [List.map_cons] using hnames
      have hnamePrefix : parameter.name ∉ previous.map CalleeParameter.name :=
        nodup_append_cons_not_mem (previous.map CalleeParameter.name)
          (parameters.map CalleeParameter.name) parameter.name hnames'
      have hmetadataName : parameter.name ∉
          (previous.map (fun oldParameter =>
            (oldParameter.name, (oldParameter.shape, oldParameter.slots)))).map
              Prod.fst := by
        simpa [List.map_map, Function.comp_def] using hnamePrefix
      have hname : lookupInfo parameter.name context.vars = none := by
        rw [hcontext]
        exact lookupInfo_none_of_name_not_mem parameter.name _ hmetadataName
      have hparameterAll : parameter ∈ all := by
        rw [← hdecomp]
        simp
      have hnoalias : ∀ oldName oldShape oldSlots,
          oldName ≠ parameter.name →
          lookupInfo oldName context.vars = some (oldShape, oldSlots) →
          ∀ slot ∈ parameter.slots, slot ∉ oldSlots := by
        intro oldName oldShape oldSlots hne hlookup slot hslot
        have hmetadataMem : (oldName, (oldShape, oldSlots)) ∈
            previous.map (fun oldParameter =>
              (oldParameter.name, (oldParameter.shape, oldParameter.slots))) := by
          have hlookupMem := lookupInfo_some_mem oldName context.vars
            (oldShape, oldSlots) hlookup
          simpa [hcontext] using hlookupMem
        obtain ⟨oldParameter, holdPrefix, hmetadata⟩ :=
          List.mem_map.mp hmetadataMem
        have holdName : oldParameter.name = oldName :=
          congrArg (fun entry => entry.1) hmetadata
        have holdSlots : oldParameter.slots = oldSlots :=
          congrArg (fun entry => entry.2.2) hmetadata
        have holdAll : oldParameter ∈ all := by
          rw [← hdecomp]
          simp [holdPrefix]
        have hneParameter : parameter ≠ oldParameter := by
          intro heq
          apply hne
          calc
            oldName = oldParameter.name := holdName.symm
            _ = parameter.name := by simp [heq]
        have hseparated := hseparate parameter hparameterAll oldParameter
          holdAll hneParameter slot hslot
        intro holdSlot
        apply hseparated
        rw [holdSlots]
        exact holdSlot
      have hcontextTail :
          (addCalleeParameterContextAppend context parameter).vars =
          (previous ++ [parameter]).map (fun oldParameter =>
              (oldParameter.name, (oldParameter.shape, oldParameter.slots))) := by
        simp [addCalleeParameterContextAppend, hcontext, List.map_append]
      have hdecompTail : (previous ++ [parameter]) ++ parameters = all := by
        simpa [List.append_assoc] using hdecomp
      have hnamesTail :
          ((previous ++ [parameter]).map CalleeParameter.name ++
            parameters.map CalleeParameter.name).Nodup := by
        simpa [List.map_append, List.map_cons, List.append_assoc] using hnames
      refine ⟨hname, hshape parameter hparameterAll,
        hlength parameter hparameterAll, hdistinct parameter hparameterAll,
        hflat parameter hparameterAll, hnoalias, ?_⟩
      exact ih (previous := previous ++ [parameter])
        (context := addCalleeParameterContextAppend context parameter)
        hcontextTail hdecompTail hnamesTail

theorem calleeParameterListFreshAppend_of_conditions
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (parameters : List (CalleeParameter α))
    (hcontext : context.vars = [])
    (hnames : (parameters.map CalleeParameter.name).Nodup)
    (hshape : ∀ parameter ∈ parameters,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hlength : ∀ parameter ∈ parameters,
      parameter.slots.length = parameter.values.length)
    (hdistinct : ∀ parameter ∈ parameters,
      CrepDistinctNames parameter.slots)
    (hflat : ∀ parameter ∈ parameters,
      panValueFlatWords parameter.value = parameter.values)
    (hseparate : ∀ left ∈ parameters, ∀ right ∈ parameters, left ≠ right →
      ∀ slot ∈ left.slots, slot ∉ right.slots) :
    CalleeParameterListFreshAppend structs context parameters := by
  apply calleeParameterListFreshAppend_of_conditions_aux structs context [] parameters
    parameters
  · simp [hcontext]
  · simp
  · exact hnames
  · exact hshape
  · exact hlength
  · exact hdistinct
  · exact hflat
  · exact hseparate

theorem pairwise_symmetric_relation_of_mem
    {β : Type u} (relation : β → β → Prop) (entries : List β)
    (hpairwise : List.Pairwise
      (fun left right => relation left right ∧ relation right left) entries) :
    ∀ left ∈ entries, ∀ right ∈ entries, left ≠ right →
      relation left right := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      simp only [List.pairwise_cons] at hpairwise
      intro left hleft right hright hne
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · exact False.elim (hne rfl)
        · exact (hpairwise.1 right hright).1
      · rcases hright with rfl | hright
        · exact (hpairwise.1 left hleft).2
        · exact ih hpairwise.2 left hleft right hright hne

theorem compileCalleeParameterList_names
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    (compileCalleeParameterList params values offset).map
        CalleeParameter.name = params.map Prod.fst := by
  have hmetadata := compileCalleeParameterList_metadata params values offset hlength
  have hnamesMetadata := congrArg (List.map Prod.fst) hmetadata
  have hnamesParams := compileParamVars_preserves_parameter_shapes params offset
  have hnamesCompiled :
      (compileParamVars params offset).1.map Prod.fst = params.map Prod.fst := by
    simpa [Function.comp_def] using congrArg (List.map Prod.fst) hnamesParams
  calc
    (compileCalleeParameterList params values offset).map CalleeParameter.name =
        ((compileCalleeParameterList params values offset).map (fun parameter =>
          (parameter.name, (parameter.shape, parameter.slots)))).map Prod.fst := by
            simp [List.map_map, Function.comp_def]
    _ = (compileParamVars params offset).1.map Prod.fst := hnamesMetadata
    _ = params.map Prod.fst := hnamesCompiled

theorem compileCalleeParameterList_flattening_of_mem
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (parameter : CalleeParameter α)
    (hparameter : parameter ∈ compileCalleeParameterList params values offset) :
    panValueFlatWords parameter.value = parameter.values := by
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList] at hparameter
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              simp only [compileCalleeParameterList, List.mem_cons] at hparameter
              rcases hparameter with rfl | hparameter
              · rfl
              · exact ih values (offset + Shape.shapeSize shape) htail hparameter

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

theorem compileCalleeParameterList_separate
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    ∀ left ∈ compileCalleeParameterList params values offset,
      ∀ right ∈ compileCalleeParameterList params values offset, left ≠ right →
        ∀ slot ∈ left.slots, slot ∉ right.slots := by
  have hpairwise := compileCalleeParameterList_slots_pairwise_disjoint
    params values offset hlength
  intro left hleft right hright hne
  exact (pairwise_symmetric_relation_of_mem
    (fun left right : CalleeParameter α =>
      ∀ slot ∈ left.slots, slot ∉ right.slots)
    (compileCalleeParameterList params values offset) hpairwise
    left hleft right hright hne)

theorem compileCalleeParameterList_fresh_append
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length)
    (hcontext : context.vars = [])
    (hnames : (params.map Prod.fst).Nodup)
    (hshape : ∀ parameter ∈ compileCalleeParameterList params values offset,
      panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ parameter ∈ compileCalleeParameterList params values offset,
      parameter.slots.length = parameter.values.length) :
    CalleeParameterListFreshAppend structs context
      (compileCalleeParameterList params values offset) := by
  apply calleeParameterListFreshAppend_of_conditions structs context
    (compileCalleeParameterList params values offset)
  · exact hcontext
  · rw [compileCalleeParameterList_names params values offset hlength]
    exact hnames
  · exact hshape
  · exact hparameterLength
  · exact compileCalleeParameterList_distinct_slots params values offset hlength
  · exact fun parameter hparameter =>
      compileCalleeParameterList_flattening_of_mem params values offset hlength
        parameter hparameter
  · exact compileCalleeParameterList_separate params values offset hlength

end Flapjack
