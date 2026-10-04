import Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCodeLabels

/-! The `stack_good_handler_labels` chain of `stack_to_labProofScript.sml:4537-4731`:
every stack-to-lab pass preserves `stack_good_handler_labels`, so every
nonzero-entry label the compiled Lab program refers to is one of its own code
labels. HOL sets are Lean `Set`s and `SND x` is `x.2`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.GoodHandlerLabels
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.LabelSets
open Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCodeLabels

/-- HOL `nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels" (words_as_type_indexed_bitvec)]
theorem nonzeroGetLabelsMapProgToSectionSubsetCodeLabels {width : Nat} [NeZero width] :
    ∀ p : List (Nat × HolProg width),
      (∀ sec ∈ p.map progToSectionHOL, LabProps.secLabelsOk sec) ∧ stackGoodHandlerLabels p →
      restrictNonzero (LabProps.LabelSets.getLabels (p.map progToSectionHOL)) ⊆
        LabProps.LabelSets.getCodeLabels (p.map progToSectionHOL) := by
  rintro p ⟨hok, hgood⟩ lab ⟨hlab, hnz⟩
  rcases getLabelsMapProgToSectionSubsetCodeLabelsLemma p hok hlab with h | h
  · exact h
  · rcases hgood ⟨h, hnz⟩ with h | h
    · exact mapProgToSectionPreservesHandlerLabels p h
    · exact oneProgSection h

section Infrastructure
variable {width : Nat} [NeZero width]

/-- The right-hand side of `stack_good_handler_labels_def` (Flapjack
abbreviation). -/
def handlerRhs (prog : List (Nat × HolProg width)) : Set (Nat × Nat) :=
  ⋃₀ {labels | labels ∈ prog.map (fun (name, body) => stackGetHandlerLabels name body)} ∪
    (fun name => (name, 1)) '' {name | name ∈ prog.map Prod.fst}

theorem mem_handlerRhs {prog : List (Nat × HolProg width)} {a b : Nat} :
    (a, b) ∈ handlerRhs prog ↔
      (∃ np ∈ prog, (a, b) ∈ stackGetHandlerLabels np.1 np.2) ∨
        (a ∈ prog.map Prod.fst ∧ b = 1) := by
  simp only [handlerRhs, Set.mem_union, Set.mem_sUnion, Set.mem_ofPred_eq, List.mem_map,
    Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨_, ⟨⟨n, p⟩, hm, rfl⟩, h⟩ | ⟨x, hx, rfl, rfl⟩)
    · exact .inl ⟨(n, p), hm, h⟩
    · exact .inr ⟨hx, rfl⟩
  · rintro (⟨⟨n, p⟩, hm, h⟩ | ⟨hx, rfl⟩)
    · exact .inl ⟨_, ⟨(n, p), hm, rfl⟩, h⟩
    · exact .inr ⟨a, hx, rfl, rfl⟩

theorem goodHandler_iff {prog : List (Nat × HolProg width)} :
    stackGoodHandlerLabels prog ↔
      ∀ np ∈ prog, ∀ a b, (a, b) ∈ getCodeLabels np.2 → b ≠ 0 → (a, b) ∈ handlerRhs prog := by
  constructor
  · intro h np hnp a b hab hb
    exact h ⟨⟨_, ⟨np.2, List.mem_map_of_mem hnp, rfl⟩, hab⟩, hb⟩
  · rintro h ⟨a, b⟩ ⟨⟨_, ⟨body, hb, rfl⟩, hx⟩, hnz⟩
    obtain ⟨np, hnp, rfl⟩ := List.mem_map.mp hb
    exact h np hnp a b hx hnz

theorem handlerRhs_append_right {pre prog : List (Nat × HolProg width)} :
    handlerRhs prog ⊆ handlerRhs (pre ++ prog) := by
  rintro ⟨a, b⟩ h
  rw [mem_handlerRhs] at h ⊢
  rcases h with ⟨np, hm, h⟩ | h
  · exact .inl ⟨np, List.mem_append_right _ hm, h⟩
  · simp_all

theorem handlerRhs_append_left {pre prog : List (Nat × HolProg width)} :
    handlerRhs pre ⊆ handlerRhs (pre ++ prog) := by
  rintro ⟨a, b⟩ h
  rw [mem_handlerRhs] at h ⊢
  rcases h with ⟨np, hm, h⟩ | h
  · exact .inl ⟨np, List.mem_append_left _ hm, h⟩
  · simp_all

theorem handlerRhs_map {prog : List (Nat × HolProg width)}
    (g : Nat × HolProg width → HolProg width)
    (hh : ∀ np ∈ prog, stackGetHandlerLabels np.1 (g np) = stackGetHandlerLabels np.1 np.2) :
    handlerRhs (prog.map fun np => (np.1, g np)) = handlerRhs prog := by
  ext ⟨a, b⟩
  simp only [mem_handlerRhs, List.map_map, Function.comp_def, List.mem_map]
  constructor
  · rintro (⟨_, ⟨np, hm, rfl⟩, h⟩ | h)
    · exact .inl ⟨np, hm, by rw [← hh np hm]; exact h⟩
    · exact .inr h
  · rintro (⟨np, hm, h⟩ | h)
    · exact .inl ⟨_, ⟨np, hm, rfl⟩, by rw [hh np hm]; exact h⟩
    · exact .inr h

/-- Transport of `stack_good_handler_labels` through a name-preserving pass that
preserves handler labels and adds at most the zero-entry label `(e,0)`. -/
theorem goodHandler_map {prog : List (Nat × HolProg width)}
    (g : Nat × HolProg width → HolProg width) (e : Nat)
    (hh : ∀ np ∈ prog, stackGetHandlerLabels np.1 (g np) = stackGetHandlerLabels np.1 np.2)
    (hcode : ∀ np ∈ prog, getCodeLabels (g np) ⊆ insert (e, 0) (getCodeLabels np.2))
    (hg : stackGoodHandlerLabels prog) :
    stackGoodHandlerLabels (prog.map fun np => (np.1, g np)) := by
  rw [goodHandler_iff, handlerRhs_map g hh]
  intro np hnp a b hab hb
  obtain ⟨np0, hm, rfl⟩ := List.mem_map.mp hnp
  rcases hcode np0 hm hab with h | h
  · exact absurd (Prod.mk.inj h).2 hb
  · exact goodHandler_iff.mp hg np0 hm a b h hb

end Infrastructure

/-- HOL `stack_names_stack_good_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_stack_good_handler_labels" (words_as_type_indexed_bitvec)]
theorem stackNamesStackGoodHandlerLabels {width : Nat} [NeZero width] :
    ∀ (prog : List (Nat × HolProg width)) (f : Spt Nat),
      stackGoodHandlerLabels prog → stackGoodHandlerLabels (StackNames.compileHOL f prog) := by
  intro prog f h
  rw [compileHOL_eq_map]
  exact goodHandler_map _ 0 (fun np _ => stackNamesStackGetHandlerLabelsComp f np.2 np.1)
    (fun np _ => by rw [stackNamesGetCodeLabelsComp]; exact Set.subset_insert _ _) h

/-- HOL `restrict_nonzero_union`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "restrict_nonzero_union"]
theorem restrictNonzeroUnion {A B : Set (Nat × Nat)} :
    restrictNonzero (A ∪ B) = restrictNonzero A ∪ restrictNonzero B := by
  ext x
  simp only [restrictNonzero, Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- HOL `restrict_nonzero_IN`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "restrict_nonzero_IN"]
theorem restrictNonzeroIn {x : Nat × Nat} {s : Set (Nat × Nat)} :
    x ∈ restrictNonzero s ↔ x ∈ s ∧ x.2 ≠ 0 :=
  Iff.rfl

/-- HOL `stack_good_handler_labels_append`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_good_handler_labels_append" (words_as_type_indexed_bitvec)]
theorem stackGoodHandlerLabelsAppend {width : Nat} [NeZero width]
    {xs ys : List (Nat × HolProg width)} :
    stackGoodHandlerLabels xs ∧ stackGoodHandlerLabels ys →
      stackGoodHandlerLabels (xs ++ ys) := by
  rintro ⟨hx, hy⟩
  rw [goodHandler_iff] at hx hy ⊢
  intro np hnp a b hab hb
  rcases List.mem_append.mp hnp with hm | hm
  · exact handlerRhs_append_left (hx np hm a b hab hb)
  · exact handlerRhs_append_right (hy np hm a b hab hb)

/-- HOL `stack_remove_stack_good_handler_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_stack_good_handler_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackGoodHandlerLabelsIncr {width : Nat} [NeZero width] {jump : Bool}
    {offset : BitVec width × BitVec width} {sp : Nat} :
    ∀ prog : List (Nat × HolProg width),
      stackGoodHandlerLabels prog →
        stackGoodHandlerLabels (prog.map (StackRemove.progComp jump offset sp)) := by
  intro prog h
  exact goodHandler_map (fun np => StackRemove.comp jump offset sp np.2) StackRemove.stackErrLab
    (fun np _ => stackRemoveStackGetHandlerLabelsComp jump offset sp np.2 np.1)
    (fun np _ => stackRemoveGetCodeLabelsComp jump offset sp np.2) h

/-- HOL `stack_remove_stack_good_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_stack_good_handler_labels" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackGoodHandlerLabels {width : Nat} [NeZero width] {jump : Bool}
    {off : BitVec width × BitVec width} {ggc : Bool} {mh sp loc : Nat} :
    ∀ prog : List (Nat × HolProg width),
      stackGoodHandlerLabels prog →
        stackGoodHandlerLabels (StackRemove.compileHOL jump off ggc mh sp loc prog) := by
  intro prog h
  refine stackGoodHandlerLabelsAppend ⟨?_, stackRemoveStackGoodHandlerLabelsIncr prog h⟩
  rw [goodHandler_iff]
  intro np hnp a b hab hb
  have := initStubsLabels np.2 (List.mem_map_of_mem hnp) hab
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
    Prod.mk.injEq] at this
  omega

/-- HOL `stack_alloc_stack_good_handler_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_stack_good_handler_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackAllocStackGoodHandlerLabelsIncr {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width),
      stackGoodHandlerLabels prog → stackGoodHandlerLabels (prog.map StackAlloc.progComp) := by
  intro prog h
  rw [progComp_eq_map]
  exact goodHandler_map _ gcStubLocation
    (fun np _ => stackAllocStackGetHandlerLabelsComp _ _ np.2)
    (fun np _ => stackAllocGetCodeLabelsComp _ _ np.2) h

/-- HOL `stack_alloc_stack_good_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_stack_good_handler_labels" (words_as_type_indexed_bitvec)]
theorem stackAllocStackGoodHandlerLabels {width : Nat} [NeZero width] :
    ∀ (prog : List (Nat × HolProg width)) (c : DataToWord.Config),
      stackGoodHandlerLabels prog → stackGoodHandlerLabels (StackAlloc.compile c prog) := by
  intro prog c h
  refine stackGoodHandlerLabelsAppend ⟨?_, stackAllocStackGoodHandlerLabelsIncr prog h⟩
  rw [goodHandler_iff]
  intro np hnp a b hab _
  simp only [StackAlloc.stubs, List.mem_cons, List.not_mem_nil, or_false] at hnp
  subst hnp
  simp [getCodeLabels, stackAllocInitCodeLabels] at hab

/-- HOL `stack_rawcall_stack_good_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_stack_good_handler_labels" (words_as_type_indexed_bitvec)]
theorem stackRawcallStackGoodHandlerLabels {width : Nat} [NeZero width]
    {prog : List (Nat × HolProg width)} :
    stackGoodHandlerLabels prog → stackGoodHandlerLabels (StackRawCall.compile prog) := by
  intro h
  have heq : StackRawCall.compile prog = prog.map fun np =>
      (np.1, StackRawCall.compTop (StackRawCall.collectInfo prog .ln) np.2) := rfl
  rw [heq, goodHandler_iff,
    handlerRhs_map _ (fun np _ => (StackRawCall.stackGetHandlerLabelsComp _ np.2 np.1).2)]
  intro np hnp a b hab hb
  obtain ⟨np0, hm, rfl⟩ := List.mem_map.mp hnp
  obtain ⟨k, hk, hne⟩ := inGetCodeLabelsCompTop hab
  by_cases hbk : b = k
  · subst hbk
    exact goodHandler_iff.mp h np0 hm a b hk hb
  · obtain ⟨rfl, -, ha⟩ := hne hbk
    rw [mem_handlerRhs]
    exact .inr ⟨ha, rfl⟩

/-- HOL `stack_to_lab_stack_good_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_stack_good_handler_labels" (words_as_type_indexed_bitvec)]
theorem stackToLabStackGoodHandlerLabels {width : Nat} [NeZero width]
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {prog : List (Nat × HolProg width)}
    {prog' : LabSem.LabProgHOL width} :
    StackToLab.compile stackConf dataConf maxHeap sp offset prog = prog' ∧
      stackGoodHandlerLabels prog ∧ (∀ sec ∈ prog', LabProps.secLabelsOk sec) →
      restrictNonzero (LabProps.LabelSets.getLabels prog') ⊆
        LabProps.LabelSets.getCodeLabels prog' := by
  rintro ⟨rfl, h, hok⟩
  refine nonzeroGetLabelsMapProgToSectionSubsetCodeLabels _ ⟨hok, ?_⟩
  exact stackNamesStackGoodHandlerLabels _ _ (stackRemoveStackGoodHandlerLabels _
    (stackAllocStackGoodHandlerLabels _ _ (stackRawcallStackGoodHandlerLabels h)))

/-- HOL `stack_to_lab_stack_good_handler_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_stack_good_handler_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackToLabStackGoodHandlerLabelsIncr {width : Nat} [NeZero width] {f : Spt Nat}
    {jump : Bool} {offset : BitVec width × BitVec width} {sp : Nat}
    {prog : List (Nat × HolProg width)} {prog' : LabSem.LabProgHOL width} :
    StackToLab.compileNoStubs f jump offset sp prog = prog' ∧
      stackGoodHandlerLabels prog ∧ (∀ sec ∈ prog', LabProps.secLabelsOk sec) →
      restrictNonzero (LabProps.LabelSets.getLabels prog') ⊆
        LabProps.LabelSets.getCodeLabels prog' := by
  rintro ⟨rfl, h, hok⟩
  refine nonzeroGetLabelsMapProgToSectionSubsetCodeLabels _ ⟨hok, ?_⟩
  exact stackNamesStackGoodHandlerLabels _ _ (stackRemoveStackGoodHandlerLabelsIncr _
    (stackAllocStackGoodHandlerLabelsIncr _ h))

end Flapjack.Compiler.Backend.StackToLab.Proofs.GoodHandlerLabels
