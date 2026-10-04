import Flapjack.Compiler.Backend.StackToLab.Proofs.LabelSets
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackRawCall.Proofs.HandlerLabels
import Flapjack.Compiler.Backend.StackRemove.Comp

/-! The `stack_good_code_labels` chain of `stack_to_labProofScript.sml:4090-4536`:
every stack-to-lab pass preserves `stack_good_code_labels`, so the labels the
compiled Lab program refers to are its own code labels or external entries.
HOL sets are Lean `Set`s, `set l` is list membership and `domain t` is
`sptMem`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCodeLabels
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.LabelSets

section Infrastructure
variable {width : Nat} [NeZero width]

/-- The right-hand side of `stack_good_code_labels_def` (Flapjack
abbreviation). -/
def goodRhs (prog : List (Nat × HolProg width)) (elabs : Set Nat) : Set (Nat × Nat) :=
  ⋃₀ {labels | labels ∈ prog.map (fun (name, body) => stackGetHandlerLabels name body)} ∪
    (fun name => (name, 0)) '' {name | name ∈ prog.map Prod.fst} ∪
    (fun name => (name, 0)) '' elabs ∪
    (fun name => (name, 1)) '' {name | name ∈ prog.map Prod.fst} ∪
    (fun name => (name, 1)) '' elabs

theorem mem_goodRhs {prog : List (Nat × HolProg width)} {elabs : Set Nat} {a b : Nat} :
    (a, b) ∈ goodRhs prog elabs ↔
      (∃ np ∈ prog, (a, b) ∈ stackGetHandlerLabels np.1 np.2) ∨
        (a ∈ prog.map Prod.fst ∧ b = 0) ∨ (a ∈ elabs ∧ b = 0) ∨
        (a ∈ prog.map Prod.fst ∧ b = 1) ∨ (a ∈ elabs ∧ b = 1) := by
  simp only [goodRhs, Set.mem_union, Set.mem_sUnion, Set.mem_ofPred_eq, List.mem_map,
    Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ((((⟨_, ⟨⟨n, p⟩, hm, rfl⟩, h⟩ | ⟨x, hx, rfl, rfl⟩) | ⟨x, hx, rfl, rfl⟩) |
      ⟨x, hx, rfl, rfl⟩) | ⟨x, hx, rfl, rfl⟩)
    · exact .inl ⟨(n, p), hm, h⟩
    · exact .inr (.inl ⟨hx, rfl⟩)
    · exact .inr (.inr (.inl ⟨hx, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨hx, rfl⟩)))
    · exact .inr (.inr (.inr (.inr ⟨hx, rfl⟩)))
  · rintro (⟨⟨n, p⟩, hm, h⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩)
    · exact .inl (.inl (.inl (.inl ⟨_, ⟨(n, p), hm, rfl⟩, h⟩)))
    · exact .inl (.inl (.inl (.inr ⟨a, hx, rfl, rfl⟩)))
    · exact .inl (.inl (.inr ⟨a, hx, rfl, rfl⟩))
    · exact .inl (.inr ⟨a, hx, rfl, rfl⟩)
    · exact .inr ⟨a, hx, rfl, rfl⟩

theorem good_iff {prog : List (Nat × HolProg width)} {elabs : Set Nat} :
    stackGoodCodeLabels prog elabs ↔ ∀ np ∈ prog, getCodeLabels np.2 ⊆ goodRhs prog elabs := by
  constructor
  · intro h np hnp x hx
    exact h ⟨_, ⟨np.2, List.mem_map_of_mem hnp, rfl⟩, hx⟩
  · rintro h x ⟨_, ⟨body, hb, rfl⟩, hx⟩
    obtain ⟨np, hnp, rfl⟩ := List.mem_map.mp hb
    exact h np hnp hx

theorem goodRhs_append_right {pre prog : List (Nat × HolProg width)} {elabs : Set Nat} :
    goodRhs prog elabs ⊆ goodRhs (pre ++ prog) elabs := by
  rintro ⟨a, b⟩ h
  rw [mem_goodRhs] at h ⊢
  rcases h with ⟨np, hm, h⟩ | h | h | h | h
  · exact .inl ⟨np, List.mem_append_right _ hm, h⟩
  all_goals simp_all

theorem goodRhs_append_left {pre prog : List (Nat × HolProg width)} {elabs : Set Nat} :
    goodRhs pre elabs ⊆ goodRhs (pre ++ prog) elabs := by
  rintro ⟨a, b⟩ h
  rw [mem_goodRhs] at h ⊢
  rcases h with ⟨np, hm, h⟩ | h | h | h | h
  · exact .inl ⟨np, List.mem_append_left _ hm, h⟩
  all_goals simp_all

theorem goodRhs_map {prog : List (Nat × HolProg width)} {elabs : Set Nat}
    (g : Nat × HolProg width → HolProg width)
    (hh : ∀ np ∈ prog, stackGetHandlerLabels np.1 (g np) = stackGetHandlerLabels np.1 np.2) :
    goodRhs (prog.map fun np => (np.1, g np)) elabs = goodRhs prog elabs := by
  ext ⟨a, b⟩
  simp only [mem_goodRhs, List.map_map, Function.comp_def, List.mem_map]
  constructor
  · rintro (⟨_, ⟨np, hm, rfl⟩, h⟩ | h)
    · exact .inl ⟨np, hm, by rw [← hh np hm]; exact h⟩
    · exact .inr h
  · rintro (⟨np, hm, h⟩ | h)
    · exact .inl ⟨_, ⟨np, hm, rfl⟩, by rw [hh np hm]; exact h⟩
    · exact .inr h

/-- Pointwise transport of `stack_good_code_labels` through a name-preserving
pass that preserves handler labels and adds at most the labels `extra`. -/
theorem codeLabels_map_sub {pre prog : List (Nat × HolProg width)} {elabs : Set Nat}
    (g : Nat × HolProg width → HolProg width) (extra : Set (Nat × Nat))
    (hh : ∀ np ∈ prog, stackGetHandlerLabels np.1 (g np) = stackGetHandlerLabels np.1 np.2)
    (hcode : ∀ np ∈ prog, getCodeLabels (g np) ⊆ extra ∪ getCodeLabels np.2)
    (hextra : extra ⊆ goodRhs (pre ++ prog.map fun np => (np.1, g np)) elabs)
    (hg : stackGoodCodeLabels prog elabs) :
    ∀ np ∈ prog.map (fun np => (np.1, g np)), getCodeLabels np.2 ⊆
      goodRhs (pre ++ prog.map fun np => (np.1, g np)) elabs := by
  intro np hnp x hx
  obtain ⟨np0, hm, rfl⟩ := List.mem_map.mp hnp
  rcases hcode np0 hm hx with h | h
  · exact hextra h
  · exact goodRhs_append_right (by rw [goodRhs_map g hh]; exact good_iff.mp hg np0 hm h)

end Infrastructure

/-! ### stack_names -/

/-- HOL `get_code_labels_comp` (stack_names version, line 4090). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_code_labels_comp" 4090
  (words_as_type_indexed_bitvec)]
theorem complexGetCodeLabelsStackNamesComp {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width),
      complexGetCodeLabels (StackNames.progCompHOL f p) = complexGetCodeLabels p := by
  intro f p
  induction p using StackNames.progCompHOL.induct <;>
    (try simp_all [StackNames.progCompHOL, complexGetCodeLabels])
  case case11 rh target handler _ _ =>
    rcases rh with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      rcases target with t | t <;>
      simp_all [StackNames.progCompHOL, complexGetCodeLabels, StackNames.destFindNameHOL]

/-- HOL `stack_names_get_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_get_code_labels"
  (words_as_type_indexed_bitvec)]
theorem stackNamesGetCodeLabels {width : Nat} [NeZero width] {f : Spt Nat}
    {prog : List (Nat × HolProg width)} :
    List.Forall₂ (fun cp p => complexGetCodeLabels cp = complexGetCodeLabels p)
      ((StackNames.compileHOL f prog).map Prod.snd) (prog.map Prod.snd) := by
  simp only [StackNames.compileHOL, List.map_map]
  induction prog with
  | nil => exact .nil
  | cons np rest ih => exact .cons (complexGetCodeLabelsStackNamesComp f np.2) ih

section StackRemoveHelpers
variable {width : Nat} [NeZero width]

theorem getCodeLabels_stackAlloc (jump : Bool) (pointer : Nat) :
    ∀ count, getCodeLabels (StackRemove.stackAlloc (width := width) jump pointer count) ⊆
      {(StackRemove.stackErrLab, 0)} := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.stackAlloc]
    split
    · simp [getCodeLabels]
    split
    · unfold StackRemove.singleStackAlloc; split <;> simp [getCodeLabels, StackRemove.haltInst]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [getCodeLabels]
      refine Set.union_subset ?_ this
      unfold StackRemove.singleStackAlloc; split <;> simp [getCodeLabels, StackRemove.haltInst]

theorem getCodeLabels_stackFree (pointer : Nat) :
    ∀ count, getCodeLabels (StackRemove.stackFree (width := width) pointer count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.stackFree]
    split
    · simp [getCodeLabels]
    split
    · simp [StackRemove.singleStackFree, getCodeLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp_all [StackRemove.singleStackFree, getCodeLabels]

theorem getCodeLabels_upshift (register : Nat) :
    ∀ count, getCodeLabels (StackRemove.upshift (width := width) register count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.upshift]
    split
    · simp [getCodeLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp_all [getCodeLabels]

theorem getCodeLabels_downshift (register : Nat) :
    ∀ count, getCodeLabels (StackRemove.downshift (width := width) register count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.downshift]
    split
    · simp [getCodeLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp_all [getCodeLabels]

theorem handlerLabels_stackAlloc (jump : Bool) (pointer : Nat) (owner : Nat) :
    ∀ count, stackGetHandlerLabels owner (StackRemove.stackAlloc (width := width) jump pointer count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.stackAlloc]
    split
    · simp [stackGetHandlerLabels]
    split
    · unfold StackRemove.singleStackAlloc; split <;> simp [stackGetHandlerLabels, StackRemove.haltInst]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      unfold StackRemove.singleStackAlloc; split <;>
        simp [stackGetHandlerLabels, StackRemove.haltInst, this]

theorem handlerLabels_stackFree (pointer owner : Nat) :
    ∀ count, stackGetHandlerLabels owner (StackRemove.stackFree (width := width) pointer count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.stackFree]
    split
    · simp [stackGetHandlerLabels]
    split
    · simp [StackRemove.singleStackFree, stackGetHandlerLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp [StackRemove.singleStackFree, stackGetHandlerLabels, this]

theorem handlerLabels_upshift (register owner : Nat) :
    ∀ count, stackGetHandlerLabels owner (StackRemove.upshift (width := width) register count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.upshift]
    split
    · simp [stackGetHandlerLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp [stackGetHandlerLabels, this]

theorem handlerLabels_downshift (register owner : Nat) :
    ∀ count, stackGetHandlerLabels owner (StackRemove.downshift (width := width) register count) = ∅ := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [StackRemove.downshift]
    split
    · simp [stackGetHandlerLabels]
    · have := ih (count - StackRemove.maxStackAlloc)
        (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp [stackGetHandlerLabels, this]

end StackRemoveHelpers

/-- HOL `get_code_labels_comp` (stack_remove version, line 4110). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "get_code_labels_comp" 4110
  (words_as_type_indexed_bitvec)]
theorem getCodeLabelsStackRemoveComp {width : Nat} [NeZero width] :
    ∀ (a : Bool) (b : BitVec width × BitVec width) (c : Nat) (p : HolProg width),
      getCodeLabels (StackRemove.comp a b c p) ⊆
        insert (StackRemove.stackErrLab, 0) (getCodeLabels p) := by
  intro a b c p
  induction p using StackRemove.comp.induct (bounds := b) <;>
    (try simp only [StackRemove.comp]) <;>
    (try split) <;>
    (try simp_all [getCodeLabels, getCodeLabels_stackFree, getCodeLabels_upshift,
      getCodeLabels_downshift, StackRemove.stackStore, StackRemove.stackLoad, moveInst,
      moveHOL, addInst, subInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.loadInst, StackRemove.storeInst, addBytesInWordInst, listSeqHOL,
      StackRemove.copyLoop, StackRemove.copyEach, whileHOL])
  case case7 count =>
    intro x y h
    simpa using getCodeLabels_stackAlloc a c count h
  case case19 ih2 ih1 =>
    exact ⟨ih2.trans (Set.insert_subset_insert Set.subset_union_left),
      ih1.trans (Set.insert_subset_insert Set.subset_union_right)⟩
  case case20 ih2 ih1 =>
    exact ⟨ih2.trans (Set.insert_subset_insert Set.subset_union_left),
      ih1.trans (Set.insert_subset_insert Set.subset_union_right)⟩
  case case22 ret target handler ih2 ih1 =>
    rcases ret with _ | ⟨bd, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      rcases target with t | t <;>
      simp only [Set.subset_def, Set.mem_insert_iff] at ih1 ih2 <;>
      simp only [StackRemove.comp, getCodeLabels, Set.subset_def, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false] <;>
      intro x hx <;> (try have := ih1 x) <;> (try have := ih2 x) <;> tauto

/-- The stack_remove initializer refers only to label `(1,0)` (HOL's `EVAL_TAC`
step of `stack_remove_init_code_labels`). -/
theorem mem_getCodeLabels_initCode {width : Nat} [NeZero width] {ggc : Bool} {mh sp : Nat}
    {x : Nat × Nat} :
    x ∈ getCodeLabels (StackRemove.initCode (width := width) ggc mh sp) → x = (1, 0) := by
  have hs : ∀ (a t : Nat) (ls : List (BitVec width ⊕ Nat)),
      getCodeLabels (StackRemove.storeListCode a t ls) = ∅ := by
    intro a t ls
    induction ls with
    | nil => simp [StackRemove.storeListCode, getCodeLabels]
    | cons x xs ih =>
      rcases x with v | r <;>
        simp [StackRemove.storeListCode, getCodeLabels, listSeqHOL, addBytesInWordInst, ih]
  simp [StackRemove.initCode, getCodeLabels, listSeqHOL, StackRemove.initMemory, hs, moveHOL,
    subInst, addInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst]

/-- HOL `init_stubs_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "init_stubs_labels"
  (words_as_type_indexed_bitvec)]
theorem initStubsLabels {width : Nat} [NeZero width] {ggc : Bool} {mh k start : Nat} :
    ∀ p ∈ (StackRemove.initStubs ggc mh k start : List (Nat × HolProg width)).map Prod.snd,
      getCodeLabels p ⊆ {x | x ∈ [(1, 0), (start, 0)]} := by
  intro p hp x hx
  simp only [StackRemove.initStubs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp only [getCodeLabels, Set.mem_union] at hx
    rcases hx with hx | hx
    · simp [mem_getCodeLabels_initCode hx]
    · simp_all
  all_goals simp [getCodeLabels, StackRemove.haltInst] at hx

/-- HOL `stack_names_get_code_labels_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_get_code_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackNamesGetCodeLabelsComp {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width),
      getCodeLabels (StackNames.progCompHOL f p) = getCodeLabels p := by
  intro f p
  induction p using StackNames.progCompHOL.induct <;>
    (try simp_all [StackNames.progCompHOL, getCodeLabels])
  case case11 rh target handler _ _ =>
    rcases rh with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      rcases target with t | t <;>
      simp_all [StackNames.progCompHOL, getCodeLabels, StackNames.destFindNameHOL]

/-- HOL `stack_names_stack_get_handler_labels_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_stack_get_handler_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackNamesStackGetHandlerLabelsComp {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width) (n : Nat),
      stackGetHandlerLabels n (StackNames.progCompHOL f p) = stackGetHandlerLabels n p := by
  intro f p n
  induction p using StackNames.progCompHOL.induct <;>
    (try simp_all [StackNames.progCompHOL, stackGetHandlerLabels])
  case case11 rh target handler _ _ =>
    rcases rh with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      rcases target with t | t <;>
      simp_all [StackNames.progCompHOL, stackGetHandlerLabels, StackNames.destFindNameHOL]

/-- HOL `UNCURRY_PAIR_ETA`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "UNCURRY_PAIR_ETA"]
theorem uncurryPairEta {α β γ : Type _} {f : α → β → γ} :
    Function.uncurry f = fun (p1, p2) => f p1 p2 := by
  funext ⟨a, b⟩; rfl

theorem compileHOL_eq_map {width : Nat} [NeZero width] (f : Spt Nat)
    (prog : List (Nat × HolProg width)) :
    StackNames.compileHOL f prog = prog.map fun np => (np.1, StackNames.progCompHOL f np.2) := rfl

/-- HOL `stack_names_stack_good_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_stack_good_code_labels" (words_as_type_indexed_bitvec)]
theorem stackNamesStackGoodCodeLabels {width : Nat} [NeZero width] {elabs : Set Nat} :
    ∀ (prog : List (Nat × HolProg width)) (f : Spt Nat),
      stackGoodCodeLabels prog elabs →
        stackGoodCodeLabels (StackNames.compileHOL f prog) elabs := by
  intro prog f h
  rw [compileHOL_eq_map, good_iff]
  have := codeLabels_map_sub (pre := []) (elabs := elabs) (fun np => StackNames.progCompHOL f np.2) ∅
    (fun np _ => stackNamesStackGetHandlerLabelsComp f np.2 np.1)
    (fun np _ => by rw [stackNamesGetCodeLabelsComp]; exact Set.subset_union_right)
    (Set.empty_subset _) h
  simpa using this

/-! ### stack_remove -/

/-- HOL `stack_remove_get_code_labels_comp` (the same statement as the line-4110
`get_code_labels_comp`). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_get_code_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackRemoveGetCodeLabelsComp {width : Nat} [NeZero width] :
    ∀ (a : Bool) (b : BitVec width × BitVec width) (c : Nat) (p : HolProg width),
      getCodeLabels (StackRemove.comp a b c p) ⊆
        insert (StackRemove.stackErrLab, 0) (getCodeLabels p) :=
  getCodeLabelsStackRemoveComp

/-- HOL `stack_remove_stack_get_handler_labels_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_stack_get_handler_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackGetHandlerLabelsComp {width : Nat} [NeZero width] :
    ∀ (a : Bool) (b : BitVec width × BitVec width) (c : Nat) (p : HolProg width) (m : Nat),
      stackGetHandlerLabels m (StackRemove.comp a b c p) = stackGetHandlerLabels m p := by
  intro a b c p m
  induction p using StackRemove.comp.induct (bounds := b) <;>
    (try simp only [StackRemove.comp]) <;>
    (try split) <;>
    (try simp_all [stackGetHandlerLabels, handlerLabels_stackAlloc, handlerLabels_stackFree,
      handlerLabels_upshift, handlerLabels_downshift, StackRemove.stackStore,
      StackRemove.stackLoad, moveInst, moveHOL, addInst, subInst, StackRemove.leftShiftInst,
      StackRemove.rightShiftInst, StackRemove.loadInst, StackRemove.storeInst,
      addBytesInWordInst, listSeqHOL, StackRemove.copyLoop, StackRemove.copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨bd, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [StackRemove.comp, stackGetHandlerLabels]

/-- HOL `stack_remove_init_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_init_code_labels" (words_as_type_indexed_bitvec)]
theorem stackRemoveInitCodeLabels {width : Nat} [NeZero width] {ggc : Bool} {mh sp : Nat}
    {x : Nat × Nat} :
    x ∈ getCodeLabels (StackRemove.initCode ggc mh sp : HolProg width) → x = (1, 0) := by
  exact mem_getCodeLabels_initCode

theorem compileHOL_eq {width : Nat} [NeZero width] (jump : Bool)
    (off : BitVec width × BitVec width) (ggc : Bool) (mh sp loc : Nat)
    (prog : List (Nat × HolProg width)) :
    StackRemove.compileHOL jump off ggc mh sp loc prog =
      StackRemove.initStubs ggc mh sp loc ++
        prog.map fun np => (np.1, StackRemove.comp jump off sp np.2) := rfl

/-- HOL `stack_remove_stack_good_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_stack_good_code_labels" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackGoodCodeLabels {width : Nat} [NeZero width] {elabs : Set Nat}
    {jump : Bool} {off : BitVec width × BitVec width} {ggc : Bool} {mh sp loc : Nat} :
    ∀ prog : List (Nat × HolProg width),
      loc ∈ prog.map Prod.fst ∧ stackGoodCodeLabels prog elabs →
        stackGoodCodeLabels (StackRemove.compileHOL jump off ggc mh sp loc prog) elabs := by
  rintro prog ⟨hloc, h⟩
  rw [compileHOL_eq, good_iff]
  intro np hnp
  rcases List.mem_append.mp hnp with hs | hm
  · intro x hx
    have hsub := initStubsLabels np.2 (List.mem_map_of_mem hs) hx
    obtain ⟨a, b⟩ := x
    rw [mem_goodRhs]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
      Prod.mk.injEq] at hsub
    rcases hsub with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨by simp [StackRemove.initStubs], rfl⟩)
    · refine .inr (.inl ⟨?_, rfl⟩)
      simp only [List.map_append, List.mem_append, List.map_map, Function.comp_def]
      exact .inr (by simpa using hloc)
  · exact codeLabels_map_sub (fun np => StackRemove.comp jump off sp np.2)
      {(StackRemove.stackErrLab, 0)}
      (fun np _ => stackRemoveStackGetHandlerLabelsComp jump off sp np.2 np.1)
      (fun np _ => by
        intro x hx
        rcases getCodeLabelsStackRemoveComp jump off sp np.2 hx with h | h
        · exact .inl h
        · exact .inr h)
      (by
        rintro x rfl
        rw [mem_goodRhs]
        exact .inr (.inl ⟨by simp [StackRemove.initStubs, StackRemove.stackErrLab], rfl⟩))
      h np hm

/-- HOL `stack_remove_stack_good_code_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_stack_good_code_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackGoodCodeLabelsIncr {width : Nat} [NeZero width] {elabs : Set Nat}
    {jump : Bool} {offset : BitVec width × BitVec width} {sp : Nat} :
    ∀ prog : List (Nat × HolProg width),
      StackRemove.stackErrLab ∈ elabs ∧ stackGoodCodeLabels prog elabs →
        stackGoodCodeLabels (prog.map (StackRemove.progComp jump offset sp)) elabs := by
  rintro prog ⟨herr, h⟩
  rw [show prog.map (StackRemove.progComp jump offset sp) =
    prog.map fun np => (np.1, StackRemove.comp jump offset sp np.2) from rfl, good_iff]
  have := codeLabels_map_sub (pre := []) (fun np => StackRemove.comp jump offset sp np.2)
      {(StackRemove.stackErrLab, 0)}
      (fun np _ => stackRemoveStackGetHandlerLabelsComp jump offset sp np.2 np.1)
      (fun np _ => by
        intro x hx
        rcases getCodeLabelsStackRemoveComp jump offset sp np.2 hx with h | h
        · exact .inl h
        · exact .inr h)
      (by
        rintro x rfl
        rw [mem_goodRhs]
        exact .inr (.inr (.inl ⟨herr, rfl⟩)))
      h
  simpa only [List.nil_append] using this

/-! ### stack_alloc -/

/-- HOL `stack_alloc_get_code_labels_comp`. HOL's binders `pp mm` do not occur
in the statement and are omitted. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_get_code_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackAllocGetCodeLabelsComp {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
      getCodeLabels (StackAlloc.comp n m p).1 ⊆ insert (gcStubLocation, 0) (getCodeLabels p)
  | n, m, .seq a b => by
      simp only [StackAlloc.comp, getCodeLabels]
      exact Set.union_subset
        ((stackAllocGetCodeLabelsComp n m a).trans (Set.insert_subset_insert Set.subset_union_left))
        ((stackAllocGetCodeLabelsComp n _ b).trans (Set.insert_subset_insert Set.subset_union_right))
  | n, m, .ite cmp r ri a b => by
      simp only [StackAlloc.comp, getCodeLabels]
      exact Set.union_subset
        ((stackAllocGetCodeLabelsComp n m a).trans (Set.insert_subset_insert Set.subset_union_left))
        ((stackAllocGetCodeLabelsComp n _ b).trans (Set.insert_subset_insert Set.subset_union_right))
  | n, m, .loop body => by
      simp only [StackAlloc.comp, getCodeLabels]
      exact stackAllocGetCodeLabelsComp n m body
  | n, m, .call none dest handler => by
      rcases handler with _ | ⟨hp, k1, k2⟩ <;> simp only [StackAlloc.comp, getCodeLabels] <;>
        intro x hx <;>
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_empty_iff_false] at hx ⊢ <;>
        tauto
  | n, m, .call (some (rp, lr, l1, l2)) dest none => by
      have h1 := stackAllocGetCodeLabelsComp n m rp
      simp only [StackAlloc.comp, getCodeLabels]
      intro x hx
      have h1 := @h1 x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_empty_iff_false] at hx h1 ⊢
      tauto
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)) => by
      have h1 := stackAllocGetCodeLabelsComp n m rp
      have h2 := stackAllocGetCodeLabelsComp n (StackAlloc.comp n m rp).2 hp
      simp only [StackAlloc.comp, getCodeLabels]
      intro x hx
      have h1 := @h1 x
      have h2 := @h2 x
      simp only [Set.mem_union, Set.mem_insert_iff] at hx h1 h2 ⊢
      tauto
  | n, m, .alloc k => by
      simp [StackAlloc.comp, getCodeLabels]
  | n, m, .storeConsts t1 t2 (some loc) => by
      simp [StackAlloc.comp, getCodeLabels]
  | _, _, .storeConsts _ _ none | _, _, .skip | _, _, .halt _ | _, _, .tick
  | _, _, .ret _ | _, _, .raise _ | _, _, .break _ | _, _, .continue _
  | _, _, .inst _ | _, _, .get _ _ | _, _, .set _ _ | _, _, .opCurrHeap _ _ _
  | _, _, .jumpLower _ _ _ | _, _, .rawCall _ | _, _, .install _ _ _ _ _
  | _, _, .shMemOp _ _ _ | _, _, .codeBufferWrite _ _ | _, _, .dataBufferWrite _ _
  | _, _, .ffi _ _ _ _ _ _ | _, _, .locValue _ _ _ | _, _, .stackAlloc _
  | _, _, .stackFree _ | _, _, .stackLoad _ _ | _, _, .stackLoadAny _ _
  | _, _, .stackStore _ _ | _, _, .stackStoreAny _ _ | _, _, .stackGetSize _
  | _, _, .stackSetSize _ | _, _, .bitmapLoad _ _ => by
      simp only [StackAlloc.comp]; exact Set.subset_insert _ _
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

/-- HOL `stack_alloc_stack_get_handler_labels_comp`. HOL's binders `pp mm` do not
occur in the statement and are omitted. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_stack_get_handler_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackAllocStackGetHandlerLabelsComp {width : Nat} [NeZero width] {i : Nat} :
    ∀ (n m : Nat) (p : HolProg width),
      stackGetHandlerLabels i (StackAlloc.comp n m p).1 = stackGetHandlerLabels i p
  | n, m, .seq a b => by
      simp only [StackAlloc.comp, stackGetHandlerLabels]
      rw [stackAllocStackGetHandlerLabelsComp n m a, stackAllocStackGetHandlerLabelsComp n _ b]
  | n, m, .ite cmp r ri a b => by
      simp only [StackAlloc.comp, stackGetHandlerLabels]
      rw [stackAllocStackGetHandlerLabelsComp n m a, stackAllocStackGetHandlerLabelsComp n _ b]
  | n, m, .loop body => by
      simp only [StackAlloc.comp, stackGetHandlerLabels]
      exact stackAllocStackGetHandlerLabelsComp n m body
  | n, m, .call none dest handler => by
      simp [StackAlloc.comp, stackGetHandlerLabels]
  | n, m, .call (some (rp, lr, l1, l2)) dest none => by
      simp only [StackAlloc.comp, stackGetHandlerLabels]
      rw [stackAllocStackGetHandlerLabelsComp n m rp]
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)) => by
      simp only [StackAlloc.comp, stackGetHandlerLabels]
      rw [stackAllocStackGetHandlerLabelsComp n m rp,
        stackAllocStackGetHandlerLabelsComp n (StackAlloc.comp n m rp).2 hp]
  | n, m, .alloc k => by
      simp [StackAlloc.comp, stackGetHandlerLabels]
  | n, m, .storeConsts t1 t2 (some loc) => by
      simp [StackAlloc.comp, stackGetHandlerLabels]
  | _, _, .storeConsts _ _ none | _, _, .skip | _, _, .halt _ | _, _, .tick
  | _, _, .ret _ | _, _, .raise _ | _, _, .break _ | _, _, .continue _
  | _, _, .inst _ | _, _, .get _ _ | _, _, .set _ _ | _, _, .opCurrHeap _ _ _
  | _, _, .jumpLower _ _ _ | _, _, .rawCall _ | _, _, .install _ _ _ _ _
  | _, _, .shMemOp _ _ _ | _, _, .codeBufferWrite _ _ | _, _, .dataBufferWrite _ _
  | _, _, .ffi _ _ _ _ _ _ | _, _, .locValue _ _ _ | _, _, .stackAlloc _
  | _, _, .stackFree _ | _, _, .stackLoad _ _ | _, _, .stackLoadAny _ _
  | _, _, .stackStore _ _ | _, _, .stackStoreAny _ _ | _, _, .stackGetSize _
  | _, _, .stackSetSize _ | _, _, .bitmapLoad _ _ => by
      simp only [StackAlloc.comp]
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

/-- HOL `stack_alloc_init_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_init_code_labels" (words_as_type_indexed_bitvec)]
theorem stackAllocInitCodeLabels {width : Nat} [NeZero width] {c : DataToWord.Config} :
    getCodeLabels (StackAlloc.wordGcCode c : HolProg width) = ∅ := by
  unfold StackAlloc.wordGcCode
  split
  · simp [getCodeLabels, listSeqHOL, StackRemove.constInst]
  · simp [getCodeLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, add1Inst, orInst,
      addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
      StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode,
      StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode,
      StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode]
  · rename_i sizes _
    cases sizes
    · simp [getCodeLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcMoveDataCode,
        StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode,
        StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]
    · simp [getCodeLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode,
        StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode,
        StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode,
        StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode,
        StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode,
        StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]

theorem progComp_eq_map {width : Nat} [NeZero width] (prog : List (Nat × HolProg width)) :
    prog.map StackAlloc.progComp =
      prog.map fun np => (np.1, (StackAlloc.comp np.1 (StackAlloc.nextLabHOL np.2 2) np.2).1) := by
  rfl

/-- HOL `stack_alloc_stack_good_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_stack_good_code_labels" (words_as_type_indexed_bitvec)]
theorem stackAllocStackGoodCodeLabels {width : Nat} [NeZero width] {elabs : Set Nat} :
    ∀ (prog : List (Nat × HolProg width)) (c : DataToWord.Config),
      stackGoodCodeLabels prog elabs → stackGoodCodeLabels (StackAlloc.compile c prog) elabs := by
  intro prog c h
  rw [StackAlloc.compile, progComp_eq_map, good_iff]
  intro np hnp
  rcases List.mem_append.mp hnp with hs | hm
  · simp only [StackAlloc.stubs, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    simp [getCodeLabels, stackAllocInitCodeLabels]
  · exact codeLabels_map_sub
      (fun np => (StackAlloc.comp np.1 (StackAlloc.nextLabHOL np.2 2) np.2).1)
      {(gcStubLocation, 0)}
      (fun np _ => stackAllocStackGetHandlerLabelsComp _ _ np.2)
      (fun np _ => by
        intro x hx
        rcases stackAllocGetCodeLabelsComp _ _ np.2 hx with h | h
        · exact .inl h
        · exact .inr h)
      (by
        rintro x rfl
        rw [mem_goodRhs]
        exact .inr (.inl ⟨by simp [StackAlloc.stubs], rfl⟩))
      h np hm

/-- HOL `stack_alloc_stack_good_code_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_stack_good_code_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackAllocStackGoodCodeLabelsIncr {width : Nat} [NeZero width] {elabs : Set Nat} :
    ∀ prog : List (Nat × HolProg width),
      gcStubLocation ∈ elabs ∧ stackGoodCodeLabels prog elabs →
        stackGoodCodeLabels (prog.map StackAlloc.progComp) elabs := by
  rintro prog ⟨hgc, h⟩
  rw [progComp_eq_map, good_iff]
  have := codeLabels_map_sub (pre := [])
      (fun np => (StackAlloc.comp np.1 (StackAlloc.nextLabHOL np.2 2) np.2).1)
      {(gcStubLocation, 0)}
      (fun np _ => stackAllocStackGetHandlerLabelsComp _ _ np.2)
      (fun np _ => by
        intro x hx
        rcases stackAllocGetCodeLabelsComp _ _ np.2 hx with h | h
        · exact .inl h
        · exact .inr h)
      (by
        rintro x rfl
        rw [mem_goodRhs]
        exact .inr (.inr (.inl ⟨hgc, rfl⟩)))
      h
  simpa only [List.nil_append] using this

/-! ### stack_rawcall -/

section RawCallHelpers
variable {width : Nat} [NeZero width]

/-- The conclusion shape of `IN_get_code_labels_comp_top_lemma` (Flapjack
abbreviation). -/
def CompTopWitness (i : Spt Nat) (q : HolProg width) (p_1 p_2 : Nat) : Prop :=
  ∃ k, (p_1, k) ∈ getCodeLabels q ∧ (p_2 ≠ k → p_2 = 1 ∧ k = 0 ∧ sptMem p_1 i)

theorem CompTopWitness.refl {i : Spt Nat} {q : HolProg width} {p_1 p_2 : Nat}
    (h : (p_1, p_2) ∈ getCodeLabels q) : CompTopWitness i q p_1 p_2 :=
  ⟨p_2, h, fun hne => absurd rfl hne⟩

theorem CompTopWitness.mono {i : Spt Nat} {q q' : HolProg width} {p_1 p_2 : Nat}
    (hs : getCodeLabels q ⊆ getCodeLabels q') :
    CompTopWitness i q p_1 p_2 → CompTopWitness i q' p_1 p_2 := by
  rintro ⟨k, hk, hne⟩
  exact ⟨k, hs hk, hne⟩

end RawCallHelpers

/-- HOL `IN_get_code_labels_comp_top_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "IN_get_code_labels_comp_top_lemma" (words_as_type_indexed_bitvec)]
theorem inGetCodeLabelsCompTopLemma {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (q : HolProg width) (p_1 p_2 : Nat),
      ((p_1, p_2) ∈ getCodeLabels (StackRawCall.comp i q) →
        ∃ k, (p_1, k) ∈ getCodeLabels q ∧ (p_2 ≠ k → p_2 = 1 ∧ k = 0 ∧ sptMem p_1 i)) ∧
      ((p_1, p_2) ∈ getCodeLabels (StackRawCall.compTop i q) →
        ∃ k, (p_1, k) ∈ getCodeLabels q ∧ (p_2 ≠ k → p_2 = 1 ∧ k = 0 ∧ sptMem p_1 i)) := by
  intro info q
  induction q using StackRawCall.comp.induct with
  | case1 first second ih1 ih2 =>
    intro p_1 p_2
    have hdef : (p_1, p_2) ∈ getCodeLabels
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) →
        CompTopWitness info (.seq first second) p_1 p_2 := by
      intro h
      simp only [getCodeLabels, Set.mem_union] at h
      rcases h with h | h
      · exact CompTopWitness.mono (by simp [getCodeLabels]) ((ih1 p_1 p_2).1 h)
      · exact CompTopWitness.mono (by simp [getCodeLabels]) ((ih2 p_1 p_2).1 h)
    refine ⟨fun h => ?_, fun h => hdef (by simpa [StackRawCall.compTop] using h)⟩
    by_cases hs : StackRawCall.compSeq first second info
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) =
        .seq (StackRawCall.comp info first) (StackRawCall.comp info second)
    · simp only [StackRawCall.comp] at h
      rw [hs] at h
      exact hdef h
    · obtain ⟨k, dest, rfl, rfl⟩ := StackRawCall.compSeqNeqImp first second
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) info hs
      simp only [StackRawCall.comp, StackRawCall.compSeq, StackRawCall.destCase] at h
      split at h
      · exact hdef h
      · rename_i l hl
        have hp : p_1 = dest ∧ p_2 = 1 := by
          split at h
          · simpa [getCodeLabels] using h
          split at h <;> simpa [getCodeLabels] using h
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨0, by simp [getCodeLabels], fun _ => ⟨rfl, rfl, by simp [sptMem, sptDomain, hl]⟩⟩
  | case2 op r ri a b ihA ihB =>
    intro p_1 p_2
    suffices key : (p_1, p_2) ∈ getCodeLabels (StackRawCall.comp info (.ite op r ri a b)) →
        CompTopWitness info (.ite op r ri a b) p_1 p_2 from
      ⟨key, fun h => key (by simpa [StackRawCall.compTop] using h)⟩
    intro h
    simp only [StackRawCall.comp, getCodeLabels, Set.mem_union] at h
    repeat' (rcases (h : _ ∨ _) with h | h)
    all_goals first
      | exact CompTopWitness.refl (by simp only [getCodeLabels, Set.mem_union]; tauto)
      | exact CompTopWitness.mono (fun x hx => by simp only [getCodeLabels, Set.mem_union]; tauto)
          ((ihA p_1 p_2).1 h)
      | exact CompTopWitness.mono (fun x hx => by simp only [getCodeLabels, Set.mem_union]; tauto)
          ((ihB p_1 p_2).1 h)
  | case3 body ihA =>
    intro p_1 p_2
    suffices key : (p_1, p_2) ∈ getCodeLabels (StackRawCall.comp info (.loop body)) →
        CompTopWitness info (.loop body) p_1 p_2 from
      ⟨key, fun h => key (by simpa [StackRawCall.compTop] using h)⟩
    intro h
    simp only [StackRawCall.comp, getCodeLabels] at h
    exact CompTopWitness.mono (fun x hx => by simpa only [getCodeLabels] using hx)
      ((ihA p_1 p_2).1 h)
  | case4 body lr l1 l2 dest ihA =>
    intro p_1 p_2
    suffices key : (p_1, p_2) ∈ getCodeLabels (StackRawCall.comp info (.call (some (body, lr, l1, l2)) dest none)) →
        CompTopWitness info (.call (some (body, lr, l1, l2)) dest none) p_1 p_2 from
      ⟨key, fun h => key (by simpa [StackRawCall.compTop] using h)⟩
    intro h
    simp only [StackRawCall.comp, getCodeLabels, Set.mem_union, Set.mem_empty_iff_false,
      or_false] at h
    repeat' (rcases (h : _ ∨ _) with h | h)
    all_goals first
      | exact CompTopWitness.refl (by simp only [getCodeLabels, Set.mem_union]; tauto)
      | exact CompTopWitness.mono (fun x hx => by simp only [getCodeLabels, Set.mem_union]; tauto)
          ((ihA p_1 p_2).1 h)
  | case5 body lr l1 l2 dest hd k1 k2 ihA ihB =>
    intro p_1 p_2
    suffices key : (p_1, p_2) ∈ getCodeLabels (StackRawCall.comp info (.call (some (body, lr, l1, l2)) dest (some (hd, k1, k2)))) →
        CompTopWitness info (.call (some (body, lr, l1, l2)) dest (some (hd, k1, k2))) p_1 p_2 from
      ⟨key, fun h => key (by simpa [StackRawCall.compTop] using h)⟩
    intro h
    simp only [StackRawCall.comp, getCodeLabels, Set.mem_union] at h
    repeat' (rcases (h : _ ∨ _) with h | h)
    all_goals first
      | exact CompTopWitness.refl (by simp only [getCodeLabels, Set.mem_union]; tauto)
      | exact CompTopWitness.mono (fun x hx => by simp only [getCodeLabels, Set.mem_union]; tauto)
          ((ihA p_1 p_2).1 h)
      | exact CompTopWitness.mono (fun x hx => by simp only [getCodeLabels, Set.mem_union]; tauto)
          ((ihB p_1 p_2).1 h)
  | case6 q h1 h2 h3 h4 h5 =>
    intro p_1 p_2
    have hc : StackRawCall.comp info q = q := by
      rw [StackRawCall.comp.eq_def]
      split
      all_goals first
        | rfl
        | exact absurd rfl (h1 _ _)
        | exact absurd rfl (h2 _ _ _ _ _)
        | exact absurd rfl (h3 _)
        | exact absurd rfl (h4 _ _ _ _ _)
        | exact absurd rfl (h5 _ _ _ _ _ _ _ _)
    have ht : StackRawCall.compTop info q = q := by
      rw [StackRawCall.compTop.eq_def]
      split
      · exact absurd rfl (h1 _ _)
      · exact hc
    exact ⟨fun h => CompTopWitness.refl (hc ▸ h), fun h => CompTopWitness.refl (ht ▸ h)⟩

/-- HOL `IN_domain_collect_info`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IN_domain_collect_info"
  (words_as_type_indexed_bitvec)]
theorem inDomainCollectInfo {width : Nat} [NeZero width] :
    ∀ (prog : List (Nat × HolProg width)) (f : Spt Nat) (p_1 : Nat),
      sptMem p_1 (StackRawCall.collectInfo prog f) → p_1 ∈ prog.map Prod.fst ∨ sptMem p_1 f := by
  intro prog
  induction prog with
  | nil => intro f p_1 h; exact .inr h
  | cons np rest ih =>
    intro f p_1 h
    obtain ⟨n, body⟩ := np
    simp only [StackRawCall.collectInfo] at h
    rcases ih _ _ h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · split at h
      · exact .inr h
      · rcases (sptMem_sptInsert _ _ _ _).mp h with rfl | h
        · exact .inl (List.mem_cons_self ..)
        · exact .inr h

/-- HOL `IN_get_code_labels_comp_top`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "IN_get_code_labels_comp_top"
  (words_as_type_indexed_bitvec)]
theorem inGetCodeLabelsCompTop {width : Nat} [NeZero width] {p_1 p_2 : Nat}
    {prog : List (Nat × HolProg width)} {q : HolProg width} :
    (p_1, p_2) ∈ getCodeLabels (StackRawCall.compTop (StackRawCall.collectInfo prog .ln) q) →
      ∃ k, (p_1, k) ∈ getCodeLabels q ∧ (p_2 ≠ k → p_2 = 1 ∧ k = 0 ∧ p_1 ∈ prog.map Prod.fst) := by
  intro h
  obtain ⟨k, hk, hne⟩ := (inGetCodeLabelsCompTopLemma _ q p_1 p_2).2 h
  refine ⟨k, hk, fun hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hne hn
  refine ⟨h1, h2, ?_⟩
  rcases inDomainCollectInfo prog .ln p_1 h3 with h | h
  · exact h
  · simp at h

/-- HOL `stack_rawcall_stack_good_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_stack_good_code_labels" (words_as_type_indexed_bitvec)]
theorem stackRawcallStackGoodCodeLabels {width : Nat} [NeZero width] {elabs : Set Nat}
    {prog : List (Nat × HolProg width)} :
    stackGoodCodeLabels prog elabs → stackGoodCodeLabels (StackRawCall.compile prog) elabs := by
  intro h
  have heq : StackRawCall.compile prog = prog.map fun np =>
      (np.1, StackRawCall.compTop (StackRawCall.collectInfo prog .ln) np.2) := by
    rfl
  rw [heq, good_iff, goodRhs_map _ (fun np _ => (StackRawCall.stackGetHandlerLabelsComp _ np.2 np.1).2)]
  intro np hnp
  obtain ⟨np0, hm, rfl⟩ := List.mem_map.mp hnp
  rintro ⟨a, b⟩ hx
  obtain ⟨k, hk, hne⟩ := inGetCodeLabelsCompTop hx
  have hin := good_iff.mp h np0 hm hk
  by_cases hb : b = k
  · subst hb; exact hin
  · obtain ⟨rfl, rfl, ha⟩ := hne hb
    rw [mem_goodRhs]
    exact .inr (.inr (.inr (.inl ⟨ha, rfl⟩)))

/-! ### stack_to_lab -/

/-- HOL `stack_to_lab_stack_good_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_stack_good_code_labels" (words_as_type_indexed_bitvec)]
theorem stackToLabStackGoodCodeLabels {width : Nat} [NeZero width] {stackConf : StackToLab.Config}
    {dataConf : DataToWord.Config} {maxHeap sp : Nat} {offset : BitVec width × BitVec width}
    {prog : List (Nat × HolProg width)} {prog' : LabSem.LabProgHOL width} {elabs : Set Nat} :
    StackToLab.compile stackConf dataConf maxHeap sp offset prog = prog' ∧
      BvlToBvi.initGlobalsLocation ∈ prog.map Prod.fst ∧
      stackGoodCodeLabels prog elabs ∧
      (∀ sec ∈ prog', LabProps.secLabelsOk sec) →
      LabProps.LabelSets.getLabels prog' ⊆ LabProps.LabelSets.getCodeLabels prog' ∪ (fun n => (n, 0)) '' elabs ∪
        (fun n => (n, 1)) '' elabs := by
  rintro ⟨rfl, hloc, h, hok⟩
  refine getLabelsMapProgToSectionSubsetCodeLabels _ ⟨hok, ?_⟩
  refine stackNamesStackGoodCodeLabels _ _ (stackRemoveStackGoodCodeLabels _ ⟨?_, ?_⟩)
  · simp only [StackAlloc.compile, StackRawCall.compile, List.map_append, List.mem_append,
      List.map_map, Function.comp_def, StackAlloc.progComp]
    exact .inr hloc
  · exact stackAllocStackGoodCodeLabels _ _ (stackRawcallStackGoodCodeLabels h)

/-- HOL `stack_to_lab_stack_good_code_labels_incr`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_to_lab_stack_good_code_labels_incr" (words_as_type_indexed_bitvec)]
theorem stackToLabStackGoodCodeLabelsIncr {width : Nat} [NeZero width] {elabs : Set Nat}
    {f : Spt Nat} {jump : Bool} {offset : BitVec width × BitVec width} {sp : Nat}
    {prog : List (Nat × HolProg width)} {prog' : LabSem.LabProgHOL width} :
    StackRemove.stackErrLab ∈ elabs ∧ gcStubLocation ∈ elabs ∧
      StackToLab.compileNoStubs f jump offset sp prog = prog' ∧
      stackGoodCodeLabels prog elabs ∧
      (∀ sec ∈ prog', LabProps.secLabelsOk sec) →
      LabProps.LabelSets.getLabels prog' ⊆ LabProps.LabelSets.getCodeLabels prog' ∪ (fun n => (n, 0)) '' elabs ∪
        (fun n => (n, 1)) '' elabs := by
  rintro ⟨herr, hgc, rfl, h, hok⟩
  refine getLabelsMapProgToSectionSubsetCodeLabels _ ⟨hok, ?_⟩
  exact stackNamesStackGoodCodeLabels _ _ (stackRemoveStackGoodCodeLabelsIncr _
    ⟨herr, stackAllocStackGoodCodeLabelsIncr _ ⟨hgc, h⟩⟩)

end Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCodeLabels
