import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
import Flapjack.Compiler.Backend.StackRemove.Proofs.LabPres
import Flapjack.Compiler.Backend.StackRemove.StoreListCode
import Flapjack.Compiler.Backend.StackRawCall.Proofs.ExtractLabels
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Labels
import Flapjack.Compiler.Backend.StackNames.Proofs.LabelsCallArgs

/-! `stack_to_labProofScript.sml:3194-3347`: `MAP_FST_compile_compile`, the
rebound `next_lab_non_zero` and `MAP_prog_to_section_FST`,
`extract_label_store_list_code`, and `stack_to_lab_compile_lab_pres` (the
compiled sections are `labels_ok`). The commented-out rebinding of
`stack_to_lab_lab_pres` at line 3219 is not part of the theory. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

/-- HOL `MAP_FST_compile_compile` (local). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_FST_compile_compile"
  (words_as_type_indexed_bitvec)]
theorem mapFstCompileCompile {width : Nat} [NeZero width] {jump : Bool}
    {off : BitVec width × BitVec width} {gen : Bool} {maxHeap k : Nat}
    {c : DataToWord.Config} {code : List (Nat × HolProg width)} :
    (StackRemove.compileHOL jump off gen maxHeap k BvlToBvi.initGlobalsLocation
        (StackAlloc.compile c (StackRawCall.compile code))).map Prod.fst =
      0 :: 1 :: 2 :: gcStubLocation :: code.map Prod.fst := by
  simp [StackRemove.compileHOL, StackRemove.initStubs, StackAlloc.compile, StackAlloc.stubs,
    StackRawCall.compile, StackRemove.progComp, StackAlloc.progComp, List.map_map,
    Function.comp_def]

/-- HOL `next_lab_non_zero` (rebound at line 3211): both start labels are
bounds of the program's next label. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "next_lab_non_zero" 3211
  (words_as_type_indexed_bitvec)]
theorem nextLabNonZero' {width : Nat} [NeZero width] :
    ∀ p : HolProg width, 1 ≤ StackAlloc.nextLabHOL p 1 ∧ 2 ≤ StackAlloc.nextLabHOL p 2 := by
  intro p
  rw [StackAlloc.next_lab_EQ_MAX p 0 1, StackAlloc.next_lab_EQ_MAX p 0 2]
  omega

/-- HOL `MAP_prog_to_section_FST` (local, rebound at line 3272 with the same
statement as at line 228). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "MAP_prog_to_section_FST" 3272
  (words_as_type_indexed_bitvec)]
theorem mapProgToSectionFst' {width : Nat} [NeZero width] (prog : List (Nat × HolProg width)) :
    (prog.map progToSectionHOL).map (fun s => s.sectionId) = prog.map Prod.fst :=
  mapProgToSectionFst prog

/-- HOL `extract_label_store_list_code` (local). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "extract_label_store_list_code"
  (words_as_type_indexed_bitvec)]
theorem extractLabelStoreListCode {width : Nat} [NeZero width] :
    ∀ (a t : Nat) (ls : List (BitVec width ⊕ Nat)),
      StackPropsCodeLabels.extractLabels (StackRemove.storeListCode a t ls) = [] := by
  intro a t ls
  induction ls with
  | nil => simp [StackRemove.storeListCode, StackPropsCodeLabels.extractLabels]
  | cons x xs ih =>
    rcases x with v | r <;>
      simp [StackRemove.storeListCode, StackPropsCodeLabels.extractLabels, listSeqHOL,
        addBytesInWordInst, ih]


/-- The stack_remove initializer has no labels (HOL's `EVAL_TAC` step). -/
theorem extractLabels_initCode {width : Nat} [NeZero width] (gen : Bool) (maxHeap k : Nat) :
    StackPropsCodeLabels.extractLabels (StackRemove.initCode (width := width) gen maxHeap k) =
      [] := by
  simp [StackRemove.initCode, StackPropsCodeLabels.extractLabels, listSeqHOL,
    extractLabelStoreListCode, StackRemove.initMemory, moveHOL, subInst, addInst,
    addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst]

/-- The stack_alloc garbage-collector stub has no labels (HOL's `EVAL_TAC`
step). -/
theorem extractLabels_wordGcCode {width : Nat} [NeZero width] (c : DataToWord.Config) :
    StackPropsCodeLabels.extractLabels (StackAlloc.wordGcCode (width := width) c) = [] := by
  unfold StackAlloc.wordGcCode
  split
  · simp [StackPropsCodeLabels.extractLabels, listSeqHOL, StackRemove.constInst]
  · simp [StackPropsCodeLabels.extractLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst,
      addInst, add1Inst, orInst, addBytesInWordInst, StackRemove.leftShiftInst,
      StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst,
      StackRemove.storeInst,
      StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode,
      StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode,
      StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode]
  · rename_i sizes _
    cases sizes
    · simp [StackPropsCodeLabels.extractLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst,
        addInst, andInst, add1Inst, orInst, addBytesInWordInst, StackRemove.leftShiftInst,
        StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst,
        StackRemove.storeInst, StackAlloc.memcpyCode, StackAlloc.clearTopInst,
        StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcMoveDataCode,
        StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode,
        StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]
    · simp [StackPropsCodeLabels.extractLabels, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst,
        addInst, andInst, add1Inst, orInst, addBytesInWordInst, StackRemove.leftShiftInst,
        StackRemove.rightShiftInst, StackRemove.constInst, StackRemove.loadInst,
        StackRemove.storeInst, StackAlloc.memcpyCode, StackAlloc.clearTopInst,
        StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode,
        StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode,
        StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode,
        StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode,
        StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode,
        StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]

/-- Label conditions of one compiled section entry (Flapjack abbreviation of
the per-procedure conjunct of `stack_to_lab_compile_lab_pres`). -/
def EntryLabelsOk {width : Nat} [NeZero width] (np : Nat × HolProg width) : Prop :=
  (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
    (StackPropsCodeLabels.extractLabels np.2).Nodup

theorem entryLabelsOk_of_nil {width : Nat} [NeZero width] {np : Nat × HolProg width}
    (h : StackPropsCodeLabels.extractLabels np.2 = []) : EntryLabelsOk np := by
  simp [EntryLabelsOk, h]

/-- HOL `stack_to_lab_compile_lab_pres`: if the source procedure names avoid
the stub locations and each procedure's labels are its own, nonzero, not 1 and
distinct, the compiled sections are `labels_ok`. The `let labs` binding is
inlined. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_compile_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem stackToLabCompileLabPres {width : Nat} [NeZero width] {c : StackToLab.Config}
    {c2 : DataToWord.Config} {c3 sp : Nat} {offset : BitVec width × BitVec width}
    {prog : List (Nat × HolProg width)} :
    (∀ n ∈ prog.map Prod.fst, n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gcStubLocation) ∧
    (∀ np ∈ prog,
      (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
      (StackPropsCodeLabels.extractLabels np.2).Nodup) ∧
    (prog.map Prod.fst).Nodup →
    labelsOk (StackToLab.compile c c2 c3 sp offset prog) := by
  rintro ⟨hnames, hlabs, hnd⟩
  unfold StackToLab.compile
  refine progToSectionLabelsOk ⟨?_, ?_⟩
  · intro np hmem
    simp only [StackNames.compileHOL, List.mem_map] at hmem
    obtain ⟨q, hq, rfl⟩ := hmem
    show EntryLabelsOk (StackNames.progCompEntryHOL c.regNames q)
    unfold EntryLabelsOk
    simp only [StackNames.progCompEntryHOL, ← StackNames.stackNamesLabPres]
    simp only [StackRemove.compileHOL, List.mem_append, List.mem_map] at hq
    rcases hq with hq | ⟨r, hr, rfl⟩
    · simp only [StackRemove.initStubs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        exact entryLabelsOk_of_nil (by
          simp [StackPropsCodeLabels.extractLabels, extractLabels_initCode, StackRemove.haltInst])
    · simp only [StackRemove.progComp, ← StackRemove.Proofs.LabPres.stackRemoveLabPres]
      simp only [StackAlloc.compile, List.mem_append, List.mem_map] at hr
      rcases hr with hr | ⟨⟨n, p'⟩, hp', rfl⟩
      · simp only [StackAlloc.stubs, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact entryLabelsOk_of_nil (by
          simp [StackPropsCodeLabels.extractLabels, extractLabels_wordGcCode])
      · simp only [StackRawCall.compile, List.mem_map] at hp'
        obtain ⟨⟨n0, p0⟩, hp0, he⟩ := hp'
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hE, hD⟩ := hlabs _ hp0
        have hc := (StackRawCall.extractLabelsComp (StackRawCall.collectInfo prog .ln) p0).2
        simp only [StackAlloc.progComp]
        set q := StackRawCall.compTop (StackRawCall.collectInfo prog .ln) p0
        have := StackAlloc.stack_alloc_lab_pres n0 (StackAlloc.nextLabHOL q 2) q 0
          ⟨by rw [hc]; exact hE, by rw [hc]; exact hD, Nat.le_refl _⟩
        exact ⟨this.1, this.2.1⟩
  · rw [StackNames.map_fst_compileHOL, mapFstCompileCompile]
    have h3 : ∀ n ∈ prog.map Prod.fst, n ≠ gcStubLocation := fun n h => (hnames n h).2.2.2
    simp only [List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by decide, by decide, by decide, fun h => (hnames 0 h).1 rfl⟩,
      ⟨by decide, by decide, fun h => (hnames 1 h).2.1 rfl⟩,
      ⟨by decide, fun h => (hnames 2 h).2.2.1 rfl⟩, fun h => h3 _ h rfl, hnd⟩

end Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
