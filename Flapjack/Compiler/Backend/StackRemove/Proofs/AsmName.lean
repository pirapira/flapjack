import Flapjack.Compiler.Backend.StackRemove.Comp
import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackRemove.InitStubs
import Flapjack.Compiler.Backend.StackRemove.InitCode
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.RemoveNames
import Flapjack.Misc.GoodDimindex

/-! `stack_remove_comp_stack_asm_name` and `stack_remove_stack_asm_name`
(`stack_removeProofScript.sml:4209-4300`): under the assembler-configuration
premises, stack removal produces programs whose instructions satisfy
`stack_asm_name`. HOL's `n2w (n * (dimindex (:'a) DIV 8))` is
`BitVec.ofNat width (n * (width / 8))`, `addr_offset_ok c w` is
`asmAddrOffsetOkExact c w`, and `INL Add`/`INL Sub` are `Sum.inl .add`/`.sub`. -/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.AsmName
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackRemove

section Gadgets
variable {width : Nat} [NeZero width] {c : AsmConfigExact width}

theorem regName_of_le {a b : Nat} (h : regName a c) (hle : b ≤ a) : regName b c := by
  simp only [regName] at *; omega

/-- The immediate premise of `stack_remove_comp_stack_asm_name` at `word_offset`. -/
def ImmOk (c : AsmConfigExact width) : Prop :=
  ∀ n, n ≤ maxStackAlloc →
    c.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
    c.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true

theorem ImmOk.sub (h : ImmOk c) {n : Nat} (hn : n ≤ maxStackAlloc) :
    c.validImm (.inl .sub) (wordOffset n) = true := by
  rw [wordOffset, Nat.mul_comm]; exact (h n hn).1

theorem ImmOk.add (h : ImmOk c) {n : Nat} (hn : n ≤ maxStackAlloc) :
    c.validImm (.inl .add) (wordOffset n) = true := by
  rw [wordOffset, Nat.mul_comm]; exact (h n hn).2

theorem ImmOk.bytes (h : ImmOk c) :
    c.validImm (.inl .add) (wordSemBytesInWord (width := width)) = true := by
  have := (h 1 (by simp [maxStackAlloc])).2
  simpa [wordSemBytesInWord] using this

theorem upshift_name (h : ImmOk c) {r : Nat} (hr : regName r c) :
    ∀ n, stackAsmName c (upshift (width := width) r n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [upshift]
    split
    · simp [stackAsmName, instName, arithName, regImmName, hr, h.add ‹_›]
    · refine ⟨?_, ih _ (by simp only [maxStackAlloc] at *; omega)⟩
      simp [stackAsmName, instName, arithName, regImmName, hr, h.add (Nat.le_refl _)]

theorem downshift_name (h : ImmOk c) {r : Nat} (hr : regName r c) :
    ∀ n, stackAsmName c (downshift (width := width) r n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [downshift]
    split
    · simp [stackAsmName, instName, arithName, regImmName, hr, h.sub ‹_›]
    · refine ⟨?_, ih _ (by simp only [maxStackAlloc] at *; omega)⟩
      simp [stackAsmName, instName, arithName, regImmName, hr, h.sub (Nat.le_refl _)]

theorem stackFree_name (h : ImmOk c) {r : Nat} (hr : regName r c) :
    ∀ n, stackAsmName c (stackFree (width := width) r n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [stackFree]
    split
    · simp [stackAsmName]
    split
    · simp [singleStackFree, stackAsmName, instName, arithName, regImmName, hr, h.add ‹_›]
    · refine ⟨?_, ih _ (by simp only [maxStackAlloc] at *; omega)⟩
      simp [singleStackFree, stackAsmName, instName, arithName, regImmName, hr,
        h.add (Nat.le_refl _)]

theorem stackAlloc_name (h : ImmOk c) {r : Nat} (hr : regName r c) (h1 : regName 1 c)
    (jump : Bool) : ∀ n, stackAsmName c (stackAlloc (width := width) jump r n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [stackAlloc]
    split
    · simp [stackAsmName]
    split
    · unfold singleStackAlloc
      split <;> simp [stackAsmName, instName, arithName, regImmName, hr, h1, haltInst,
        h.sub ‹_›]
    · refine ⟨?_, ih _ (by simp only [maxStackAlloc] at *; omega)⟩
      unfold singleStackAlloc
      split <;> simp [stackAsmName, instName, arithName, regImmName, hr, h1, haltInst,
        h.sub (Nat.le_refl _)]

end Gadgets

theorem leftShift_name {width : Nat} [NeZero width] {c : AsmConfigExact width}
    (hdim : goodDimindex width) {r : Nat} (hr : regName r c) :
    stackAsmName c (leftShiftInst (width := width) r (wordShiftAmount width)) := by
  rcases hdim with rfl | rfl <;>
    simp [leftShiftInst, wordShiftAmount, stackAsmName, instName, arithName, hr]

theorem rightShift_name {width : Nat} [NeZero width] {c : AsmConfigExact width}
    (hdim : goodDimindex width) {r : Nat} (hr : regName r c) :
    stackAsmName c (rightShiftInst (width := width) r (wordShiftAmount width)) := by
  rcases hdim with rfl | rfl <;>
    simp [rightShiftInst, wordShiftAmount, stackAsmName, instName, arithName, hr]

theorem copyLoop_name {width : Nat} [NeZero width] {c : AsmConfigExact width}
    (hdim : goodDimindex width) (hb : c.validImm (.inl .add) (wordSemBytesInWord (width := width)) = true)
    (h0 : asmAddrOffsetOkExact c 0 = true) (h1 : regName 1 c) (h2 : regName 2 c)
    (h3 : regName 3 c) {t b : Nat} (ht : regName t c) (hbm : regName b c) :
    stackAsmName c (copyLoop (width := width) t b) := by
  have hs1 : stackAsmName c (rightShiftInst (width := width) 1 1) := by
    rcases hdim with rfl | rfl <;> simp [rightShiftInst, stackAsmName, instName, arithName, h1]
  simp_all [copyLoop, copyEach, whileHOL, listSeqHOL, stackAsmName, instName, arithName,
    regImmName, addrName, loadInst, storeInst, addBytesInWordInst, addInst]

theorem shift_name {width : Nat} [NeZero width] {c : AsmConfigExact width} (hdim : goodDimindex width)
    {r : Nat} (hr : regName r c) :
    stackAsmName c (leftShiftInst (width := width) r (wordShiftAmount width)) ∧
      stackAsmName c (rightShiftInst (width := width) r (wordShiftAmount width)) := by
  rcases hdim with rfl | rfl <;>
    simp [leftShiftInst, rightShiftInst, wordShiftAmount, stackAsmName, instName, arithName, hr]

/-- HOL `stack_remove_comp_stack_asm_name`. HOL's free `c` is implicit; all
eleven premises are kept in order. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "stack_remove_comp_stack_asm_name" (words_as_type_indexed_bitvec)]
theorem stackRemoveCompStackAsmName {width : Nat} [NeZero width] {c : AsmConfigExact width} :
    ∀ (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) (p : HolProg width),
      stackAsmName c p ∧ stackAsmRemove c p ∧ asmAddrOffsetOkExact c 0 = true ∧
        goodDimindex width ∧
        (∀ n, n ≤ maxStackAlloc →
          c.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
          c.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true) ∧
        (∀ s, asmAddrOffsetOkExact c (storeOffset s) = true) ∧
        regName (k + 2) c ∧ regName (k + 1) c ∧ regName k c ∧ k ≠ 0 ∧ off = c.addrOffset →
      stackAsmName c (comp jump off k p) := by
  intro jump off k p
  induction p using comp.induct (bounds := off) <;>
    rintro ⟨hn, hr, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩
  case case19 first second ihA ihB =>
    simp only [stackAsmName, stackAsmRemove] at hn hr
    simp only [comp, stackAsmName]
    first
      | exact ⟨ihA ⟨hn.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩,
          ihB ⟨hn.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩⟩
      | exact ⟨ihB ⟨hn.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩,
          ihA ⟨hn.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩⟩
  case case20 first second ihA ihB =>
    simp only [stackAsmName, stackAsmRemove] at hn hr
    simp only [comp, stackAsmName]
    first
      | exact ⟨ihA ⟨hn.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩,
          ihB ⟨hn.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩⟩
      | exact ⟨ihB ⟨hn.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩,
          ihA ⟨hn.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩⟩
  case case21 body ih =>
    simp only [stackAsmName, stackAsmRemove] at hn hr
    simp only [comp, stackAsmName]
    exact ih ⟨hn, hr, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩
  case case22 ret target handler ihA ihB =>
    rcases ret with _ | ⟨bd, lr, l1, l2⟩ <;> rcases handler with _ | ⟨hd, k1, k2⟩ <;>
      simp only [stackAsmName, stackAsmRemove, and_true] at hn hr ihA ihB ⊢ <;>
      simp only [comp, stackAsmName, and_true]
    · exact hn
    · exact hn
    · first
        | exact ⟨hn.1, ihA ⟨hn.2, hr, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩⟩
        | exact ⟨hn.1, ihB ⟨hn.2, hr, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩⟩
    · first
        | exact ⟨hn.1, ihA ⟨hn.2.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩,
            ihB ⟨hn.2.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩⟩
        | exact ⟨hn.1, ihB ⟨hn.2.1, hr.1, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩,
            ihA ⟨hn.2.2, hr.2, h0, hdim, himm, hst, hk2, hk1, hk, hk0⟩⟩
  all_goals
    have hi : ImmOk c := himm
    have h1 : regName 1 c := regName_of_le hk (by omega)
    have h2 : regName 2 c := regName_of_le hk1 (by omega)
    have h3 : regName 3 c := regName_of_le hk2 (by omega)
    have hb := hi.bytes
    have hsk := shift_name hdim hk
    have hsk1 := shift_name hdim hk1
    have hs1 : stackAsmName c (rightShiftInst (width := width) 1 1) := by
      rcases hdim with rfl | rfl <;> simp [rightShiftInst, stackAsmName, instName, arithName, h1]
    clear himm
    try simp only [comp]
  all_goals (try split) <;>
    (try simp_all [stackAsmName, stackAsmRemove, instName, arithName, regImmName, addrName,
      moveInst, moveHOL, addInst, subInst, stackStore, stackLoad, listSeqHOL,
      upshift_name, downshift_name, stackFree_name,
      stackAlloc_name, asmAddrOffsetOkExact, leftShift_name, rightShift_name, copyLoop_name])
  all_goals simp_all (config := { zetaDelta := true })
  all_goals trace_state
  all_goals sorry

theorem storeListCode_name {width : Nat} [NeZero width] {c : AsmConfigExact width}
    (hb : c.validImm (.inl .add) (wordSemBytesInWord (width := width)) = true)
    (h0 : asmAddrOffsetOkExact c 0 = true) {a t : Nat} (ha : regName a c) (ht : regName t c) :
    ∀ vs : List (Sum (BitVec width) Nat), (∀ r, Sum.inr r ∈ vs → regName r c) →
      stackAsmName c (storeListCode a t vs) := by
  intro vs
  induction vs with
  | nil => intro _; simp [storeListCode, stackAsmName]
  | cons v vs ih =>
    intro hv
    have hrest := ih (fun r hr => hv r (List.mem_cons_of_mem _ hr))
    rcases v with w | r
    · simp_all [storeListCode, listSeqHOL, stackAsmName, instName, arithName, regImmName,
        addrName, addBytesInWordInst]
    · have hr := hv r List.mem_cons_self
      simp_all [storeListCode, listSeqHOL, stackAsmName, instName, arithName, regImmName,
        addrName, addBytesInWordInst]

theorem initCode_name {width : Nat} [NeZero width] {c : AsmConfigExact width}
    (h0 : asmAddrOffsetOkExact c 0 = true) (hdim : goodDimindex width)
    (h4 : c.validImm (.inl .add) 4 = true) (h8 : c.validImm (.inl .add) 8 = true)
    (h7 : regName 7 c) {k : Nat} (hk2 : regName (k + 2) c) (hk1 : regName (k + 1) c)
    (hk : regName k c) (gen : Bool) (mh : Nat) :
    stackAsmName c (initCode (width := width) gen mh k) := by
  have r : ∀ n, n ≤ 7 → regName n c := fun n hn => regName_of_le h7 hn
  have hb : c.validImm (.inl .add) (wordSemBytesInWord (width := width)) = true := by
    rcases hdim with rfl | rfl
    · exact h4
    · exact h8
  have hsl : ∀ v q, storeInit (width := width) gen k v = .inr q → q = k + 2 ∨ q ≤ 7 := by
    intro v q h
    cases v <;> simp [storeInit] at h <;> (try split at h) <;> (try simp at h) <;> omega
  have hmem : ∀ q, Sum.inr q ∈ (storeList.reverse.map (storeInit (width := width) gen k)) →
      regName q c := by
    intro q hq
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hq
    rcases hsl v q hv with rfl | hle
    · exact hk2
    · exact r q hle
  have hstore := storeListCode_name hb h0 hk1 (r 0 (by omega)) _ hmem
  rcases hdim with rfl | rfl <;>
    simp_all [initCode, listSeqHOL, initMemory, stackAsmName, instName, arithName,
      regImmName, addrName, moveHOL, subInst, addInst, addBytesInWordInst, constInst,
      loadInst, storeInst, leftShiftInst, rightShiftInst, wordShiftAmount, bytesInWord]

/-- HOL `stack_remove_stack_asm_name`. HOL's free `c prog jump gen_gc max_heap
k start` are implicit; all thirteen premises are kept in order. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "stack_remove_stack_asm_name" (words_as_type_indexed_bitvec)]
theorem stackRemoveStackAsmName {width : Nat} [NeZero width] {c : AsmConfigExact width}
    {prog : List (Nat × HolProg width)} {jump genGc : Bool} {maxHeap k start : Nat} :
    (∀ np ∈ prog, stackAsmName c np.2) ∧ (∀ np ∈ prog, stackAsmRemove c np.2) ∧
      asmAddrOffsetOkExact c 0 = true ∧ goodDimindex width ∧
      (∀ n, n ≤ maxStackAlloc →
        c.validImm (.inl .sub) (BitVec.ofNat width (n * (width / 8))) = true ∧
        c.validImm (.inl .add) (BitVec.ofNat width (n * (width / 8))) = true) ∧
      c.validImm (.inl .add) 4 = true ∧ c.validImm (.inl .add) 8 = true ∧
      (∀ s, asmAddrOffsetOkExact c (storeOffset s) = true) ∧
      regName 7 c ∧ regName (k + 2) c ∧ regName (k + 1) c ∧ regName k c ∧ k ≠ 0 →
      ∀ np ∈ compileHOL jump c.addrOffset genGc maxHeap k start prog, stackAsmName c np.2 := by
  rintro ⟨hn, hr, h0, hdim, himm, h4, h8, hst, h7, hk2, hk1, hk, hk0⟩ np hnp
  simp only [compileHOL, initStubs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hnp
  have h1 : regName 1 c := regName_of_le h7 (by omega)
  rcases hnp with (rfl | rfl | rfl) | ⟨⟨n, p⟩, hm, rfl⟩
  · simp [stackAsmName, initCode_name h0 hdim h4 h8 h7 hk2 hk1 hk]
  · simp [stackAsmName, haltInst, instName, h1]
  · simp [stackAsmName, haltInst, instName, h1]
  · exact stackRemoveCompStackAsmName jump c.addrOffset k p
      ⟨hn _ hm, hr _ hm, h0, hdim, himm, hst, hk2, hk1, hk, hk0, rfl⟩

end Flapjack.Compiler.Backend.StackRemove.Proofs.AsmName
