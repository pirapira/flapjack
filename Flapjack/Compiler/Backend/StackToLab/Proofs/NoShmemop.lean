import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.LabProps.CodeSafety
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackRemove.Comp

/-! The `no_shmemop` chain of `stack_to_labProofScript.sml:4732-4986`: every
stack-to-lab pass preserves the absence of `ShMemOp`, and the flattened and
compiled Lab code then contains no `ShareMem` instruction
(`no_share_mem_inst`). HOL's Boolean predicates are Lean `Bool`s; `EVERY` over
a list is a membership quantifier with the tuple lambdas rendered by
projections. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.NoShmemop
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled

/-- HOL `stack_rawcall_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackRawcallCompNoShmemop {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (p : HolProg width),
      noShmemop p = true → noShmemop (StackRawCall.comp i p) = true := by
  intro info body
  induction body using StackRawCall.comp.induct with
  | case1 first second ihFirst ihSecond =>
    intro h
    simp only [noShmemop, Bool.and_eq_true] at h
    by_cases hs : StackRawCall.compSeq first second info
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) =
        .seq (StackRawCall.comp info first) (StackRawCall.comp info second)
    · simp [StackRawCall.comp, hs, noShmemop, ihFirst h.1, ihSecond h.2]
    · obtain ⟨k, dest, rfl, rfl⟩ := StackRawCall.compSeqNeqImp first second
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) info hs
      simp only [StackRawCall.comp, StackRawCall.compSeq, StackRawCall.destCase]
      split <;> try simp_all [noShmemop]
      all_goals split <;> try simp_all [noShmemop]
      all_goals split <;> try simp_all [noShmemop]
  | _ => intro h; simp_all [StackRawCall.comp, noShmemop]

/-- HOL `stack_rawcall_comp_top_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_comp_top_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackRawcallCompTopNoShmemop {width : Nat} [NeZero width] {i : Spt Nat} :
    ∀ p : HolProg width, noShmemop p = true → noShmemop (StackRawCall.compTop i p) = true := by
  intro p h
  rw [StackRawCall.compTop.eq_def]
  split
  · rename_i a b
    simp only [noShmemop, Bool.and_eq_true] at h ⊢
    exact ⟨stackRawcallCompNoShmemop i a h.1, stackRawcallCompNoShmemop i b h.2⟩
  · exact stackRawcallCompNoShmemop i _ h

/-- HOL `stack_rawcall_compile_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_compile_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackRawcallCompileNoShmemop {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ StackRawCall.compile prog, noShmemop ap.2 = true := by
  intro prog h ap hap
  simp only [StackRawCall.compile, List.mem_map] at hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := hap
  exact stackRawcallCompTopNoShmemop p (h _ hm)

/-- HOL `stack_alloc_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_comp_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackAllocCompNoShmemop {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
      noShmemop p = true → noShmemop (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [noShmemop, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noShmemop, Bool.and_eq_true]
      exact ⟨stackAllocCompNoShmemop n m a h.1, stackAllocCompNoShmemop n _ b h.2⟩
  | n, m, .ite cmp r ri a b, h => by
      simp only [noShmemop, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noShmemop, Bool.and_eq_true]
      exact ⟨stackAllocCompNoShmemop n m a h.1, stackAllocCompNoShmemop n _ b h.2⟩
  | n, m, .loop body, h => by
      simp only [noShmemop] at h
      simp only [StackAlloc.comp, noShmemop]
      exact stackAllocCompNoShmemop n m body h
  | n, m, .call none dest handler, h => by
      simp [StackAlloc.comp, noShmemop]
  | n, m, .call (some (rp, lr, l1, l2)) dest none, h => by
      simp only [noShmemop, Bool.and_true] at h
      simp only [StackAlloc.comp, noShmemop, Bool.and_true]
      exact stackAllocCompNoShmemop n m rp h
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), h => by
      simp only [noShmemop, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noShmemop, Bool.and_eq_true]
      exact ⟨stackAllocCompNoShmemop n m rp h.1, stackAllocCompNoShmemop n _ hp h.2⟩
  | n, m, .alloc k, _ => by
      simp [StackAlloc.comp, noShmemop]
  | n, m, .storeConsts t1 t2 (some loc), _ => by
      simp [StackAlloc.comp, noShmemop]
  | _, _, .storeConsts _ _ none, h | _, _, .skip, h | _, _, .halt _, h | _, _, .tick, h
  | _, _, .ret _, h | _, _, .raise _, h | _, _, .break _, h | _, _, .continue _, h
  | _, _, .inst _, h | _, _, .get _ _, h | _, _, .set _ _, h | _, _, .opCurrHeap _ _ _, h
  | _, _, .jumpLower _ _ _, h | _, _, .rawCall _, h | _, _, .install _ _ _ _ _, h
  | _, _, .shMemOp _ _ _, h | _, _, .codeBufferWrite _ _, h | _, _, .dataBufferWrite _ _, h
  | _, _, .ffi _ _ _ _ _ _, h | _, _, .locValue _ _ _, h | _, _, .stackAlloc _, h
  | _, _, .stackFree _, h | _, _, .stackLoad _ _, h | _, _, .stackLoadAny _ _, h
  | _, _, .stackStore _ _, h | _, _, .stackStoreAny _ _, h | _, _, .stackGetSize _, h
  | _, _, .stackSetSize _, h | _, _, .bitmapLoad _ _, h => by
      simp only [StackAlloc.comp]; exact h
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

/-- HOL `stack_alloc_prog_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_prog_comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackAllocProgCompNoShmemop {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ prog.map StackAlloc.progComp, noShmemop ap.2 = true := by
  intro prog h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackAllocCompNoShmemop a _ p (h _ hm)

/-- The garbage-collector stub has no `ShMemOp` (HOL's `EVAL_TAC` step). -/
theorem noShmemop_wordGcCode {width : Nat} [NeZero width] (c : DataToWord.Config) :
    noShmemop (StackAlloc.wordGcCode (width := width) c) = true := by
  unfold StackAlloc.wordGcCode
  split
  · simp [noShmemop, listSeqHOL, StackRemove.constInst]
  · simp [noShmemop, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, add1Inst, orInst,
      addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
      StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode,
      StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode,
      StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode]
  · rename_i sizes _
    cases sizes
    · simp [noShmemop, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcMoveDataCode,
        StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode,
        StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]
    · simp [noShmemop, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
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

/-- HOL `stack_alloc_compile_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_compile_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackAllocCompileNoShmemop {width : Nat} [NeZero width] {data : DataToWord.Config}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ StackAlloc.compile data prog, noShmemop ap.2 = true := by
  intro h ap hap
  simp only [StackAlloc.compile, StackAlloc.stubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hap
  rcases hap with rfl | hap
  · simp [noShmemop, noShmemop_wordGcCode]
  · exact stackAllocProgCompNoShmemop prog h ap hap

/-- HOL `upshift_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "upshift_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem upshiftNoShmemop {width : Nat} [NeZero width] :
    ∀ k n : Nat, noShmemop (StackRemove.upshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.upshift]
    split
    · simp [noShmemop]
    · simp only [noShmemop, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `downshift_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "downshift_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem downshiftNoShmemop {width : Nat} [NeZero width] :
    ∀ k n : Nat, noShmemop (StackRemove.downshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.downshift]
    split
    · simp [noShmemop]
    · simp only [noShmemop, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_free_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_free_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackFreeNoShmemop {width : Nat} [NeZero width] :
    ∀ k n : Nat, noShmemop (StackRemove.stackFree k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackFree]
    split
    · simp [noShmemop]
    split
    · simp [StackRemove.singleStackFree, noShmemop]
    · simp only [noShmemop, Bool.and_eq_true]
      refine ⟨by simp [StackRemove.singleStackFree, noShmemop], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_alloc_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackAllocNoShmemop {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (k n : Nat),
      noShmemop (StackRemove.stackAlloc jump k n : HolProg width) = true := by
  intro jump k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackAlloc]
    split
    · simp [noShmemop]
    split
    · unfold StackRemove.singleStackAlloc; split <;> simp [noShmemop, StackRemove.haltInst]
    · simp only [noShmemop, Bool.and_eq_true]
      refine ⟨by unfold StackRemove.singleStackAlloc; split <;>
        simp [noShmemop, StackRemove.haltInst], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_remove_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_comp_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackRemoveCompNoShmemop {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) (p : HolProg width),
      noShmemop p = true → noShmemop (StackRemove.comp jump off k p) = true := by
  intro jump off k p
  induction p using StackRemove.comp.induct (bounds := off) <;>
    (try simp only [StackRemove.comp]) <;>
    (try split) <;>
    (try simp_all [noShmemop, stackAllocNoShmemop, stackFreeNoShmemop, upshiftNoShmemop,
      downshiftNoShmemop, StackRemove.stackStore, StackRemove.stackLoad, moveInst,
      moveHOL, addInst, subInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.loadInst, StackRemove.storeInst, addBytesInWordInst, listSeqHOL,
      StackRemove.copyLoop, StackRemove.copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [StackRemove.comp, noShmemop]

/-- HOL `stack_remove_prog_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_prog_comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackRemoveProgCompNoShmemop {width : Nat} [NeZero width] {Name : Type} {jump : Bool}
    {off : BitVec width × BitVec width} {k : Nat} {n : Name} :
    ∀ p : HolProg width, noShmemop p = true →
      noShmemop (StackRemove.progComp jump off k (n, p)).2 = true :=
  fun p h => stackRemoveCompNoShmemop jump off k p h

/-- The stack_remove initializer has no `ShMemOp` (HOL's `EVAL_TAC` step). -/
theorem noShmemop_initCode {width : Nat} [NeZero width] (gen : Bool) (maxHeap k : Nat) :
    noShmemop (StackRemove.initCode (width := width) gen maxHeap k) = true := by
  have hs : ∀ (a t : Nat) (ls : List (BitVec width ⊕ Nat)),
      noShmemop (StackRemove.storeListCode a t ls) = true := by
    intro a t ls
    induction ls with
    | nil => simp [StackRemove.storeListCode, noShmemop]
    | cons x xs ih =>
      rcases x with v | r <;>
        simp [StackRemove.storeListCode, noShmemop, listSeqHOL, addBytesInWordInst, ih]
  simp [StackRemove.initCode, noShmemop, listSeqHOL, StackRemove.initMemory, hs, moveHOL,
    subInst, addInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst]

/-- HOL `stack_remove_compile_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_compile_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackRemoveCompileNoShmemop {width : Nat} [NeZero width] {jump : Bool}
    {offset : BitVec width × BitVec width} {gckind : Bool} {mh sp loc : Nat}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ StackRemove.compileHOL jump offset gckind mh sp loc prog, noShmemop ap.2 = true := by
  intro h ap hap
  simp only [StackRemove.compileHOL, StackRemove.initStubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hap
  rcases hap with (rfl | rfl | rfl) | ⟨⟨a, p⟩, hm, rfl⟩
  · simp [noShmemop, noShmemop_initCode]
  · simp [noShmemop, StackRemove.haltInst]
  · simp [noShmemop, StackRemove.haltInst]
  · exact stackRemoveCompNoShmemop jump offset sp p (h _ hm)

/-- HOL `stack_remove_prog_comp_no_shmemop_MAP`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_prog_comp_no_shmemop_MAP" (words_as_type_indexed_bitvec)]
theorem stackRemoveProgCompNoShmemopMap {width : Nat} [NeZero width] {Name : Type} {jump : Bool}
    {offset : BitVec width × BitVec width} {sp : Nat} {prog : List (Name × HolProg width)} :
    (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ prog.map (StackRemove.progComp jump offset sp), noShmemop ap.2 = true := by
  intro h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackRemoveCompNoShmemop jump offset sp p (h _ hm)

/-- HOL `stack_names_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_comp_no_shmemop"
  (words_as_type_indexed_bitvec)]
theorem stackNamesCompNoShmemop {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width),
      noShmemop p = true → noShmemop (StackNames.progCompHOL f p) = true := by
  intro f p
  induction p using StackNames.progCompHOL.induct <;>
    try simp_all [StackNames.progCompHOL, noShmemop]
  rename_i rh _ hd ih2 ih1
  rcases rh with _ | ⟨rp, lr, l1, l2⟩ <;> rcases hd with _ | ⟨hp, h1, h2⟩ <;>
    simp_all [StackNames.progCompHOL, noShmemop]

/-- HOL `stack_names_prog_comp_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_prog_comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackNamesProgCompNoShmemop {width : Nat} [NeZero width] {Name : Type} {f : Spt Nat} :
    ∀ prog : List (Name × HolProg width), (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ prog.map (StackNames.progCompEntryHOL f), noShmemop ap.2 = true := by
  intro prog h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackNamesCompNoShmemop f p (h _ hm)

/-- HOL `stack_names_compile_no_shmemop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_compile_no_shmemop" (words_as_type_indexed_bitvec)]
theorem stackNamesCompileNoShmemop {width : Nat} [NeZero width] {Name : Type} {names : Spt Nat}
    {prog : List (Name × HolProg width)} :
    (∀ ap ∈ prog, noShmemop ap.2 = true) →
      ∀ ap ∈ StackNames.compileHOL names prog, noShmemop ap.2 = true :=
  stackNamesProgCompNoShmemop prog

/-- A Lab line that is not a `ShareMem` instruction (Flapjack infrastructure). -/
def lineNoShareMem {width : Nat} [NeZero width] : LabSem.LabLineHOL width → Bool
  | .asm (.shareMem _ _ _) _ _ => false
  | _ => true

theorem flattenAllNoShareMem {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat), noShmemop p = true →
      (appListAppend (flattenHOL t p n m cs bs).1).all lineNoShareMem = true := by
  intro t p n m cs bs
  induction t, p, m, cs, bs using flattenHOL.induct n
  all_goals
    intro hns
    rw [flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split) <;>
    (try simp only [FlattenCorrect.appListAppendList, FlattenCorrect.appListAppendAppend,
      noShmemop, Bool.and_eq_true, lineNoShareMem, compileJumpHOL, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (repeat' split) <;> (try simp only [FlattenCorrect.appListAppendList,
      FlattenCorrect.appListAppendAppend,
      Bool.and_eq_true, lineNoShareMem, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (try obtain ⟨hns1, hns2⟩ := hns)
  all_goals (repeat' constructor) <;> (try solve_by_elim)
  all_goals rename_i h; split at h <;> simp at h

/-- HOL `flatten_no_share_mem_inst`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem flattenNoShareMemInst {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat), noShmemop p = true →
      ∀ ln ∈ appListAppend (flattenHOL t p n m cs bs).1,
        ∀ op re a inst len, ln ≠ .asm (.shareMem op re a) inst len := by
  intro t p n m cs bs h ln hln op re a inst len heq
  have := List.all_eq_true.mp (flattenAllNoShareMem t p n m cs bs h) ln hln
  rw [heq] at this
  simp [lineNoShareMem] at this

/-- HOL `asm_fetch_aux_no_share_mem_inst_CONS`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "asm_fetch_aux_no_share_mem_inst_CONS" (words_as_type_indexed_bitvec)]
theorem asmFetchAuxNoShareMemInstCons {width : Nat} [NeZero width] {k : Nat}
    {ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) (BitVec width)))} :
    ∀ xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) (BitVec width)),
      (∀ ln ∈ xs, ∀ op re a inst len, ln ≠ .asm (.shareMem op re a) inst len) ∧
        LabProps.noShareMemInst ls →
      LabProps.noShareMemInst (⟨k, xs⟩ :: ls) := by
  intro xs ⟨hxs, hls⟩
  induction xs with
  | nil =>
    intro pos op re a inst len
    rw [LabSem.asmFetchAux]
    exact hls pos op re a inst len
  | cons x xs ih =>
    have ih' := ih (fun ln h => hxs ln (List.mem_cons_of_mem _ h))
    intro pos op re a inst len
    rw [LabSem.asmFetchAux]
    split
    · exact ih' pos op re a inst len
    split
    · intro h
      exact hxs x List.mem_cons_self op re a inst len (Option.some.inj h)
    · exact ih' (pos - 1) op re a inst len

/-- HOL `prog_to_section_no_share_mem_inst`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "prog_to_section_no_share_mem_inst" (words_as_type_indexed_bitvec)]
theorem progToSectionNoShareMemInst {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noShmemop ap.2 = true) →
      LabProps.noShareMemInst (prog.map progToSectionHOL) := by
  intro prog h
  induction prog with
  | nil =>
    intro pos op re a inst len
    simp [LabSem.asmFetchAux]
  | cons e es ih =>
    obtain ⟨a, p⟩ := e
    rw [List.map_cons, progToSection_eq]
    refine asmFetchAuxNoShareMemInstCons _ ⟨fun ln hln => ?_,
      ih (fun ap hap => h ap (List.mem_cons_of_mem _ hap))⟩
    rcases List.mem_append.mp hln with hln | hln
    · exact flattenNoShareMemInst true p a _ [] [] (h _ List.mem_cons_self) ln hln
    · simp only [List.mem_singleton] at hln
      subst hln
      intro op re a inst len h
      cases h

/-- HOL `compile_no_share_mem_inst`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "compile_no_share_mem_inst"
  (words_as_type_indexed_bitvec)]
theorem compileNoShareMemInst {width : Nat} [NeZero width] {stackConf : StackToLab.Config}
    {dataConf : DataToWord.Config} {maxHeap sp : Nat} {offset : BitVec width × BitVec width} :
    ∀ (prog : List (Nat × HolProg width)) (prog' : LabSem.LabProgHOL width),
      (∀ ap ∈ prog, noShmemop ap.2 = true) ∧
        StackToLab.compile stackConf dataConf maxHeap sp offset prog = prog' →
      LabProps.noShareMemInst prog' := by
  rintro prog _ ⟨h, rfl⟩
  exact progToSectionNoShareMemInst _ (stackNamesCompileNoShmemop
    (stackRemoveCompileNoShmemop (stackAllocCompileNoShmemop
      (stackRawcallCompileNoShmemop prog h))))

/-- HOL `compile_no_stubs_no_share_mem_inst`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "compile_no_stubs_no_share_mem_inst" (words_as_type_indexed_bitvec)]
theorem compileNoStubsNoShareMemInst {width : Nat} [NeZero width] {f : Spt Nat} {jump : Bool}
    {offset : BitVec width × BitVec width} {sp : Nat} {prog : List (Nat × HolProg width)}
    {prog' : LabSem.LabProgHOL width} :
    (∀ ap ∈ prog, noShmemop ap.2 = true) ∧
      StackToLab.compileNoStubs f jump offset sp prog = prog' →
    LabProps.noShareMemInst prog' := by
  rintro ⟨h, rfl⟩
  exact progToSectionNoShareMemInst _ (stackNamesCompileNoShmemop
    (stackRemoveProgCompNoShmemopMap (stackAllocProgCompNoShmemop prog h)))

end Flapjack.Compiler.Backend.StackToLab.Proofs.NoShmemop
