import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.LabProps.CodeSafety
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackRemove.Comp

/-! The `no_install` chain of `stack_to_labProofScript.sml:4987-5209`: every
stack-to-lab pass preserves the absence of `Install`, and the flattened and
compiled Lab code then contains no `Install` instruction (labProps
`no_install`). HOL's Boolean predicates are Lean `Bool`s; `EVERY` over
a list is a membership quantifier with the tuple lambdas rendered by
projections. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.NoInstall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled

/-- HOL `stack_rawcall_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_rawcall_comp_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackRawcallCompNoInstall {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (p : HolProg width),
      noInstall p = true → noInstall (StackRawCall.comp i p) = true := by
  intro info body
  induction body using StackRawCall.comp.induct with
  | case1 first second ihFirst ihSecond =>
    intro h
    simp only [noInstall, Bool.and_eq_true] at h
    by_cases hs : StackRawCall.compSeq first second info
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) =
        .seq (StackRawCall.comp info first) (StackRawCall.comp info second)
    · simp [StackRawCall.comp, hs, noInstall, ihFirst h.1, ihSecond h.2]
    · obtain ⟨k, dest, rfl, rfl⟩ := StackRawCall.compSeqNeqImp first second
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) info hs
      simp only [StackRawCall.comp, StackRawCall.compSeq, StackRawCall.destCase]
      split <;> try simp_all [noInstall]
      all_goals split <;> try simp_all [noInstall]
      all_goals split <;> try simp_all [noInstall]
  | _ => intro h; simp_all [StackRawCall.comp, noInstall]

/-- HOL `stack_rawcall_comp_top_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_comp_top_no_install" (words_as_type_indexed_bitvec)]
theorem stackRawcallCompTopNoInstall {width : Nat} [NeZero width] {i : Spt Nat} :
    ∀ p : HolProg width, noInstall p = true → noInstall (StackRawCall.compTop i p) = true := by
  intro p h
  rw [StackRawCall.compTop.eq_def]
  split
  · rename_i a b
    simp only [noInstall, Bool.and_eq_true] at h ⊢
    exact ⟨stackRawcallCompNoInstall i a h.1, stackRawcallCompNoInstall i b h.2⟩
  · exact stackRawcallCompNoInstall i _ h

/-- HOL `stack_rawcall_compile_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_rawcall_compile_no_install" (words_as_type_indexed_bitvec)]
theorem stackRawcallCompileNoInstall {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ StackRawCall.compile prog, noInstall ap.2 = true := by
  intro prog h ap hap
  simp only [StackRawCall.compile, List.mem_map] at hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := hap
  exact stackRawcallCompTopNoInstall p (h _ hm)

/-- HOL `stack_alloc_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_comp_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackAllocCompNoInstall {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
      noInstall p = true → noInstall (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [noInstall, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noInstall, Bool.and_eq_true]
      exact ⟨stackAllocCompNoInstall n m a h.1, stackAllocCompNoInstall n _ b h.2⟩
  | n, m, .ite cmp r ri a b, h => by
      simp only [noInstall, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noInstall, Bool.and_eq_true]
      exact ⟨stackAllocCompNoInstall n m a h.1, stackAllocCompNoInstall n _ b h.2⟩
  | n, m, .loop body, h => by
      simp only [noInstall] at h
      simp only [StackAlloc.comp, noInstall]
      exact stackAllocCompNoInstall n m body h
  | n, m, .call none dest handler, h => by
      simp [StackAlloc.comp, noInstall]
  | n, m, .call (some (rp, lr, l1, l2)) dest none, h => by
      simp only [noInstall, Bool.and_true] at h
      simp only [StackAlloc.comp, noInstall, Bool.and_true]
      exact stackAllocCompNoInstall n m rp h
  | n, m, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), h => by
      simp only [noInstall, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, noInstall, Bool.and_eq_true]
      exact ⟨stackAllocCompNoInstall n m rp h.1, stackAllocCompNoInstall n _ hp h.2⟩
  | n, m, .alloc k, _ => by
      simp [StackAlloc.comp, noInstall]
  | n, m, .storeConsts t1 t2 (some loc), _ => by
      simp [StackAlloc.comp, noInstall]
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

/-- HOL `stack_alloc_prog_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_prog_comp_no_install" (words_as_type_indexed_bitvec)]
theorem stackAllocProgCompNoInstall {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ prog.map StackAlloc.progComp, noInstall ap.2 = true := by
  intro prog h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackAllocCompNoInstall a _ p (h _ hm)

/-- The garbage-collector stub has no `Install` (HOL's `EVAL_TAC` step). -/
theorem noInstall_wordGcCode {width : Nat} [NeZero width] (c : DataToWord.Config) :
    noInstall (StackAlloc.wordGcCode (width := width) c) = true := by
  unfold StackAlloc.wordGcCode
  split
  · simp [noInstall, listSeqHOL, StackRemove.constInst]
  · simp [noInstall, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, add1Inst, orInst,
      addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
      StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode,
      StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode,
      StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode]
  · rename_i sizes _
    cases sizes
    · simp [noInstall, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcMoveDataCode,
        StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode,
        StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]
    · simp [noInstall, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
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

/-- HOL `stack_alloc_compile_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_alloc_compile_no_install" (words_as_type_indexed_bitvec)]
theorem stackAllocCompileNoInstall {width : Nat} [NeZero width] {data : DataToWord.Config}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ StackAlloc.compile data prog, noInstall ap.2 = true := by
  intro h ap hap
  simp only [StackAlloc.compile, StackAlloc.stubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hap
  rcases hap with rfl | hap
  · simp [noInstall, noInstall_wordGcCode]
  · exact stackAllocProgCompNoInstall prog h ap hap

/-- HOL `upshift_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "upshift_no_install"
  (words_as_type_indexed_bitvec)]
theorem upshiftNoInstall {width : Nat} [NeZero width] :
    ∀ k n : Nat, noInstall (StackRemove.upshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.upshift]
    split
    · simp [noInstall]
    · simp only [noInstall, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `downshift_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "downshift_no_install"
  (words_as_type_indexed_bitvec)]
theorem downshiftNoInstall {width : Nat} [NeZero width] :
    ∀ k n : Nat, noInstall (StackRemove.downshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.downshift]
    split
    · simp [noInstall]
    · simp only [noInstall, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_free_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_free_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackFreeNoInstall {width : Nat} [NeZero width] :
    ∀ k n : Nat, noInstall (StackRemove.stackFree k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackFree]
    split
    · simp [noInstall]
    split
    · simp [StackRemove.singleStackFree, noInstall]
    · simp only [noInstall, Bool.and_eq_true]
      refine ⟨by simp [StackRemove.singleStackFree, noInstall], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_alloc_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_alloc_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackAllocNoInstall {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (k n : Nat),
      noInstall (StackRemove.stackAlloc jump k n : HolProg width) = true := by
  intro jump k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackAlloc]
    split
    · simp [noInstall]
    split
    · unfold StackRemove.singleStackAlloc; split <;> simp [noInstall, StackRemove.haltInst]
    · simp only [noInstall, Bool.and_eq_true]
      refine ⟨by unfold StackRemove.singleStackAlloc; split <;>
        simp [noInstall, StackRemove.haltInst], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

/-- HOL `stack_remove_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_remove_comp_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackRemoveCompNoInstall {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) (p : HolProg width),
      noInstall p = true → noInstall (StackRemove.comp jump off k p) = true := by
  intro jump off k p
  induction p using StackRemove.comp.induct (bounds := off) <;>
    (try simp only [StackRemove.comp]) <;>
    (try split) <;>
    (try simp_all [noInstall, stackAllocNoInstall, stackFreeNoInstall, upshiftNoInstall,
      downshiftNoInstall, StackRemove.stackStore, StackRemove.stackLoad, moveInst,
      moveHOL, addInst, subInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.loadInst, StackRemove.storeInst, addBytesInWordInst, listSeqHOL,
      StackRemove.copyLoop, StackRemove.copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [StackRemove.comp, noInstall]

/-- HOL `stack_remove_prog_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_prog_comp_no_install" (words_as_type_indexed_bitvec)]
theorem stackRemoveProgCompNoInstall {width : Nat} [NeZero width] {Name : Type} {jump : Bool}
    {off : BitVec width × BitVec width} {k : Nat} {n : Name} :
    ∀ p : HolProg width, noInstall p = true →
      noInstall (StackRemove.progComp jump off k (n, p)).2 = true :=
  fun p h => stackRemoveCompNoInstall jump off k p h

/-- The stack_remove initializer has no `Install` (HOL's `EVAL_TAC` step). -/
theorem noInstall_initCode {width : Nat} [NeZero width] (gen : Bool) (maxHeap k : Nat) :
    noInstall (StackRemove.initCode (width := width) gen maxHeap k) = true := by
  have hs : ∀ (a t : Nat) (ls : List (BitVec width ⊕ Nat)),
      noInstall (StackRemove.storeListCode a t ls) = true := by
    intro a t ls
    induction ls with
    | nil => simp [StackRemove.storeListCode, noInstall]
    | cons x xs ih =>
      rcases x with v | r <;>
        simp [StackRemove.storeListCode, noInstall, listSeqHOL, addBytesInWordInst, ih]
  simp [StackRemove.initCode, noInstall, listSeqHOL, StackRemove.initMemory, hs, moveHOL,
    subInst, addInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst]

/-- HOL `stack_remove_compile_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_remove_compile_no_install" (words_as_type_indexed_bitvec)]
theorem stackRemoveCompileNoInstall {width : Nat} [NeZero width] {jump : Bool}
    {offset : BitVec width × BitVec width} {gckind : Bool} {mh sp loc : Nat}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ StackRemove.compileHOL jump offset gckind mh sp loc prog, noInstall ap.2 = true := by
  intro h ap hap
  simp only [StackRemove.compileHOL, StackRemove.initStubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hap
  rcases hap with (rfl | rfl | rfl) | ⟨⟨a, p⟩, hm, rfl⟩
  · simp [noInstall, noInstall_initCode]
  · simp [noInstall, StackRemove.haltInst]
  · simp [noInstall, StackRemove.haltInst]
  · exact stackRemoveCompNoInstall jump offset sp p (h _ hm)

/-- HOL `stack_names_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_names_comp_no_install"
  (words_as_type_indexed_bitvec)]
theorem stackNamesCompNoInstall {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width),
      noInstall p = true → noInstall (StackNames.progCompHOL f p) = true := by
  intro f p
  induction p using StackNames.progCompHOL.induct <;>
    try simp_all [StackNames.progCompHOL, noInstall]
  rename_i rh _ hd ih2 ih1
  rcases rh with _ | ⟨rp, lr, l1, l2⟩ <;> rcases hd with _ | ⟨hp, h1, h2⟩ <;>
    simp_all [StackNames.progCompHOL, noInstall]

/-- HOL `stack_names_prog_comp_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_prog_comp_no_install" (words_as_type_indexed_bitvec)]
theorem stackNamesProgCompNoInstall {width : Nat} [NeZero width] {Name : Type} {f : Spt Nat} :
    ∀ prog : List (Name × HolProg width), (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ prog.map (StackNames.progCompEntryHOL f), noInstall ap.2 = true := by
  intro prog h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackNamesCompNoInstall f p (h _ hm)

/-- HOL `stack_names_compile_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "stack_names_compile_no_install" (words_as_type_indexed_bitvec)]
theorem stackNamesCompileNoInstall {width : Nat} [NeZero width] {Name : Type} {names : Spt Nat}
    {prog : List (Name × HolProg width)} :
    (∀ ap ∈ prog, noInstall ap.2 = true) →
      ∀ ap ∈ StackNames.compileHOL names prog, noInstall ap.2 = true :=
  stackNamesProgCompNoInstall prog

/-- A Lab line that is not a `Install` instruction (Flapjack infrastructure). -/
def lineNoInstall {width : Nat} [NeZero width] : LabSem.LabLineHOL width → Bool
  | .labAsm .install _ _ _ => false
  | _ => true

theorem flattenAllNoInstall {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat), noInstall p = true →
      (appListAppend (flattenHOL t p n m cs bs).1).all lineNoInstall = true := by
  intro t p n m cs bs
  induction t, p, m, cs, bs using flattenHOL.induct n
  all_goals
    intro hns
    rw [flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split) <;>
    (try simp only [FlattenCorrect.appListAppendList, FlattenCorrect.appListAppendAppend,
      noInstall, Bool.and_eq_true, lineNoInstall, compileJumpHOL, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (repeat' split) <;> (try simp only [FlattenCorrect.appListAppendList,
      FlattenCorrect.appListAppendAppend,
      Bool.and_eq_true, lineNoInstall, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (try obtain ⟨hns1, hns2⟩ := hns)
  all_goals (repeat' constructor) <;> (try solve_by_elim)
  all_goals rename_i h; split at h <;> simp at h

/-- HOL `flatten_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_no_install"
  (words_as_type_indexed_bitvec)]
theorem flattenNoInstall {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat), noInstall p = true →
      ∀ ln ∈ appListAppend (flattenHOL t p n m cs bs).1,
        ∀ w bytes l, ln ≠ .labAsm .install w bytes l := by
  intro t p n m cs bs h ln hln w bytes l heq
  have := List.all_eq_true.mp (flattenAllNoInstall t p n m cs bs h) ln hln
  rw [heq] at this
  simp [lineNoInstall] at this

/-- HOL `asm_fetch_aux_no_install_CONS`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "asm_fetch_aux_no_install_CONS" (words_as_type_indexed_bitvec)]
theorem asmFetchAuxNoInstallCons {width : Nat} [NeZero width] {k : Nat}
    {ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) (BitVec width)))} :
    ∀ xs : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) (BitVec width)),
      (∀ ln ∈ xs, ∀ w bytes l, ln ≠ .labAsm .install w bytes l) ∧
        LabProps.noInstall ls →
      LabProps.noInstall (⟨k, xs⟩ :: ls) := by
  intro xs ⟨hxs, hls⟩
  induction xs with
  | nil =>
    intro pos w bytes l
    rw [LabSem.asmFetchAux]
    exact hls pos w bytes l
  | cons x xs ih =>
    have ih' := ih (fun ln h => hxs ln (List.mem_cons_of_mem _ h))
    intro pos w bytes l
    rw [LabSem.asmFetchAux]
    split
    · exact ih' pos w bytes l
    split
    · intro h
      exact hxs x List.mem_cons_self w bytes l (Option.some.inj h)
    · exact ih' (pos - 1) w bytes l

/-- HOL `prog_to_section_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "prog_to_section_no_install" (words_as_type_indexed_bitvec)]
theorem progToSectionNoInstall {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, noInstall ap.2 = true) →
      LabProps.noInstall (prog.map progToSectionHOL) := by
  intro prog h
  induction prog with
  | nil =>
    intro pos w bytes l
    simp [LabSem.asmFetchAux]
  | cons e es ih =>
    obtain ⟨a, p⟩ := e
    rw [List.map_cons, progToSection_eq]
    refine asmFetchAuxNoInstallCons _ ⟨fun ln hln => ?_,
      ih (fun ap hap => h ap (List.mem_cons_of_mem _ hap))⟩
    rcases List.mem_append.mp hln with hln | hln
    · exact flattenNoInstall true p a _ [] [] (h _ List.mem_cons_self) ln hln
    · simp only [List.mem_singleton] at hln
      subst hln
      intro w bytes l h
      cases h

/-- HOL `stack_to_lab_compile_no_install`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "stack_to_lab_compile_no_install"
  (words_as_type_indexed_bitvec)]
theorem compileNoInstall {width : Nat} [NeZero width] {stackConf : StackToLab.Config}
    {dataConf : DataToWord.Config} {maxHeap sp : Nat} {offset : BitVec width × BitVec width} :
    ∀ (prog : List (Nat × HolProg width)) (prog' : LabSem.LabProgHOL width),
      (∀ ap ∈ prog, noInstall ap.2 = true) ∧
        StackToLab.compile stackConf dataConf maxHeap sp offset prog = prog' →
      LabProps.noInstall prog' := by
  rintro prog _ ⟨h, rfl⟩
  exact progToSectionNoInstall _ (stackNamesCompileNoInstall
    (stackRemoveCompileNoInstall (stackAllocCompileNoInstall
      (stackRawcallCompileNoInstall prog h))))

end Flapjack.Compiler.Backend.StackToLab.Proofs.NoInstall
