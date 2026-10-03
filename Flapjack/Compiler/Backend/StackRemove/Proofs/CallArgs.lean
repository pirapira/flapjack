import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackProps.CallArgs

/-! `stack_remove_call_args` (`stack_removeProofScript.sml`): the
stack_remove compiler keeps the `call_args p 1 2 3 4 0` convention of every
procedure, and its stubs satisfy it. -/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.CallArgs
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove

section
variable {width : Nat} [NeZero width]

theorem callArgs_stackAlloc (jump : Bool) (pointer : Nat) :
    ∀ count, callArgs (stackAlloc (width := width) jump pointer count) 1 2 3 4 0 := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [stackAlloc]
    split
    · simp [callArgs]
    split
    · unfold singleStackAlloc; split <;> simp [callArgs, haltInst]
    · simp only [callArgs]
      refine ⟨by unfold singleStackAlloc; split <;> simp [callArgs, haltInst], ih _ ?_⟩
      simp only [maxStackAlloc] at *; omega

theorem callArgs_stackFree (pointer : Nat) :
    ∀ count, callArgs (stackFree (width := width) pointer count) 1 2 3 4 0 := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [stackFree]
    split
    · simp [callArgs]
    split
    · simp [singleStackFree, callArgs]
    · simp only [callArgs]
      refine ⟨by simp [singleStackFree, callArgs], ih _ ?_⟩
      simp only [maxStackAlloc] at *; omega

theorem callArgs_upshift (register : Nat) :
    ∀ count, callArgs (upshift (width := width) register count) 1 2 3 4 0 := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [upshift]
    split
    · simp [callArgs]
    · simp only [callArgs, true_and]
      apply ih; simp only [maxStackAlloc] at *; omega

theorem callArgs_downshift (register : Nat) :
    ∀ count, callArgs (downshift (width := width) register count) 1 2 3 4 0 := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [downshift]
    split
    · simp [callArgs]
    · simp only [callArgs, true_and]
      apply ih; simp only [maxStackAlloc] at *; omega

theorem callArgs_comp (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) :
    ∀ p : HolProg width, callArgs p 1 2 3 4 0 → callArgs (comp jump off k p) 1 2 3 4 0 := by
  intro p
  induction p using comp.induct (bounds := off) <;>
    (try simp only [comp]) <;>
    (try split) <;>
    (try simp_all [callArgs, callArgs_stackAlloc, callArgs_stackFree,
      callArgs_upshift, callArgs_downshift, stackStore, stackLoad, moveInst, moveHOL,
      addInst, subInst, leftShiftInst, rightShiftInst, loadInst, storeInst, addBytesInWordInst,
      listSeqHOL, copyLoop, copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [comp, callArgs]

end

theorem callArgs_storeListCode {width : Nat} [NeZero width] (a t : Nat) :
    ∀ ls : List (BitVec width ⊕ Nat), callArgs (storeListCode a t ls) 1 2 3 4 0 := by
  intro ls
  induction ls with
  | nil => simp [storeListCode, callArgs]
  | cons x xs ih =>
    rcases x with v | r <;> simp [storeListCode, callArgs, listSeqHOL, addBytesInWordInst, ih]

theorem callArgs_initCode {width : Nat} [NeZero width] (gen : Bool) (maxHeap k : Nat) :
    callArgs (initCode (width := width) gen maxHeap k) 1 2 3 4 0 := by
  simp [initCode, callArgs, listSeqHOL, initMemory, callArgs_storeListCode, moveHOL, subInst,
    addInst, addBytesInWordInst, leftShiftInst, rightShiftInst, constInst, loadInst, storeInst]

/-- HOL `stack_remove_call_args`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_call_args"
  (words_as_type_indexed_bitvec)]
theorem stackRemoveCallArgs {width : Nat} [NeZero width] {jump : Bool}
    {off : BitVec width × BitVec width} {genGc : Bool} {n k pos : Nat}
    {p p' : List (Nat × HolProg width)} :
    compileHOL jump off genGc n k pos p = p' ∧ (∀ q ∈ p.map Prod.snd, callArgs q 1 2 3 4 0) →
      ∀ q ∈ p'.map Prod.snd, callArgs q 1 2 3 4 0 := by
  rintro ⟨rfl, h⟩ q hq
  simp only [compileHOL, initStubs, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    Function.comp_def] at hq
  rcases hq with (rfl | rfl | rfl) | ⟨⟨a, b⟩, hab, rfl⟩
  · exact ⟨callArgs_initCode _ _ _, by simp [callArgs]⟩
  · simp [callArgs, haltInst]
  · simp [callArgs, haltInst]
  · exact callArgs_comp jump off k b (h b (List.mem_map.mpr ⟨(a, b), hab, rfl⟩))

end Flapjack.Compiler.Backend.StackRemove.Proofs.CallArgs
