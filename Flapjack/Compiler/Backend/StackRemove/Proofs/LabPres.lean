import Flapjack.Compiler.Backend.StackRemove.Comp
import Flapjack.Compiler.Backend.StackProps.OrderedLabels

/-! `stack_remove_lab_pres` (`stack_removeProofScript.sml:4176-4200`):
`stack_remove$comp` preserves the extracted labels. -/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.LabPres
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackPropsCodeLabels
open Flapjack.Compiler.Backend.StackRemove

section
variable {width : Nat} [NeZero width]

theorem extractLabels_stackAlloc (jump : Bool) (pointer : Nat) :
    ∀ count, extractLabels (stackAlloc (width := width) jump pointer count) = [] := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [stackAlloc]
    split
    · simp [extractLabels]
    split
    · unfold singleStackAlloc; split <;> simp [extractLabels, haltInst]
    · simp only [extractLabels, List.append_eq_nil_iff]
      refine ⟨by unfold singleStackAlloc; split <;> simp [extractLabels, haltInst], ih _ ?_⟩
      simp only [maxStackAlloc] at *; omega

theorem extractLabels_stackFree (pointer : Nat) :
    ∀ count, extractLabels (stackFree (width := width) pointer count) = [] := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [stackFree]
    split
    · simp [extractLabels]
    split
    · simp [singleStackFree, extractLabels]
    · simp only [extractLabels, List.append_eq_nil_iff]
      refine ⟨by simp [singleStackFree, extractLabels], ih _ ?_⟩
      simp only [maxStackAlloc] at *; omega

theorem extractLabels_upshift (register : Nat) :
    ∀ count, extractLabels (upshift (width := width) register count) = [] := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [upshift]
    split
    · simp [extractLabels]
    · simp only [extractLabels, List.nil_append]
      apply ih; simp only [maxStackAlloc] at *; omega

theorem extractLabels_downshift (register : Nat) :
    ∀ count, extractLabels (downshift (width := width) register count) = [] := by
  intro count
  induction count using Nat.strongRecOn with
  | _ count ih =>
    rw [downshift]
    split
    · simp [extractLabels]
    · simp only [extractLabels, List.nil_append]
      apply ih; simp only [maxStackAlloc] at *; omega

end

/-- HOL `stack_remove_lab_pres`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem stackRemoveLabPres {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) (p : HolProg width),
      extractLabels p = extractLabels (comp jump off k p) := by
  intro jump off k p
  induction p using comp.induct (bounds := off) <;>
    (try simp only [comp]) <;>
    (try split) <;>
    (try simp_all [extractLabels, extractLabels_stackAlloc, extractLabels_stackFree,
      extractLabels_upshift, extractLabels_downshift, stackStore, stackLoad, moveInst, moveHOL,
      addInst, subInst, leftShiftInst, rightShiftInst, loadInst, storeInst, addBytesInWordInst,
      listSeqHOL, copyLoop, copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [comp, extractLabels]

end Flapjack.Compiler.Backend.StackRemove.Proofs.LabPres
