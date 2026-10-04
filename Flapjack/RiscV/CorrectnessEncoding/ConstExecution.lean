import Flapjack.RiscV.CorrectnessEncoding.ConstStep
import Flapjack.Misc.BytesInMemory
import Flapjack.Compiler.Encoders.AsmProps.Assertions

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.AsmProps
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Original domain graph projection determines every byte in that domain.
Untagged infrastructure, not a separately named HOL theorem. -/
theorem projected_memory_eq (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (h : riscvProj d ms = riscvProj d ns) (a : BitVec 64) (inside : d a) :
    ms.MEM8 a = ns.MEM8 a := by
  simp only [riscvProj, Prod.mk.injEq] at h
  have member : SetSep.fun2Set (ms.MEM8,d) (a,ms.MEM8 a) :=
    (SetSep.fun2SetThm _ _ _ _).mpr ⟨rfl,inside⟩
  rw [h.2.2.2.2.2.1] at member
  exact ((SetSep.fun2SetThm _ _ _ _).mp member).1.symm

/-- Transport a literal original emitted-byte region through original
projection equality. No agreement outside the original domain is assumed. -/
theorem bytes_projection_transfer (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (h : riscvProj d ms = riscvProj d ns) (pc : BitVec 64) (bs : List (BitVec 8))
    (bytes : bytesInMemoryHOL pc bs ms.MEM8 d) :
    bytesInMemoryHOL pc bs ns.MEM8 d := by
  induction bs generalizing pc with
  | nil => trivial
  | cons b bs ih =>
    rcases bytes with ⟨value,inside,tail⟩
    exact ⟨(projected_memory_eq d ms ns h pc inside).symm.trans value,
      inside, ih (pc + 1) tail⟩

/-- Extract all four literal instruction bytes from the original native byte
region predicate, retaining its original domain obligations at the call site. -/
theorem encoded_bytes_of_region (d : BitVec 64 → Prop) (ms : riscv_state)
    (i : instruction)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (riscvEncode i) ms.MEM8 d) :
    encodedInstructionBytes ms i := by
  simp only [riscvEncode, bytesInMemoryHOL] at bytes
  exact ⟨bytes.1, bytes.2.2.1,
    by simpa [BitVec.add_assoc] using bytes.2.2.2.2.1,
    by simpa [BitVec.add_assoc] using bytes.2.2.2.2.2.2.1⟩

/-- Actual faithful native target iterator with environment interleaved after
each step. The instruction list supplies only the number of native steps;
every transition calls original `riscvTarget.next`. Untagged iteration
infrastructure, not a replacement evaluator or a named HOL port. -/
noncomputable def constNativeExecute (env : Nat → riscv_state → riscv_state)
    (index : Nat) (is : List instruction) (ms : riscv_state) : riscv_state :=
  match is with
  | [] => ms
  | _ :: tail => constNativeExecute env (index + 1) tail (env index (riscvTarget.next ms))

/-- Actual whole native execution follows the complete pure step list from
original emitted bytes and original projection-preserving interference.
All fetch, validity and remaining-byte premises are derived internally;
no target execution or post-state relation is an input. Untagged composition
infrastructure; the full original Const assertions remain separate open work. -/
theorem const_native_execute (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (nonzero : ∀ i ∈ is, constDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    constNativeExecute env index is ms = constStepInterleaved env index is ms := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have rn := nonzero i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, constDestination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := next_const_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = constStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := const_step_frame i kind ms ok
    have stepOk := const_step_ok i kind ms ok
    have envProjection := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((constStep i ms).c_PC (constStep i ms).procID)
        (is.flatMap riscvEncode) (constStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (constStep i ms)
      (env index (constStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (constStep i ms)).c_PC (env index (constStep i ms)).procID =
        (constStep i ms).c_PC (constStep i ms).procID := by
      have fields := envProjection
      simp only [riscvProj, Prod.mk.injEq] at fields
      exact fields.2.2.2.2.2.2
    rw [← pcEq] at envBytes
    simp only [constNativeExecute, constStepInterleaved, step]
    exact ih tailKinds tailNonzero (index + 1) _ envOk envBytes

/-- Full original projection of actual native execution, derived from emitted
bytes, equals the complete pure-step list effect, including scratch31 and PC.
No target execution hypothesis; not a separately named HOL theorem. -/
theorem const_native_execute_projection (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (nonzero : ∀ i ∈ is, constDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constNativeExecute env index is ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ms) := by
  rw [const_native_execute d is kinds nonzero env index ms ok bytes interference]
  exact const_interleaved_step_projection d is kinds env index ms ok interference

/-- Actual native list execution retains original validity, advances PC by
exactly four per instruction, and preserves every byte in the original domain.
The environment may change processor identity or memory outside that domain;
no stronger preservation premise is introduced. Untagged composition
infrastructure; original full encoder assertions remain separate open work. -/
theorem const_native_execute_frame (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (nonzero : ∀ i ∈ is, constDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    let final := constNativeExecute env index is ms
    riscvOk final = true ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) ∧
      ∀ a, d a → final.MEM8 a = ms.MEM8 a := by
  have pureFrame := const_step_list_frame is kinds ms ok
  have projection := const_native_execute_projection d is kinds nonzero env index ms ok bytes interference
  have finalOk := (riscv_ok_of_projection_eq d _ _ projection).trans pureFrame.1
  have pc := projection
  simp only [riscvProj, Prod.mk.injEq] at pc
  dsimp only
  refine ⟨finalOk, pc.2.2.2.2.2.2.trans pureFrame.2.2.2, ?_⟩
  intro a inside
  exact (projected_memory_eq d _ _ projection a inside).trans
    (congrFun pureFrame.2.2.1 a)

/-- The original asserts2 memory-frame conclusion for every native instruction
in the emitted list. Each native transition is derived from original bytes;
its full memory frame discharges the original outside-domain observation.
The original decreasing assertion counter corresponds to increasing environment
indices. Untagged composition infrastructure, not full encoder correctness. -/
theorem const_native_asserts2 (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (nonzero : ∀ i ∈ is, constDestination i ≠ 0#5)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (bytes : bytesInMemoryHOL (ms.c_PC ms.procID) (is.flatMap riscvEncode) ms.MEM8 d)
    (interference : interferenceOk env (riscvProj d)) :
    asserts2 is.length (fun k => env (index + is.length - k)) riscvTarget.next ms
      (fun before after => ∀ a, ¬ d a → before.MEM8 a = after.MEM8 a) := by
  induction is generalizing index ms with
  | nil => trivial
  | cons i is ih =>
    have kind := kinds i (by simp)
    have rn := nonzero i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have tailNonzero : ∀ j ∈ is, constDestination j ≠ 0#5 :=
      fun j hj => nonzero j (List.mem_cons_of_mem i hj)
    simp only [List.flatMap_cons, bytesInMemory_append] at bytes
    have native := next_const_step i kind ms rn ok (encoded_bytes_of_region d ms i bytes.1)
    have step : riscvTarget.next ms = constStep i ms := by
      change holThe (NextRISCV ms) = _
      rw [native]
      simp [holThe]
    have frame := const_step_frame i kind ms ok
    have stepOk := const_step_ok i kind ms ok
    have envProjection := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ envProjection).trans stepOk
    have tailBytes : bytesInMemoryHOL
        ((constStep i ms).c_PC (constStep i ms).procID)
        (is.flatMap riscvEncode) (constStep i ms).MEM8 d := by
      simpa [frame.1, frame.2.1, frame.2.2, riscvEncode] using bytes.2
    have envBytes := bytes_projection_transfer d (constStep i ms)
      (env index (constStep i ms)) envProjection.symm _ _ tailBytes
    have pcEq : (env index (constStep i ms)).c_PC (env index (constStep i ms)).procID =
        (constStep i ms).c_PC (constStep i ms).procID := by
      have fields := envProjection
      simp only [riscvProj, Prod.mk.injEq] at fields
      exact fields.2.2.2.2.2.2
    rw [← pcEq] at envBytes
    have tail := ih tailKinds tailNonzero (index + 1) _ envOk envBytes
    simp only [List.length_cons, asserts2, step]
    have firstIndex : index + (is.length + 1) - (is.length + 1) = index := by omega
    rw [firstIndex]
    refine ⟨?_, ?_⟩
    · intro a _
      exact (congrFun frame.2.1 a).symm
    · have counters : index + (is.length + 1) = index + 1 + is.length := by omega
      simpa only [counters] using tail

end Flapjack.RiscV.TargetProof
