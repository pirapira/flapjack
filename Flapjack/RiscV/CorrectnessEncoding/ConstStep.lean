import Flapjack.RiscV.CorrectnessEncoding.ConstInterference

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Destination of the literal seven Const register instruction families.
Untagged infrastructure; the fallback is never used by the family proofs. -/
def constDestination (i : instruction) : BitVec 5 :=
  match i with
  | .ArithI (.LUI (rd,_)) | .ArithI (.ADDI (rd,_,_))
  | .ArithI (.ORI (rd,_,_)) | .ArithI (.XORI (rd,_,_))
  | .Shift (.SLLI (rd,_,_)) | .ArithR (.OR (rd,_,_))
  | .ArithR (.XOR (rd,_,_)) => rd
  | _ => 0#5

/-- Complete pure effect of the literal native Const Next family: register
Run effect, Skip4 and PC+4. Unlike the Run-only helper this includes native PC
advancement. No separately named HOL declaration is claimed. -/
noncomputable def constStep (i : instruction) (ms : riscv_state) : riscv_state :=
  {Run i ms with
    c_Skip := holUpdate ms.procID 4 (Run i ms).c_Skip
    c_PC := holUpdate ms.procID (ms.c_PC ms.procID + 4) (Run i ms).c_PC}

/-- Actual native Next, derived from literal emitted bytes for every member of
the full Const family. No target execution/effect is assumed. The nonzero
destination is discharged by original asm_ok in the full encoder assembly.
Untagged composition infrastructure, not a separately named HOL theorem. -/
theorem next_const_step (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (rn : constDestination i ≠ 0#5)
    (ok : riscvOk ms = true) (bytes : encodedInstructionBytes ms i) :
    NextRISCV ms = some (constStep i ms) := by
  cases kind
  all_goals simp only [constDestination] at rn
  · rename_i rd imm
    have next := next_encoded_lui ms rd imm rn ok bytes
    simpa [constStep, Run, «dfn'LUI», «write'GPR», «write'gpr», writePost, rn] using next
  · rename_i rd rs imm
    have next := next_encoded_addi ms rd rs imm rn ok bytes
    simpa [constStep, Run, «dfn'ADDI», «write'GPR», «write'gpr», writePost, rn] using next
  · rename_i rd rs imm
    have next := next_encoded_ori ms rd rs imm rn ok bytes
    simpa [constStep, Run, «dfn'ORI», «write'GPR», «write'gpr», writePost, rn] using next
  · rename_i rd rs imm
    have next := next_encoded_xori ms rd rs imm rn ok bytes
    simpa [constStep, Run, «dfn'XORI», «write'GPR», «write'gpr», writePost, rn] using next
  · rename_i rd rs shamt
    have next := next_encoded_slli ms rd rs shamt rn ok bytes
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simpa [constStep, Run, «dfn'SLLI», «write'GPR», «write'gpr», writePost, rn,
      in32BitMode, curArch, architecture, MCSR, arch] using next
  · rename_i rd rs rt
    have next := next_encoded_or ms rd rs rt rn ok bytes
    simpa [constStep, Run, «dfn'OR», «write'GPR», «write'gpr», writePost, rn] using next
  · rename_i rd rs rt
    have next := next_encoded_xor ms rd rs rt rn ok bytes
    simpa [constStep, Run, «dfn'XOR», «write'GPR», «write'gpr», writePost, rn] using next

/-- Literal complete frame of the seven native register Run clauses, including
PC and processor identity. These are conclusions, not target-run premises. -/
theorem const_run_frame (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (Run i ms).procID = ms.procID ∧ (Run i ms).c_PC = ms.c_PC ∧
    (Run i ms).MEM8 = ms.MEM8 ∧ (Run i ms).c_MCSR = ms.c_MCSR ∧
    (Run i ms).c_NextFetch = ms.c_NextFetch ∧ (Run i ms).exception = ms.exception := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases kind
  all_goals
    simp [Run, «dfn'LUI», «dfn'ADDI», «dfn'ORI», «dfn'XORI», «dfn'SLLI»,
      «dfn'OR», «dfn'XOR», in32BitMode, curArch, architecture, MCSR, arch,
      «write'GPR», «write'gpr»]
    split_ifs <;> simp

/-- Complete native pure step preserves original validity and memory, and
advances the current-core PC by exactly four. No extra mode/alignment premise. -/
theorem const_step_frame (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (constStep i ms).procID = ms.procID ∧
    (constStep i ms).MEM8 = ms.MEM8 ∧
    (constStep i ms).c_PC ms.procID = ms.c_PC ms.procID + 4 := by
  have frame := const_run_frame i kind ms ok
  simp [constStep, frame.1, frame.2.1, frame.2.2.1, holUpdate]

/-- Original riscv_ok is preserved by the complete native step, including
alignment of PC+4; its RV64 condition discharges the SLLI mode guard. -/
theorem const_step_ok (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    riscvOk (constStep i ms) = true := by
  have frame := const_run_frame i kind ms ok
  have fields := (riscvOk_iff ms).mp ok
  apply (riscvOk_iff _).mpr
  simpa [constStep, frame.1, frame.2.1, frame.2.2.2.1,
    frame.2.2.2.2.1, frame.2.2.2.2.2, holUpdate] using
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      aligned_add_four _ fields.2.2.2.2⟩

/-- Complete native step congruence under the literal original projection.
Unlike Run-only congruence this includes PC+4; scratch31 remains observable.
No separately named HOL declaration is claimed. -/
theorem const_step_projection_eq (d : BitVec 64 → Prop) (i : instruction)
    (kind : ConstRegisterInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (constStep i ms) = riscvProj d (constStep i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have fm := const_run_frame i kind ms ok
  have fn := const_run_frame i kind ns okNs
  have runH := const_run_projection_eq d i kind ms ns ok h
  simp only [riscvProj, Prod.mk.injEq, fm.1, fn.1] at runH
  simp only [riscvProj, Prod.mk.injEq] at h
  simpa [riscvProj, constStep, fm.1, fn.1, fm.2.1, fn.2.1,
    fm.2.2.1, fn.2.2.1, fm.2.2.2.1, fn.2.2.2.1,
    fm.2.2.2.2.1, fn.2.2.2.2.1, fm.2.2.2.2.2, fn.2.2.2.2.2,
    holUpdate] using
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, runH.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Whole complete-step list congruence with native PC advancement. Untagged
infrastructure for full Const execution; no target execution is assumed. -/
theorem const_step_list_projection_eq (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (is.foldl (fun s i => constStep i s) ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ns) := by
  induction is generalizing ms ns with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih (fun j hj => kinds j (List.mem_cons_of_mem i hj))
      (constStep i ms) (constStep i ns) (const_step_ok i (kinds i (by simp)) ms ok)
      (const_step_projection_eq d i (kinds i (by simp)) ms ns ok h)

/-- Interleave the original environment after each complete native Const step.
This pure effect agrees with actual Next when its emitted bytes are present,
by `next_const_step`; no encoded-list fetch/assertion assembly is claimed here. -/
noncomputable def constStepInterleaved (env : Nat → riscv_state → riscv_state)
    (index : Nat) (is : List instruction) (ms : riscv_state) : riscv_state :=
  match is with
  | [] => ms
  | i :: tail => constStepInterleaved env (index + 1) tail (env index (constStep i ms))

/-- Arbitrary complete native step lists retain their full original projection
under original interference, including PC advancement and scratch31. Untagged
composition infrastructure; no target run or scratch-preservation premise. -/
theorem const_interleaved_step_projection (d : BitVec 64 → Prop)
    (is : List instruction) (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true) (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constStepInterleaved env index is ms) =
      riscvProj d (is.foldl (fun s i => constStep i s) ms) := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepOk := const_step_ok i kind ms ok
    have hEnv := interference index (constStep i ms)
    have envOk : riscvOk (env index (constStep i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ hEnv).trans stepOk
    simp only [constStepInterleaved, List.foldl_cons]
    exact (ih tailKinds (index + 1) _ envOk).trans
      (const_step_list_projection_eq d is tailKinds _ _ envOk hEnv)

/-- Complete pure-list native frame and total PC increment, for arbitrary
length and every intrinsic operand. The emitted-byte execution connection is
proved per instruction above; full encoded-list assertions remain open. -/
theorem const_step_list_frame (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    let final := is.foldl (fun s i => constStep i s) ms
    riscvOk final = true ∧ final.procID = ms.procID ∧ final.MEM8 = ms.MEM8 ∧
      final.c_PC final.procID = ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length) := by
  induction is generalizing ms with
  | nil => simpa using ok
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have stepFrame := const_step_frame i kind ms ok
    have tail := ih tailKinds (constStep i ms) (const_step_ok i kind ms ok)
    simp only [List.foldl_cons]
    refine ⟨tail.1, tail.2.1.trans stepFrame.1, tail.2.2.1.trans stepFrame.2.1, ?_⟩
    rw [tail.2.2.2, stepFrame.1, stepFrame.2.2]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    change ms.c_PC ms.procID + 4 + BitVec.ofNat 64 (4 * is.length) =
      ms.c_PC ms.procID + (BitVec.ofNat 64 (4 * is.length) + 4)
    rw [BitVec.add_assoc, BitVec.add_comm (4 : BitVec 64) (BitVec.ofNat 64 (4 * is.length))]

end Flapjack.RiscV.TargetProof
