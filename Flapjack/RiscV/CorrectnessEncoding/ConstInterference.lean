import Flapjack.RiscV.CorrectnessEncoding.ConstNext
import Flapjack.RiscV.CorrectnessEncoding.ConstRun

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Literal register-only native instruction family used by Const lowering.
Untagged infrastructure, not a separately named HOL datatype. -/
inductive ConstRegisterInstruction : instruction → Prop
  | lui (rd : BitVec 5) (imm : BitVec 20) : ConstRegisterInstruction (.ArithI (.LUI (rd,imm)))
  | addi (rd rs : BitVec 5) (imm : BitVec 12) : ConstRegisterInstruction (.ArithI (.ADDI (rd,rs,imm)))
  | ori (rd rs : BitVec 5) (imm : BitVec 12) : ConstRegisterInstruction (.ArithI (.ORI (rd,rs,imm)))
  | xori (rd rs : BitVec 5) (imm : BitVec 12) : ConstRegisterInstruction (.ArithI (.XORI (rd,rs,imm)))
  | slli (rd rs : BitVec 5) (shamt : BitVec 6) : ConstRegisterInstruction (.Shift (.SLLI (rd,rs,shamt)))
  | or (rd rs rt : BitVec 5) : ConstRegisterInstruction (.ArithR (.OR (rd,rs,rt)))
  | xor (rd rs rt : BitVec 5) : ConstRegisterInstruction (.ArithR (.XOR (rd,rs,rt)))

/-- Source comparison: `riscv_targetScript.sml:306-315` projects VM,
ArchBase, NextFetch, exception, the ENTIRE current-core GPR function, domain
memory and PC. `asmPropsScript.sml:77-79` quantifies every index and native
state. The proofs below use those exact carriers and quantifiers. They do not
claim a separately named HOL theorem or full Next/encoder assertion result.
Projection equality preserves every original native validity field.
Untagged composition infrastructure, with no separately named HOL theorem. -/
theorem riscv_ok_of_projection_eq (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (h : riscvProj d ms = riscvProj d ns) : riscvOk ms = riscvOk ns := by
  simp only [riscvProj, Prod.mk.injEq] at h
  simp only [riscvOk]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2]

private theorem gpr_projection_eq (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (r : BitVec 5) (h : riscvProj d ms = riscvProj d ns) : GPR r ms = GPR r ns := by
  simp only [riscvProj, Prod.mk.injEq] at h
  simp [GPR, gpr, h.2.2.2.2.1]

private theorem write_gpr_ok (ms : riscv_state) (r : BitVec 5) (v : BitVec 64) :
    riscvOk («write'GPR» (v,r) ms) = riscvOk ms := by
  by_cases zero : r = 0#5 <;> simp [«write'GPR», «write'gpr», riscvOk, zero]

private theorem write_gpr_projection_eq (d : BitVec 64 → Prop)
    (ms ns : riscv_state) (r : BitVec 5) (v : BitVec 64)
    (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d («write'GPR» (v,r) ms) = riscvProj d («write'GPR» (v,r) ns) := by
  by_cases zero : r = 0#5
  · subst r
    simpa [«write'GPR»] using h
  · simp only [riscvProj, Prod.mk.injEq] at h
    simpa [riscvProj, «write'GPR», «write'gpr», holUpdate, zero] using
      ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
        congrArg (holUpdate r v) h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

/-- Every literal Const instruction preserves original riscv_ok. No separately
named HOL composition theorem exists; this is untagged infrastructure. -/
theorem const_run_ok (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) : riscvOk (Run i ms) = true := by
  cases kind
  all_goals
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simpa [Run, «dfn'LUI», «dfn'ADDI», «dfn'ORI», «dfn'XORI»,
      «dfn'SLLI», «dfn'OR», «dfn'XOR», in32BitMode, curArch,
      architecture, MCSR, arch, write_gpr_ok] using ok

/-- Whole instruction-family projection congruence, including scratch31 and
all intrinsic operands. Original riscv_ok supplies RV64 for SLLI. Untagged
infrastructure; no target evaluation is assumed. -/
theorem const_run_projection_eq (d : BitVec 64 → Prop) (i : instruction)
    (kind : ConstRegisterInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (Run i ms) = riscvProj d (Run i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have archMs := ((riscvOk_iff ms).mp ok).2.1
  have archNs := ((riscvOk_iff ns).mp okNs).2.1
  cases kind
  · rename_i rd imm
    simp only [Run, «dfn'LUI»]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs imm
    simp only [Run, «dfn'ADDI»]
    rw [gpr_projection_eq d ms ns rs h]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs imm
    simp only [Run, «dfn'ORI»]
    rw [gpr_projection_eq d ms ns rs h]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs imm
    simp only [Run, «dfn'XORI»]
    rw [gpr_projection_eq d ms ns rs h]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs shamt
    simp only [Run, «dfn'SLLI»]
    simp only [in32BitMode, curArch, architecture, MCSR, archMs, archNs]
    simp
    rw [gpr_projection_eq d ms ns rs h]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs rt
    simp only [Run, «dfn'OR»]
    rw [gpr_projection_eq d ms ns rs h, gpr_projection_eq d ms ns rt h]
    exact write_gpr_projection_eq d ms ns rd _ h
  · rename_i rd rs rt
    simp only [Run, «dfn'XOR»]
    rw [gpr_projection_eq d ms ns rs h, gpr_projection_eq d ms ns rt h]
    exact write_gpr_projection_eq d ms ns rd _ h

/-- Whole native instruction-list congruence under the literal original
projection, with no target-run or post-state relation hypothesis. Untagged
infrastructure needed by full Const interference assembly. -/
theorem const_list_projection_eq (d : BitVec 64 → Prop) (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (is.foldl (fun s i => Run i s) ms) =
      riscvProj d (is.foldl (fun s i => Run i s) ns) := by
  induction is generalizing ms ns with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih (fun j hj => kinds j (List.mem_cons_of_mem i hj))
      (Run i ms) (Run i ns) (const_run_ok i (kinds i (by simp)) ms ok)
      (const_run_projection_eq d i (kinds i (by simp)) ms ns ok h)

/-- Register-effect iteration with the original environment applied after each
instruction. This is Flapjack infrastructure, not the native Next iterator:
`Run` does not advance PC, and the full Const assertion assembly remains open. -/
noncomputable def constRunInterleaved (env : Nat → riscv_state → riscv_state)
    (index : Nat) (is : List instruction) (ms : riscv_state) : riscv_state :=
  match is with
  | [] => ms
  | i :: tail => constRunInterleaved env (index + 1) tail (env index (Run i ms))

/-- Original projection-preserving interference cannot change the observable
register effects of any list of the seven native Const instruction families.
All current-core GPRs, including scratch31, occur in `riscvProj`; no additional
scratch-preservation or target-execution premise is introduced. Untagged
infrastructure with no separately named HOL theorem. -/
theorem const_interleaved_run_projection (d : BitVec 64 → Prop)
    (is : List instruction) (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (env : Nat → riscv_state → riscv_state) (index : Nat) (ms : riscv_state)
    (ok : riscvOk ms = true) (interference : interferenceOk env (riscvProj d)) :
    riscvProj d (constRunInterleaved env index is ms) =
      riscvProj d (is.foldl (fun s i => Run i s) ms) := by
  induction is generalizing index ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have runOk := const_run_ok i kind ms ok
    have hEnv := interference index (Run i ms)
    have envOk : riscvOk (env index (Run i ms)) = true :=
      (riscv_ok_of_projection_eq d _ _ hEnv).trans runOk
    simp only [constRunInterleaved, List.foldl_cons]
    exact (ih tailKinds (index + 1) _ envOk).trans
      (const_list_projection_eq d is tailKinds _ _ envOk hEnv)

end Flapjack.RiscV.TargetProof
