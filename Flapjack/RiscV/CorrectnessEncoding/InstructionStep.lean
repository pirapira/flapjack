import Flapjack.RiscV.CorrectnessEncoding.Skip
import Flapjack.RiscV.CorrectnessEncoding.Immediate
import Flapjack.RiscV.CorrectnessEncoding.DecodeAddi
import Flapjack.RiscV.CorrectnessEncoding.DecodeUpperImmediates
import Flapjack.RiscV.L3.Defs.UpperJump

/-! Flapjack native instruction-step infrastructure. No separately named HOL
originals exist for these compositions. The internal write_next interface is
used only with proved literal Run equations; specialized instruction steps
below derive them and take no target-evaluation premise. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem byte0 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 7 0 w = BitVec.extractLsb' 0 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte1 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 15 8 w = BitVec.extractLsb' 8 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte2 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 23 16 w = BitVec.extractLsb' 16 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte3 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w = BitVec.extractLsb' 24 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem reassemble (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w ++
      (RiscV.L3.holWordExtract 8 23 16 w ++
        (RiscV.L3.holWordExtract 8 15 8 w ++
          RiscV.L3.holWordExtract 8 7 0 w)) = w := by
  rw [byte0,byte1,byte2,byte3]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

private theorem encoded_fetch (ms : riscv_state) (w : BitVec 32)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    Fetch ms = (.Word w, {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}) := by
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _ at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _ at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _ at b3
  rw [fetch_bare ms vm]
  have lo0 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 0 = true := by
    simpa [byte0] using low0
  have lo1 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 1 = true := by
    simpa [byte0] using low1
  simp [rawReadInst, boolify8, b0, b1, b2, b3, lo0, lo1, «write'Skip»]
  exact reassemble w

def writePost (ms : riscv_state) (r : BitVec 5) (v : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_gpr := holUpdate ms.procID (holUpdate r v (ms.c_gpr ms.procID)) ms.c_gpr
    c_PC := holUpdate ms.procID (ms.c_PC ms.procID + 4) ms.c_PC}

theorem aligned_add_four (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 4) = true := by
  have he := congrArg BitVec.toNat (of_decide_eq_true h)
  rw [holAlign_eq_div] at he
  simp only [BitVec.toNat_ofNat] at he
  change decide (holAlign 2 (pc + 4) = pc + 4) = true
  apply decide_eq_true
  apply BitVec.eq_of_toNat_eq
  rw [holAlign_eq_div]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  have four : (4 : BitVec 64).toNat = 4 := by decide
  rw [four]
  norm_num at *
  have bound := pc.isLt
  omega

theorem write_post_rel (s : AsmState 64) (ms : riscv_state) (r : Nat)
    (v : BitVec 64) (bound : r < 32)
    (hr : targetStateRel riscvTarget s ms) :
    targetStateRel riscvTarget (updPc (s.pc + 4) (updReg r v s))
      (writePost ms (BitVec.ofNat 5 r) v) := by
  rcases hr with ⟨ok, pc, mem, regs, fp⟩
  have fields := (riscvOk_iff ms).mp ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (riscvOk_iff _).mpr
    simpa [writePost, holUpdate] using
      ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,
        aligned_add_four _ fields.2.2.2.2⟩
  · change (writePost ms (BitVec.ofNat 5 r) v).c_PC ms.procID = s.pc + 4
    change ms.c_PC ms.procID = s.pc at pc
    simp [writePost, holUpdate, pc]
  · exact mem
  · intro i hi
    have ibound : i < 32 := hi.1
    have ri := regs i hi
    change ms.c_gpr ms.procID (BitVec.ofNat 5 i) = s.regs i at ri
    change (writePost ms (BitVec.ofNat 5 r) v).c_gpr ms.procID (BitVec.ofNat 5 i) =
      (if i = r then v else s.regs i)
    by_cases eq : i = r
    · subst i
      simp [writePost, holUpdate]
    · have ne : BitVec.ofNat 5 r ≠ BitVec.ofNat 5 i := by
        intro e
        have n := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at n
        norm_num at n
        rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt ibound] at n
        exact eq n.symm
      simp [writePost, holUpdate, eq, ne, ri]
  · intro i hi
    change i < 0 at hi
    omega

theorem write_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
    (r : BitVec 5) (v : BitVec 64) (rn : r ≠ 0#5)
    (ok : riscvOk ms = true) (decode : DecodeAny (.Word w) = i)
    (run : Run i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (v,r) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip})
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    NextRISCV ms = some (writePost ms r v) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  let written : riscv_state := {fetched with
    c_gpr := holUpdate ms.procID (holUpdate r v (ms.c_gpr ms.procID)) ms.c_gpr}
  have hf := encoded_fetch ms w fields.1 low0 low1 b0 b1 b2 b3
  have hr : Run i fetched = written := by
    rw [run]
    simp [«write'GPR», «write'gpr», fetched, written, rn]
  have hn := nextRISCV ms (.Word w) fetched i written
    ⟨hf, decode, hr, fields.2.2.2.1, fields.2.2.1⟩
  simpa [update_pc, «write'PC», Skip, fetched, written, writePost, holUpdate] using hn


end Flapjack.RiscV.TargetProof
