import Flapjack.RiscV.CorrectnessEncoding.Skip
import Flapjack.RiscV.CorrectnessEncoding.Immediate
import Flapjack.RiscV.CorrectnessEncoding.DecodeAddi
import Flapjack.RiscV.CorrectnessEncoding.DecodeUpperImmediates
import Flapjack.RiscV.L3.Defs.UpperJump

/-! Full original Loc constructor case. Local infrastructure derives both
native transitions from emitted bytes and preserves the complete assertion
conclusion; no target run is a public hypothesis. -/
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

private def writePost (ms : riscv_state) (r : BitVec 5) (v : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_gpr := holUpdate ms.procID (holUpdate r v (ms.c_gpr ms.procID)) ms.c_gpr
    c_PC := holUpdate ms.procID (ms.c_PC ms.procID + 4) ms.c_PC}

private theorem aligned_add_four (pc : BitVec 64) (h : holAligned 2 pc = true) :
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

private theorem write_post_rel (s : AsmState 64) (ms : riscv_state) (r : Nat)
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

private theorem write_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
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

private def low (c : BitVec 64) : BitVec 12 := RiscV.L3.holWordExtract 12 11 0 c
private def high (c : BitVec 64) : BitVec 20 :=
  RiscV.L3.holWordExtract 20 31 12 (c - (low c).signExtend 64)
private def upperValue (c : BitVec 64) : BitVec 64 :=
  ((high c) ++ (0#12)).signExtend 64

private theorem low_eq (c : BitVec 64) : low c = BitVec.extractLsb' 0 12 c := by
  apply BitVec.eq_of_toNat_eq
  simp [low, RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem high_eq (c : BitVec 64) :
    high c = BitVec.extractLsb' 12 20 (c - (BitVec.extractLsb' 0 12 c).signExtend 64) := by
  rw [high, low_eq]
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

/-- Local reconstruction from exactly the original Loc guard; no additional
alignment or range premise is added to the public constructor theorem. -/
private theorem loc_split (c : BitVec 64)
    (range : -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599)
    (aligned : c.toNat % 4 = 0) : upperValue c + (low c).signExtend 64 = c := by
  have zero : (BitVec.extractLsb' 0 2 c).setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, aligned]
  have bit : c.getLsbD 1 = false := by
    have e := congrArg (fun x : BitVec 64 => x.getLsbD 1) zero
    simpa using e
  have mask : (BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12) =
      BitVec.extractLsb' 0 12 c := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and]
    by_cases ei : i = 1
    · subst i
      rw [bit]
      rfl
    · have eb : (2 : BitVec 12).getLsbD i = false := by
        change Nat.testBit (2 ^ 1) i = false
        exact Nat.testBit_two_pow_of_ne (Ne.symm ei)
      rw [eb]
      simp only [Bool.not_false, Bool.and_true]
  have bounds : (0xFFFFFFFF80000000 : BitVec 64).sle c = true ∧
      c.sle 0x7FFFF7FF = true := by
    simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
    change -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599
    exact range
  have split := split_immediate_reconstruction c ⟨bounds.1,bounds.2,zero⟩
  have em : (-1 : BitVec 64) = (-1#64) := by decide
  rw [mask, em, ← BitVec.neg_eq_neg_one_mul, ← BitVec.sub_eq_add_neg] at split
  simpa [upperValue, high_eq, low_eq] using split

private theorem auipc_low (r : BitVec 5) (c : BitVec 20) :
    (Encode (.ArithI (.AUIPC (r,c)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.AUIPC (r,c)))).getLsbD 1 = true := by
  simp only [Encode, Utype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
  simp

private theorem addi_low (r : BitVec 5) (c : BitVec 12) :
    (Encode (.ArithI (.ADDI (r,r,c)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.ADDI (r,r,c)))).getLsbD 1 = true := by
  simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
  simp

private theorem auipc_run (ms : riscv_state) (r : BitVec 5) (c : BitVec 64) :
    Run (.ArithI (.AUIPC (r,high c)))
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
    «write'GPR» (ms.c_PC ms.procID + upperValue c,r)
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
  simp [Run, «dfn'AUIPC», PC, upperValue]

private theorem addi_run (ms : riscv_state) (r : BitVec 5) (c : BitVec 64) :
    Run (.ArithI (.ADDI (r,r,low c)))
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
    «write'GPR» (GPR r ms + (low c).signExtend 64,r)
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
  simp [Run, «dfn'ADDI», GPR, gpr]

private theorem loc_guard (r : Nat) (c : BitVec 64)
    (h : asmOkExact (.loc r c) riscvConfig = true) :
    (r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false) ∧
    (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧ c.toNat % 4 = 0 := by
  have both : asmRegOkExact r riscvConfig = true ∧
      asmLocOffsetOkExact riscvConfig c = true := by
    simpa only [asmOkExact, Bool.and_eq_true] using h
  have reg : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using both.1
  have off : (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧
      c.toNat % 4 = 0 := by
    have decoded : (decide (-2147483648 ≤ c.toInt) = true ∧
        decide (c.toInt ≤ 2147481599) = true) ∧ decide (c.toNat % 4 = 0) = true := by
      have original := both.2
      simp only [asmLocOffsetOkExact, asmOffsetOkExact, asmAligned,
        Bool.and_eq_true] at original
      exact original
    exact ⟨⟨of_decide_eq_true decoded.1.1, of_decide_eq_true decoded.1.2⟩,
      of_decide_eq_true decoded.2⟩
  exact ⟨reg, off⟩

private theorem loc_post (r : Nat) (c : BitVec 64) (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.loc r c) s2) :
    s2 = updPc (s1.pc + 8) (updReg r (s1.pc + c) s1) := by
  have step := h.2.2.2.2.1
  simpa [asmUpd, riscvConfig, riscvEnc, riscvEncode, riscvAst] using step.symm

private theorem auipc_step (s : AsmState 64) (ms : riscv_state)
    (r : Nat) (c : BitVec 64) (rn : BitVec.ofNat 5 r ≠ 0#5)
    (hr : targetStateRel riscvTarget s ms)
    (hb : bytesInMemoryHOL s.pc
      (riscvEncode (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c)))) s.mem s.memDomain) :
    riscvTarget.next ms = writePost ms (BitVec.ofNat 5 r) (s.pc + upperValue c) := by
  have bytes := bytes_in_memory_thm () s ms _ _ _ _ ⟨hr, hb⟩
  have lowbits := auipc_low (BitVec.ofNat 5 r) (high c)
  have native := write_next ms (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c)))
    (Encode (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c))))
    (BitVec.ofNat 5 r) (ms.c_PC ms.procID + upperValue c) rn hr.1
    (decode_encode_auipc _ _) (auipc_run ms _ c) lowbits.1 lowbits.2
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  change holThe (NextRISCV ms) = _
  rw [native]
  have pc := hr.2.1
  change ms.c_PC ms.procID = s.pc at pc
  simp [pc, holThe]

private theorem addi_step (s : AsmState 64) (ms : riscv_state)
    (r : Nat) (c : BitVec 64) (rn : BitVec.ofNat 5 r ≠ 0#5)
    (guard : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false)
    (hr : targetStateRel riscvTarget s ms)
    (hb : bytesInMemoryHOL s.pc
      (riscvEncode (.ArithI (.ADDI (BitVec.ofNat 5 r,BitVec.ofNat 5 r,low c))))
      s.mem s.memDomain) :
    riscvTarget.next ms =
      writePost ms (BitVec.ofNat 5 r) (s.regs r + (low c).signExtend 64) := by
  have bytes := bytes_in_memory_thm () s ms _ _ _ _ ⟨hr, hb⟩
  have lowbits := addi_low (BitVec.ofNat 5 r) (low c)
  have native := write_next ms (.ArithI (.ADDI (BitVec.ofNat 5 r,BitVec.ofNat 5 r,low c)))
    (Encode (.ArithI (.ADDI (BitVec.ofNat 5 r,BitVec.ofNat 5 r,low c))))
    (BitVec.ofNat 5 r) (GPR (BitVec.ofNat 5 r) ms + (low c).signExtend 64) rn hr.1
    (decode_encode_addi _ _ _) (addi_run ms _ c) lowbits.1 lowbits.2
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have reg := hr.2.2.2.1 r guard
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at reg
  have read : GPR (BitVec.ofNat 5 r) ms = s.regs r := by
    simpa [GPR, gpr, rn] using reg
  change holThe (NextRISCV ms) = _
  rw [native, read]
  simp [holThe]

private theorem loc_two_steps (r : Nat) (c : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (hs : asmStep riscvConfig s1 (.loc r c) s2)
    (hr : targetStateRel riscvTarget s1 ms)
    (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj s1.memDomain)) :
    let mid := writePost ms (BitVec.ofNat 5 r) (s1.pc + upperValue c)
    let src := updPc (s1.pc + 4) (updReg r (s1.pc + upperValue c) s1)
    riscvTarget.next ms = mid ∧
    targetStateRel riscvTarget src (env 0 mid) ∧
    riscvTarget.next (env 0 mid) =
      writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c) ∧
    targetStateRel riscvTarget s2
      (env 1 (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c))) := by
  dsimp only
  have guard := loc_guard r c hs.2.2.2.2.2.2
  have bound : r < 32 := guard.1.1
  have rn : r ≠ 0 := by
    have avoid := guard.1.2
    simp [riscvConfig] at avoid
    exact avoid.1
  have wn : BitVec.ofNat 5 r ≠ 0#5 := by
    intro e
    have n := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt bound] at n
    exact rn n
  let a := riscvEncode (.ArithI (.AUIPC (BitVec.ofNat 5 r,high c)))
  let b := riscvEncode (.ArithI (.ADDI (BitVec.ofNat 5 r,BitVec.ofNat 5 r,low c)))
  have enc : riscvConfig.encode (.loc r c) = a ++ b := rfl
  have hb := hs.1
  rw [enc, bytesInMemory_append] at hb
  let src := updPc (s1.pc + 4) (updReg r (s1.pc + upperValue c) s1)
  let mid := writePost ms (BitVec.ofNat 5 r) (s1.pc + upperValue c)
  have first : riscvTarget.next ms = mid := auipc_step s1 ms r c wn hr hb.1
  have midrel : targetStateRel riscvTarget src mid :=
    write_post_rel s1 ms r (s1.pc + upperValue c) bound hr
  have transported : targetStateRel riscvTarget src (env 0 mid) :=
    (riscv_target_ok.2 (env 0 mid) mid src (interference 0 mid)).1.mpr midrel
  have secondbytes : bytesInMemoryHOL src.pc b src.mem src.memDomain := by
    simpa [src, updPc, updReg, a, riscvEncode] using hb.2
  have value : src.regs r + (low c).signExtend 64 = s1.pc + c := by
    simp only [src, updPc, updReg, ite_true]
    rw [BitVec.add_assoc, loc_split c guard.2.1 guard.2.2]
  have second := addi_step src (env 0 mid) r c wn guard.1 transported secondbytes
  rw [value] at second
  have postrel := write_post_rel src (env 0 mid) r (s1.pc + c) bound transported
  have postsource : updPc (src.pc + 4) (updReg r (s1.pc + c) src) = s2 := by
    rw [loc_post r c s1 s2 hs]
    simp [src, updPc, updReg, BitVec.add_assoc]
    funext i
    by_cases e : i = r <;> simp [e]
  rw [postsource] at postrel
  have finalrel := (riscv_target_ok.2
    (env 1 (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)))
    (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)) s2
    (by simpa [loc_post r c s1 s2 hs, updPc, updReg] using
      interference 1 (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)))).1.mpr postrel
  exact ⟨first, transported, second, finalrel⟩

/-- Full original Loc constructor case: the original source step and state
relation are the only premises. Register/range/alignment guards are discharged
from asm_ok, and both native steps and interference assertions are proved. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml"
  "riscv_encoder_correct"]
theorem riscv_encoder_correct_loc (r : Nat) (c : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.loc r c) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.loc r c)).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  refine ⟨1, ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.loc r c) s2 := h.1
  have run := loc_two_steps r c s1 s2 ms hs h.2 env interference
  dsimp only at run
  let mid := writePost ms (BitVec.ofNat 5 r) (s1.pc + upperValue c)
  let src := updPc (s1.pc + 4) (updReg r (s1.pc + upperValue c) s1)
  have first : riscvTarget.next ms = mid := run.1
  have second : riscvTarget.next (env 0 mid) =
      writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c) := run.2.2.1
  have rel : targetStateRel riscvTarget src (env 0 mid) := run.2.1
  have valid := rel.1
  have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.loc r c)).length s1.pc 0 →
      riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    have before := h.2.2.2.1 pc domain
    have after := rel.2.2.1 pc domain
    exact after.trans before.symm
  have pc : riscvTarget.getPc (env 0 mid) ∈
      allPcs (riscvConfig.encode (.loc r c)).length s1.pc riscvConfig.codeAlignment := by
    have address := rel.2.1
    change riscvTarget.getPc (env 0 mid) = s1.pc + 4 at address
    rw [address, allPcs_eq]
    refine ⟨1, ?_, ?_⟩
    · norm_num [riscvConfig, riscvEnc, riscvAst, riscvEncode]
    · rfl
  constructor
  · simpa [asserts, first, second] using ⟨⟨valid, code, pc⟩, run.2.2.2⟩
  · simp only [asserts2]
    rw [first]
    change (∀ x, ¬ s1.memDomain x → ms.MEM8 x = mid.MEM8 x) ∧
      (∀ x, ¬ s1.memDomain x → (env 0 mid).MEM8 x =
        (riscvTarget.next (env 0 mid)).MEM8 x) ∧ True
    rw [second]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof
