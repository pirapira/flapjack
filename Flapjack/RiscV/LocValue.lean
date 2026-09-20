import Flapjack.RiscV.Backend
import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! Semantic agreement between the legacy absolute `LocValue` lowering
(`wordLocValueToInstructions`, a single `ADDI`) and the Cake-faithful
position-aware lowering (`wordLocValueToInstructionsCake`, `AUIPC`+`ADDI`).
The legacy shape is only faithful in the non-truncating range, so the
agreement theorem carries the explicit premises `ZeroRegister state`,
`state.pc = 0`, and `label < 2 ^ 11`; source/global/memory/FFI state stays
visible as the `state` argument. -/

theorem execute_addi_read [NeZero width] (state : State width) (destination source : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.addi destination source immediate)) destination =
      if destination = 0 then readRegister state destination
      else readRegister state source + immediate := by
  by_cases h : destination = 0 <;> simp [execute, writeRegister, readRegister, h]

theorem uImmediate_zero [NeZero width] : uImmediate (0 : Word width) = 0 := by
  unfold uImmediate
  ext i
  simp [BitVec.getElem_signExtend]

theorem wordLocValueToInstructions_getD [NeZero width]
    (destination label : Nat) (hd : destination < 32) :
    (wordLocValueToInstructions (width := width) destination label).getD [] =
      [.addi ⟨destination, hd⟩ 0 (BitVec.ofNat width label)] := by
  simp [wordLocValueToInstructions, registerOfNat, hd]

theorem wordLocValueToInstructionsCake_small_eq [NeZero width]
    (destination label : Nat) (hdestination : destination < 32) (hlabel : label < 2 ^ 11) :
    wordLocValueToInstructionsCake (width := width) destination label 0 =
      some [.auipc ⟨destination, hdestination⟩ 0,
            .addi ⟨destination, hdestination⟩ ⟨destination, hdestination⟩
              (BitVec.ofNat width label)] := by
  have hrem : (label : Int) % 4096 = (label : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have hnot : ¬ ((label : Int) ≥ (2048 : Int)) := by omega
  unfold wordLocValueToInstructionsCake
  simp only [registerOfNat, hdestination, dif_pos trivial]
  have hdelta : (Int.ofNat label - Int.ofNat 0 : Int) = (label : Int) := by simp
  rw [hdelta, hrem, if_neg hnot]
  simp

theorem wordLocValueToInstructions_execution [NeZero width]
    (state : State width) (destination label : Nat) (hd : destination < 32)
    (hzero : ZeroRegister state) :
    readRegister (executeInstructions state
        [.addi ⟨destination, hd⟩ 0 (BitVec.ofNat width label)]) ⟨destination, hd⟩ =
      if destination = 0 then readRegister state ⟨destination, hd⟩
      else BitVec.ofNat width label := by
  rw [executeInstructions_single, execute_addi_read]
  simp only [Fin.ext_iff, Fin.val_zero]
  by_cases h : destination = 0
  · simp [h]
  · simp only [h, if_false]
    rw [show readRegister state (0 : Fin 32) = 0 from hzero]
    simp

theorem auipcAddi_execution_of_small [NeZero width]
    (state : State width) (destination label : Nat) (hd : destination < 32)
    (hpc : state.pc = 0) :
    readRegister (executeInstructions state
        [.auipc ⟨destination, hd⟩ 0,
         .addi ⟨destination, hd⟩ ⟨destination, hd⟩ (BitVec.ofNat width label)]) ⟨destination, hd⟩ =
      if destination = 0 then readRegister state ⟨destination, hd⟩
      else BitVec.ofNat width label := by
  simp only [executeInstructions]
  rw [execute_addi_read]
  simp only [Fin.ext_iff, Fin.val_zero]
  by_cases h : destination = 0
  · rw [execute_auipc]; simp [h]
  · rw [if_neg (by simpa using h), if_neg (by simpa using h), execute_auipc]
    simp only [Fin.ext_iff, Fin.val_zero, if_neg (by simpa using h), hpc, uImmediate_zero]
    simp

theorem wordLocValueToInstructions_agrees_cake_of_small [NeZero width]
    (state : State width) (destination label : Nat) (hd : destination < 32)
    (hzero : ZeroRegister state) (hpc : state.pc = 0) (hlabel : label < 2 ^ 11) :
    readRegister (executeInstructions state
        ((wordLocValueToInstructions (width := width) destination label).getD [])) ⟨destination, hd⟩ =
      readRegister (executeInstructions state
        ((wordLocValueToInstructionsCake (width := width) destination label 0).getD [])) ⟨destination, hd⟩ := by
  rw [wordLocValueToInstructions_getD destination label hd,
    wordLocValueToInstructionsCake_small_eq destination label hd hlabel]
  simp only [Option.getD_some]
  rw [wordLocValueToInstructions_execution state destination label hd hzero,
    auipcAddi_execution_of_small state destination label hd hpc]

example :
    readRegister (executeInstructions (zeroState 64)
        ((wordLocValueToInstructions (width := 64) 4 0x234).getD [])) 4 =
      readRegister (executeInstructions (zeroState 64)
        ((wordLocValueToInstructionsCake (width := 64) 4 0x234 0).getD [])) 4 := by
  decide

/-! ## Cake-faithful LocValue execution oracles (bead flapjack-pxn.1.4)

    The checked lowering `wordLocValueToInstructionsCake destination label position`
    mirrors Cake's PC-relative `Loc` encoding: it emits `AUIPC`/`ADDI` for the
    offset `label - position`.  Executing that pair from `pc = position` therefore
    yields `label`.  These `by decide` oracles exercise the out-of-range and
    page-crossing shapes that the legacy one-instruction boundary truncates. -/

theorem locValue_balanced_reconstruction (delta : Int) :
    (let remainder := delta % 4096
     let low := if remainder >= 2048 then remainder - 4096 else remainder
     let upper := (delta - low) / 4096
     low + upper * 4096) = delta := by
  dsimp only
  split <;> omega

example :
    readRegister (executeInstructions (zeroState 64)
        ((wordLocValueToInstructionsCake (width := 64) 4 0x123456 0).getD [])) 4 =
      BitVec.ofNat 64 0x123456 := by decide

example :
    readRegister (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
        ((wordLocValueToInstructionsCake (width := 64) 4 0x800 0x1000).getD [])) 4 =
      BitVec.ofNat 64 0x800 := by decide

example :
    readRegister (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
        ((wordLocValueToInstructionsCake (width := 64) 4 0 0x1000).getD [])) 4 =
      BitVec.ofNat 64 0 := by decide

example :
    readRegister (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 2 }
        ((wordLocValueToInstructionsCake (width := 64) 4 0x1004 2).getD [])) 4 =
      BitVec.ofNat 64 0x1004 := by decide

/-! ### Range boundary of the `AUIPC` immediate (bead flapjack-pxn.1.4)

    The generic execution identity for `wordLocValueToInstructionsCake` needs the
    pc-relative delta to fit the signed 32-bit `AUIPC`+`ADDI` range; equivalently
    the `upper` word must fit signed 20 bits.  Outside that range the `AUIPC`
    immediate sign-wraps, exactly as in Cake's `riscv_ast`.  The first
    out-of-range `upper`, `2 ^ 19`, is a concrete counterexample to the naive
    unconditional identity, while in-range values satisfy it. -/

example :
    uImmediate (BitVec.ofInt 64 (2 ^ 19 : Int)) ≠
      BitVec.ofInt 64 ((2 ^ 19 : Int) * 4096) := by decide

example :
    uImmediate (BitVec.ofInt 64 (1 : Int)) =
      BitVec.ofInt 64 ((1 : Int) * 4096) := by decide

example :
    uImmediate (BitVec.ofInt 64 (-1 : Int)) =
      BitVec.ofInt 64 ((-1 : Int) * 4096) := by decide

/-! ### Execution semantics of the Cake-faithful `LocValue` pair (bead flapjack-pxn.1.4)

    The `AUIPC`+`ADDI` pair materialized by `wordLocValueToInstructionsCake`
    executes to `state.pc + uImmediate upper + low` on the destination register.
    The remaining obligation is the arithmetic reconstruction
    `uImmediate upper + low = label`; it is isolated in
    `wordLocValueToInstructionsCake_execution_of_reconstruction`. -/

theorem execute_auipc_addi_read [NeZero width] (state : State width) (d : Fin 32)
    (hne : d ≠ 0) (upper low : Word width) :
    readRegister (executeInstructions state [.auipc d upper, .addi d d low]) d =
      state.pc + uImmediate upper + low := by
  simp only [executeInstructions]
  rw [execute_addi_read]
  rw [if_neg (by simpa using hne), execute_auipc, if_neg (by simpa using hne)]

theorem wordLocValueToInstructionsCake_getD [NeZero width] (destination label position : Nat)
    (hd : destination < 32) :
    (wordLocValueToInstructionsCake (width := width) destination label position).getD [] =
      [.auipc ⟨destination, hd⟩
        (BitVec.ofInt width
          ((Int.ofNat label - Int.ofNat position -
              (if (Int.ofNat label - Int.ofNat position) % 4096 ≥ 2048
               then (Int.ofNat label - Int.ofNat position) % 4096 - 4096
               else (Int.ofNat label - Int.ofNat position) % 4096)) / 4096)),
       .addi ⟨destination, hd⟩ ⟨destination, hd⟩
        (BitVec.ofInt width
          (if (Int.ofNat label - Int.ofNat position) % 4096 ≥ 2048
           then (Int.ofNat label - Int.ofNat position) % 4096 - 4096
           else (Int.ofNat label - Int.ofNat position) % 4096))] := by
  simp [wordLocValueToInstructionsCake, registerOfNat, hd]

theorem wordLocValueToInstructionsCake_execution_of_reconstruction [NeZero width]
    (state : State width) (destination label position : Nat) (hd : destination < 32)
    (hne : destination ≠ 0)
    (hreconstruct :
      uImmediate (BitVec.ofInt width
          ((Int.ofNat label - Int.ofNat position -
              (if (Int.ofNat label - Int.ofNat position) % 4096 ≥ 2048
               then (Int.ofNat label - Int.ofNat position) % 4096 - 4096
               else (Int.ofNat label - Int.ofNat position) % 4096)) / 4096)) +
        BitVec.ofInt width
          (if (Int.ofNat label - Int.ofNat position) % 4096 ≥ 2048
           then (Int.ofNat label - Int.ofNat position) % 4096 - 4096
           else (Int.ofNat label - Int.ofNat position) % 4096)
        = BitVec.ofNat width label) :
    readRegister (executeInstructions state
        ((wordLocValueToInstructionsCake (width := width) destination label position).getD []))
      ⟨destination, hd⟩ =
        state.pc + BitVec.ofNat width label := by
  rw [wordLocValueToInstructionsCake_getD destination label position hd]
  rw [execute_auipc_addi_read state ⟨destination, hd⟩ (by simpa using hne)]
  rw [BitVec.add_assoc, hreconstruct]

/-! ### Kernel-checked reconstruction for nonnegative (forward) offsets

The reconstruction premise used by `wordLocValueToInstructionsCake_execution_of_reconstruction`
is discharged here for the nonnegative-offset range, i.e. forward references where the
target is at or after the current position. The signed range needs the negative case as
well and remains an explicit obligation. (bead flapjack-pxn.1.4) -/

theorem bmod_ofInt_toNat_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  rw [BitVec.toNat_ofInt]
  have h1 : upper % ((2^64 : Nat) : Int) = upper := Int.emod_eq_of_lt h0 (by omega)
  rw [h1, Int.toNat_of_nonneg h0]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  exact Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2

theorem signExtend_ofNat_ofInt_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    BitVec.signExtend 64 (BitVec.ofNat 20 (BitVec.ofInt 64 upper).toNat) =
      BitVec.ofInt 64 upper := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend]
  change ((OfNat.ofNat ((BitVec.ofInt 64 upper).toNat) : BitVec 20).toInt).bmod
      (2 ^ min 64 20) = (BitVec.ofInt 64 upper).toInt
  rw [BitVec.toInt_ofNat, BitVec.toInt_ofInt, Nat.min_eq_right (by omega : 20 ≤ 64)]
  rw [bmod_ofInt_toNat_nonneg upper h0 hhi]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  rw [Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2]
  have hc1 : -(↑(2^64 : Nat) / 2) ≤ upper := by omega
  have hc2 : upper < (↑(2^64 : Nat) + 1) / 2 := by omega
  exact (Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^64) hc1 hc2).symm

theorem uImmediate_ofInt_range_nonneg (upper : Int) (h0 : 0 ≤ upper) (hhi : upper < 2^19) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  rw [uImmediate, signExtend_ofNat_ofInt_nonneg upper h0 hhi]
  rw [BitVec.shiftLeft_eq, BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rw [show BitVec.twoPow 64 12 = BitVec.ofInt 64 4096 by decide]

/-! ### Kernel-checked reconstruction for the full signed offset range

The negative-offset (backward reference) case of the reconstruction, so the
premise of `wordLocValueToInstructionsCake_execution_of_reconstruction` is
discharged for every signed 20-bit `upper`, i.e. every `delta = label - position`
with `-(2^19) ≤ delta < 2^19`. (bead flapjack-pxn.1.4) -/

theorem bmod_ofInt_toNat_neg (upper : Int) (hlo : -(2^19) ≤ upper) (hneg : upper < 0) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  rw [BitVec.toNat_ofInt]
  have hmod : upper % ((2^64 : Nat) : Int) = upper + ((2^64 : Nat) : Int) := by
    have h2 : upper % ((2^64 : Nat) : Int) =
        (upper + ((2^64 : Nat) : Int)) % ((2^64 : Nat) : Int) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      have hsub : upper - (upper + ((2^64 : Nat) : Int)) = -(((2^64 : Nat) : Int)) := by
        omega
      rw [hsub]; decide
    rw [h2]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  rw [Int.toNat_of_nonneg (by omega : (0:Int) ≤ upper + ((2^64 : Nat) : Int))]
  rw [Int.bmod_eq_emod]
  have hper : (upper + ((2^64 : Nat) : Int)) % ((2^20 : Nat) : Int) =
      upper + ((2^20 : Nat) : Int) := by
    rw [Int.add_emod]
    have hz : ((2^64 : Nat) : Int) % ((2^20 : Nat) : Int) = 0 := by decide
    rw [hz]
    have hu : upper % ((2^20 : Nat) : Int) = upper + ((2^20 : Nat) : Int) := by
      have h2 : upper % ((2^20 : Nat) : Int) =
          (upper + ((2^20 : Nat) : Int)) % ((2^20 : Nat) : Int) := by
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        have hsub : upper - (upper + ((2^20 : Nat) : Int)) = -(((2^20 : Nat) : Int)) := by
          omega
        rw [hsub]; decide
      rw [h2]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hu]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [hper]
  have hc : (((2^20 : Nat) : Int) + 1) / 2 = 524288 := by decide
  rw [if_pos (by rw [hc]; omega :
    (((2^20 : Nat) : Int) + 1) / 2 ≤ upper + ((2^20 : Nat) : Int))]
  omega

theorem bmod_ofInt_toNat_range (upper : Int) (hlo : -(2^19) ≤ upper) (hhi : upper < 2^19) :
    (((BitVec.ofInt 64 upper).toNat : Int)).bmod (2^20) = upper := by
  by_cases h : 0 ≤ upper
  · exact bmod_ofInt_toNat_nonneg upper h hhi
  · exact bmod_ofInt_toNat_neg upper hlo (by omega)

theorem signExtend_ofNat_ofInt_range (upper : Int) (hlo : -(2^19) ≤ upper)
    (hhi : upper < 2^19) :
    BitVec.signExtend 64 (BitVec.ofNat 20 (BitVec.ofInt 64 upper).toNat) =
      BitVec.ofInt 64 upper := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend]
  change ((OfNat.ofNat ((BitVec.ofInt 64 upper).toNat) : BitVec 20).toInt).bmod
      (2 ^ min 64 20) = (BitVec.ofInt 64 upper).toInt
  rw [BitVec.toInt_ofNat, BitVec.toInt_ofInt, Nat.min_eq_right (by omega : 20 ≤ 64)]
  rw [bmod_ofInt_toNat_range upper hlo hhi]
  have hb1 : -(↑(2^20 : Nat) / 2) ≤ upper := by omega
  have hb2 : upper < (↑(2^20 : Nat) + 1) / 2 := by omega
  rw [Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^20) hb1 hb2]
  have hc1 : -(↑(2^64 : Nat) / 2) ≤ upper := by omega
  have hc2 : upper < (↑(2^64 : Nat) + 1) / 2 := by omega
  exact (Int.bmod_eq_of_le (n := upper) (m := (2:Nat)^64) hc1 hc2).symm

theorem uImmediate_ofInt_range (upper : Int) (hlo : -(2^19) ≤ upper) (hhi : upper < 2^19) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  rw [uImmediate, signExtend_ofNat_ofInt_range upper hlo hhi]
  rw [BitVec.shiftLeft_eq, BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rw [show BitVec.twoPow 64 12 = BitVec.ofInt 64 4096 by decide]

/-- Packaged Cake-faithful `LocValue` execution for the non-layout API: with
`position = 0` and a forward label in `[0, 2^19)`, executing the
`wordLocValueToInstructionsCake` pair from any state writes `state.pc + label`
to the destination register. This discharges the reconstruction premise of
`wordLocValueToInstructionsCake_execution_of_reconstruction` for the position-0
case. (bead flapjack-pxn.1.4) -/
theorem wordLocValueToInstructionsCake_execution_zero (state : State 64)
    (destination label : Nat) (hd : destination < 32) (hne : destination ≠ 0)
    (hlabel : (label : Int) < 2^19) :
    readRegister (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) destination label 0).getD []))
      ⟨destination, hd⟩ = state.pc + BitVec.ofNat 64 label := by
  apply wordLocValueToInstructionsCake_execution_of_reconstruction state destination label 0 hd hne
  rw [show (Int.ofNat label - Int.ofNat 0 : Int) = (label : Int) by simp]
  rw [uImmediate_ofInt_range]
  · rw [← BitVec.ofInt_add]
    rw [show ((label : Int) - (if (label : Int) % 4096 ≥ 2048 then (label : Int) % 4096 - 4096 else (label : Int) % 4096)) / 4096 * 4096 +
          (if (label : Int) % 4096 ≥ 2048 then (label : Int) % 4096 - 4096 else (label : Int) % 4096)
        = (label : Int) by
      have hbal := locValue_balanced_reconstruction (label : Int)
      dsimp only at hbal
      omega]
    rw [BitVec.ofInt_natCast]
  · omega
  · omega

/-- The AUIPC immediate reconstruction, phrased for a balanced `low`/`upper`
split of a signed offset `delta` rather than for `uImmediate`'s own expression:
if `low` is in `[-2048, 2048)` and `low + upper * 4096 = delta` with
`|delta| < 2^19`, then `uImmediate (ofInt 64 upper)` is exactly
`ofInt 64 (upper * 4096)`. (bead flapjack-pxn.1.4) -/
theorem uImmediate_ofInt_balanced (delta upper low : Int)
    (hlo : -(2^19) ≤ delta) (hhi : delta < 2^19)
    (hlow_lo : -2048 ≤ low) (hlow_hi : low ≤ 2047)
    (hbal : low + upper * 4096 = delta) :
    uImmediate (BitVec.ofInt 64 upper) = BitVec.ofInt 64 (upper * 4096) := by
  have hupper_lo : -(2^19) ≤ upper := by omega
  have hupper_hi : upper < 2^19 := by omega
  exact uImmediate_ofInt_range upper hupper_lo hupper_hi

/-- The balanced LocValue reconstruction in the `upper * 4096 + low` order,
which is the orientation produced by `BitVec.ofInt_add`. (bead flapjack-pxn.1.4) -/
theorem locValue_balanced_reconstruction_comm (delta : Int) :
    (delta - (if delta % 4096 ≥ 2048 then delta % 4096 - 4096 else delta % 4096)) / 4096 * 4096 +
      (if delta % 4096 ≥ 2048 then delta % 4096 - 4096 else delta % 4096) = delta := by
  have hbal := locValue_balanced_reconstruction delta
  dsimp only at hbal
  omega

/-- Cake-faithful `LocValue` execution at an arbitrary program position: if the
state's `pc` is `position` and the signed offset `label - position` fits the
signed 20-bit AUIPC range, executing the `wordLocValueToInstructionsCake` pair
writes the target `label` to the destination register. This is the PC-relative
`riscv_ast (Loc r i)` semantics (`pc + (target - position)`) for the non-layout
API. (bead flapjack-pxn.1.4) -/
theorem wordLocValueToInstructionsCake_execution_general (state : State 64)
    (destination label position : Nat) (hd : destination < 32) (hne : destination ≠ 0)
    (hpc : state.pc = BitVec.ofNat 64 position)
    (hlo : -(2^19) ≤ (label : Int) - (position : Int))
    (hhi : (label : Int) - (position : Int) < 2^19) :
    readRegister (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) destination label position).getD []))
      ⟨destination, hd⟩ = BitVec.ofNat 64 label := by
  rw [wordLocValueToInstructionsCake_getD destination label position hd]
  simp only [Int.ofNat_eq_natCast]
  rw [execute_auipc_addi_read state ⟨destination, hd⟩ (by simpa using hne)]
  rw [hpc]
  have hbal := locValue_balanced_reconstruction ((label : Int) - (position : Int))
  dsimp only at hbal
  have hlow_lo : -2048 ≤ (if ((label : Int) - (position : Int)) % 4096 ≥ 2048 then ((label : Int) - (position : Int)) % 4096 - 4096 else ((label : Int) - (position : Int)) % 4096) := by split <;> omega
  have hlow_hi : (if ((label : Int) - (position : Int)) % 4096 ≥ 2048 then ((label : Int) - (position : Int)) % 4096 - 4096 else ((label : Int) - (position : Int)) % 4096) ≤ 2047 := by split <;> omega
  rw [uImmediate_ofInt_balanced _ _ _ hlo hhi hlow_lo hlow_hi hbal]
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  rw [locValue_balanced_reconstruction_comm ((label : Int) - (position : Int))]
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  rw [show (position : Int) + ((label : Int) - (position : Int)) = (label : Int) by omega]
  exact BitVec.ofInt_natCast 64 label

/-- Strengthening of `wordLocValueToInstructions_agrees_cake_of_small` to the
full forward `AUIPC` signed range: for a nonzero destination, `state.pc = 0`,
`ZeroRegister state`, and a forward label with `(label : Int) < 2 ^ 19`, the
legacy absolute single-`ADDI` lowering and the Cake-faithful `AUIPC`+`ADDI`
lowering execute to the same destination value.  The `state.pc = 0` premise is
exactly where the legacy absolute model coincides with Cake's PC-relative
`riscv_ast (Loc r i)`. (bead flapjack-pxn.1.4) -/
theorem wordLocValueToInstructions_agrees_cake_of_forward (state : State 64)
    (destination label : Nat) (hd : destination < 32) (hne : destination ≠ 0)
    (hzero : ZeroRegister state) (hpc : state.pc = 0)
    (hlabel : (label : Int) < 2 ^ 19) :
    readRegister (executeInstructions state
        ((wordLocValueToInstructions (width := 64) destination label).getD [])) ⟨destination, hd⟩ =
      readRegister (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) destination label 0).getD [])) ⟨destination, hd⟩ := by
  rw [wordLocValueToInstructions_getD destination label hd]
  rw [wordLocValueToInstructions_execution state destination label hd hzero]
  rw [show (if destination = 0 then readRegister state ⟨destination, hd⟩
        else BitVec.ofNat 64 label) = BitVec.ofNat 64 label from by rw [if_neg hne]]
  exact (wordLocValueToInstructionsCake_execution_general state destination label 0 hd hne hpc
    (by omega) (by simpa using hlabel)).symm

example :
    readRegister (executeInstructions (zeroState 64)
        ((wordLocValueToInstructions (width := 64) 4 0x12345).getD [])) 4 =
      readRegister (executeInstructions (zeroState 64)
        ((wordLocValueToInstructionsCake (width := 64) 4 0x12345 0).getD [])) 4 := by
  decide

end Flapjack.RiscV
