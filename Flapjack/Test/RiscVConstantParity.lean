import Flapjack.RiscV.Backend
import Flapjack.RiscV.Encoding
import Flapjack.RiscV.Lab

/-! Direct CakeML `riscv_ast (Inst (Const ...))` oracle checks.

`wordExpToInstruction` remains the theorem-facing one-instruction API.  These
checks cover the separate constants boundary, whose list shape follows
`riscv_targetScript.sml` (`riscv_ast_def` and `riscv_const32_def`). -/

namespace Flapjack.RiscV

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12) =
      some [.ori 4 0 (BitVec.ofNat 64 0x12)] := by
  decide

/-! Signed-12 endpoints from Cake's `valid_imm`/`riscv_ast` boundary. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2047) =
      some [.ori 4 0 (BitVec.ofNat 64 0x7ff)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 (2 ^ 64 - 2048)) =
      some [.ori 4 0 (BitVec.ofNat 64 0x800)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x12345678) =
      some [.lui 4 (BitVec.ofNat 64 0x12345),
        .addi 4 4 (BitVec.ofNat 64 0x678)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) =
      some [.lui 31 (BitVec.ofNat 64 0x55667),
        .addi 31 31 (BitVec.ofNat 64 0x788),
        .lui 4 (BitVec.ofNat 64 0x11223),
        .addi 4 4 (BitVec.ofNat 64 0x344),
        .slli 4 4 (BitVec.ofNat 64 32),
        .or 4 4 31] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 (2 ^ 64 - 8)) =
      some [.ori 4 0 (BitVec.ofNat 64 0xff8)] := by
  decide

example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 2048) =
      some [.lui 4 (BitVec.ofNat 64 0xfffff),
        .xori 4 4 (BitVec.ofNat 64 0x800)] := by
  decide

/-! Executable obligations for the Cake-faithful multi-instruction boundary.

These deliberately exercise the emitted instruction list, rather than the
legacy one-instruction expression API. -/
theorem cakeConst1234_execution_oracle :
    (wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1234) := by
  decide

theorem cakeConstWide_execution_oracle :
    (wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788)).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1122334455667788) := by
  decide

/-! The expression-facing Cake boundary preserves the same executable
    obligations while leaving the historical one-instruction selector intact.
    These are theorem-facing API checks, not production-caller migration. -/
theorem cakeExp1234_execution_oracle :
    (wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1234))).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1234) := by
  decide

theorem cakeExpWide_execution_oracle :
    (wordExpToInstructionsCake (width := 64) 4
        (.const (BitVec.ofNat 64 0x1122334455667788))).map
        (fun instructions =>
          readRegister (executeInstructions (zeroState 64) instructions) 4) =
      some (BitVec.ofNat 64 0x1122334455667788) := by
  decide

/-! `wordExpToInstruction` is not Cake-faithful for constants outside the
signed 12-bit immediate range: it returns a single `addi` whose immediate the
encoder silently truncates, while `wordConstToInstructions` emits the
`lui`/`addi` (or wider) sequence of `riscv_targetScript.sml:96`.  The witness
below records the information loss so callers that need the Cake shape use the
`wordConstToInstructions` boundary. -/

example :
    wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234)) =
      some (.addi 4 0 (BitVec.ofNat 64 0x1234)) := by
  decide

example :
    encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x1234)) =
      encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234)) := by
  decide

example :
    (wordExpToInstruction (width := 64) 4 (.const (BitVec.ofNat 64 0x1234))).map
        (fun instruction => encodeInstruction instruction) =
      some (encodeInstruction (.addi 4 0 (BitVec.ofNat 64 0x234))) := by
  decide

/-! ## Bridge to the executable Lab lowering

`labConst32` is the port of Cake's `riscv_const32`
(`riscv_targetScript.sml:77`) and `labConstInstructions` is the port of the
`Const` clause of `riscv_ast_def` (`riscv_targetScript.sml:96`).  The
`wordConst*` definitions are the option-valued, checked theorem boundary.  The
theorems below show that the two boundaries emit exactly the same instruction
lists, so correctness statements about `wordConstToInstructions` transfer to
the executable pipeline. -/

theorem wordConst32ToInstructions_eq_labConst32 {width : Nat} [NeZero width] :
    (wordConst32ToInstructions (width := width)) =
      (labConst32 (width := width)) := by
  rfl

private theorem some_ite {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (some (if c then a else b) : Option α) = if c then some a else some b := by
  split <;> rfl

theorem wordConstToInstructions_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordConstToInstructions (width := width) destination value =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) := by
  unfold wordConstToInstructions labConstInstructions
  simp only [registerOfNat, hdestination]
  rw [wordConst32ToInstructions_eq_labConst32]
  have hmod : value.toNat % 2 ^ width = value.toNat :=
    Nat.mod_eq_of_lt value.isLt
  by_cases hsmall : value.toNat < 2 ^ 11
  · have hlow : value.toNat % 2 ^ 12 = value.toNat :=
      Nat.mod_eq_of_lt (by omega)
    simp [hsmall, hlow]
  · simp only [hsmall, if_false, hmod]
    by_cases hfit :
        (value.toNat ==
          (if value.toNat % 2 ^ 12 / 2 ^ 11 % 2 = 0 then value.toNat % 2 ^ 12
            else (2 ^ width - (2 ^ 12 - value.toNat % 2 ^ 12)) % 2 ^ width)) =
          true
    · simp [hfit]
    · simp only [hfit]
      simp only [some_ite]
      simp

/-- The expression-facing Cake boundary selects the checked constant lowering
for `.const`, so it agrees with the executable Lab materialization while the
legacy one-instruction selector stays unchanged. -/
theorem wordExpToInstructionsCake_const_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordExpToInstructionsCake (width := width) destination (.const value) =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) :=
  wordConstToInstructions_eq_labConstInstructions destination value hdestination

/-! The instruction-facing Cake boundary selects the same checked constant
    lowering as the expression-facing boundary. -/
theorem wordInstToInstructionsCake_const_eq_labConstInstructions {width : Nat}
    [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordInstToInstructionsCake (width := width) (.const destination value) =
      some (labConstInstructions (width := width) ⟨destination, hdestination⟩ 0 31
        value.toNat) :=
  by simpa [wordInstToInstructionsCake_const] using
    (wordConstToInstructions_eq_labConstInstructions destination value hdestination)

/-! The function-level checked boundary composes the same Cake constant list
    with its return carrier.  This is the reusable migration theorem for
    callers that currently depend on the legacy one-instruction selector. -/
theorem wordFunctionToRiscVCake_const_assign_return_eq_labConstInstructions
    {width : Nat} [NeZero width] (destination : Nat) (value : Word width)
    (hdestination : destination < 32) :
    wordFunctionToRiscVCake (width := width)
        (.seq (.assign destination (.const value))
          (.return 0 [destination])) =
      some
        (labConstInstructions (width := width) ⟨destination, hdestination⟩
            0 31 value.toNat,
          [⟨destination, hdestination⟩]) := by
  simp [wordFunctionToRiscVCake, wordExpToInstructionsCake,
    registerOfNat, hdestination,
    wordConstToInstructions_eq_labConstInstructions destination value
      hdestination]

/-- The 0x1234 materialization oracle through the expression-facing Cake
boundary, stated directly against the executable Lab lowering. -/
example :
    wordExpToInstructionsCake (width := 64) 4 (.const (BitVec.ofNat 64 0x1234)) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

example :
    wordInstToInstructionsCake (width := 64)
        (.const 4 (BitVec.ofNat 64 0x1234)) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

/-! A constant used as a load address must retain the complete Cake
materialization before the load; this is the recursive expression boundary,
not the legacy one-instruction selector. -/
example :
    wordExpToInstructionsCake (width := 64) 1
        (.load (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 31 (BitVec.ofNat 64 1),
        .addi 31 31 (BitVec.ofNat 64 0x234),
        .loadWord 1 31] := by
  decide

/-- The 0x1234 materialization oracle, stated directly against the executable
Lab lowering rather than only against `wordConstToInstructions`. -/
example :
    wordConstToInstructions (width := 64) 4 (BitVec.ofNat 64 0x1234) =
      some (labConstInstructions (width := 64) 4 0 31 0x1234) := by
  decide

/-- The wide-constant materialization oracle against the executable Lab
lowering. -/
example :
    wordConstToInstructions (width := 64) 4
        (BitVec.ofNat 64 0x1122334455667788) =
      some (labConstInstructions (width := 64) 4 0 31 0x1122334455667788) := by
  decide

/-! ## LocValue boundary witness (bead flapjack-pxn.1.4)

The standalone Word selector materializes a location label with a single `addi`
(`Flapjack/RiscV/Backend.lean:210`), while Cake's `riscv_ast (Loc r i)`
(`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:265`) always emits
`auipc`/`addi`.  For labels outside the signed 12-bit range the single `addi`
immediate is silently truncated by the encoder.  The executable Lab selector
uses `labLocValueInstructions` (`Flapjack/RiscV/Lab.lean:194`), so production
output is unaffected; these checks record the unfaithful theorem boundary. -/

example :
    wordLocValueToInstructions (width := 64) 4 0x1234 =
      some [.addi 4 0 (BitVec.ofNat 64 0x1234)] := by
  decide

example :
    (wordLocValueToInstructions (width := 64) 4 0x1234).map List.length =
      some 1 := by
  decide

example :
    (labLocValueInstructions (width := 64) 4 0x1234 0).length = 2 := by
  decide

/-! ### Checked Cake-faithful LocValue boundary (bead flapjack-pxn.1.4)

`wordLocValueToInstructionsCake` is the position-aware `AUIPC`/`ADDI` boundary
that mirrors Cake's `riscv_ast (Loc r i)`.  The bridge below proves it emits
exactly the instructions of the executable Lab selector, so a theorem client
can use the checked boundary while the pipeline keeps using `labLocValueInstructions`. -/

theorem wordLocValueToInstructionsCake_eq_labLocValueInstructions {width : Nat}
    [NeZero width] (destination label position : Nat) (hdestination : destination < 32) :
    wordLocValueToInstructionsCake (width := width) destination label position =
      some (labLocValueInstructions (width := width) ⟨destination, hdestination⟩
        label position) := by
  unfold wordLocValueToInstructionsCake labLocValueInstructions
  simp [registerOfNat, hdestination]

example :
    wordLocValueToInstructionsCake (width := 64) 4 0x1234 0 =
      some (labLocValueInstructions (width := 64) 4 0x1234 0) := by
  decide

example :
    (wordLocValueToInstructionsCake (width := 64) 4 0x1234 0).map List.length =
      some 2 := by
  decide

example :
    wordLocValueToInstructionsCake (width := 64) 4 0x123456 0x1000 =
      some (labLocValueInstructions (width := 64) 4 0x123456 0x1000) := by
  decide

/-- Executing the checked Cake-faithful `LocValue` boundary materializes the
label value, mirroring the constant execution oracles: the `auipc`/`addi`
pair computes `label - position` relative to the current program counter. -/
example :
    readRegister
        (executeInstructions (zeroState 64)
          (labLocValueInstructions (width := 64) 4 0x1234 0)) 4 =
      some (BitVec.ofNat 64 0x1234) := by
  decide

example :
    wordProgToRiscVCake (width := 64)
        (.assign 4 (.const (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordProgToRiscVCake (width := 64)
        (.inst (.const 4 (BitVec.ofNat 64 0x1234))) =
      some [.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)] := by
  simp [wordProgToRiscVCake, wordInstToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

example :
    wordFunctionToRiscVCake (width := 64)
        (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
          (.return 0 [4])) =
      some ([.lui 4 (BitVec.ofNat 64 1),
        .addi 4 4 (BitVec.ofNat 64 0x234)], [4]) := by
  simp [wordFunctionToRiscVCake,
    wordExpToInstructionsCake, wordConstToInstructions,
    wordConst32ToInstructions, registerOfNat]

def cakeConstFunctionExecution : Option (List (Word 64)) :=
  (wordFunctionToRiscVCake (width := 64)
    (.seq (.assign 4 (.const (BitVec.ofNat 64 0x1234)))
      (.return 0 [4]))).map fun (code, returns) =>
    returns.map (readRegister (executeInstructions (zeroState 64) code))

#guard cakeConstFunctionExecution = some [BitVec.ofNat 64 0x1234]

/-! Focused regressions for the same checked boundary across the offset shapes
that the `auipc`/`addi` split must handle: an aligned upward delta, an aligned
downward page crossing, a negative delta whose signed 12-bit remainder forces a
carry, a wide label spread over many pages, and an unaligned program counter.
The `auipc`/`addi` pair computes `label - position + position`. -/
example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0 }
          (labLocValueInstructions (width := 64) 4 0x2000 0)) 4 =
      BitVec.ofNat 64 0x2000 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0 0x1000)) 4 =
      BitVec.ofNat 64 0 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x800 0x1000)) 4 =
      BitVec.ofNat 64 0x800 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 0x1000 }
          (labLocValueInstructions (width := 64) 4 0x123456 0x1000)) 4 =
      BitVec.ofNat 64 0x123456 := by
  decide

example :
    readRegister
        (executeInstructions { (zeroState 64) with pc := BitVec.ofNat 64 2 }
          (labLocValueInstructions (width := 64) 4 0x1004 2)) 4 =
      BitVec.ofNat 64 0x1004 := by
  decide

end Flapjack.RiscV
