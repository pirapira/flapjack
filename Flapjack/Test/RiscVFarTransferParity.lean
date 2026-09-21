import Flapjack.RiscV.Lab

/-!
# Far-jump and far-branch lowering against `riscv_ast`

CakeML's RISC-V encoder falls back when a PC-relative operand leaves the
architectural range (`riscv_targetScript.sml:170-263`):

* `Jump a` / `Call a` emit `JAL` while `min21 <= a <= max21` (that is,
  `-2^20 <= a <= 2^20 - 1`) and otherwise `AUIPC temp, hi; JALR _, temp, lo`.
* `JumpCmp c r ri a` emits a single branch while `-0xFFC <= a <= 0xFFF` and
  otherwise inverts the branch over a `JAL`.
* `lab_inst` (`lab_to_targetScript.sml:20-28`) reduces `Halt`, `Install` and
  `CallFFI` to `Jump w`, so all three take the `Jump` fallback, and
  `line_ok_light` checks them with `asm_ok (Jump w)`.

Two properties are pinned here.  First, the `JumpCmp` range is measured
against `a` -- the offset of the whole line, including the `ORI`/`ANDI`/`AND`
that materialises the operand -- not against the branch instruction that
follows that prelude.  Second, `CallFFI` and `Install` get the `Jump`
fallback rather than a bare, silently wrapping `JAL`.
-/

namespace Flapjack.RiscV

private def ctx : WordFfiContext := { services := [("write", 7)] }

/-! ## `JumpCmp`: the short/far boundary is measured from the line start

With an immediate operand the line is `ORI` then the branch, so the branch
sits 4 bytes past the line.  Cake switches to the inverted-branch-over-`JAL`
form at `a = 4096` and keeps the short form down to `a = -4092`; measuring at
the branch instead moves both boundaries by one instruction. -/

private def jumpCmpAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .equal 5 (.imm 3) ⟨0, 7⟩)

/- Cake keeps the immediate `Test`/`NotTest` path on `ANDI`, including the
   zero immediate; this is distinct from the register-RHS `AND` form. -/
private def jumpCmpTestZeroAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .test 5 (.imm 0) ⟨0, 7⟩)

#guard jumpCmpTestZeroAt 4092 ==
  some [.andi 31 5 (BitVec.ofNat 64 0),
    .branchNe 31 0 (BitVec.ofNat 64 4088)]

#guard jumpCmpTestZeroAt 4096 ==
  some [.andi 31 5 (BitVec.ofNat 64 0), .branchEq 31 0 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

private def jumpCmpNotTestZeroAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .notTest 5 (.imm 0) ⟨0, 7⟩)

#guard jumpCmpNotTestZeroAt 4092 ==
  some [.andi 31 5 (BitVec.ofNat 64 0),
    .branchEq 31 0 (BitVec.ofNat 64 4088)]

#guard jumpCmpNotTestZeroAt 4096 ==
  some [.andi 31 5 (BitVec.ofNat 64 0), .branchNe 31 0 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

/- The same Cake `ANDI` lowering applies to a nonzero immediate.  Pin both
   target-specific Test branches so the zero-immediate special case cannot
   mask a divergence in the ordinary immediate path. -/
private def jumpCmpTestImmAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .test 5 (.imm 3) ⟨0, 7⟩)

#guard jumpCmpTestImmAt 4092 ==
  some [.andi 31 5 (BitVec.ofNat 64 3),
    .branchNe 31 0 (BitVec.ofNat 64 4088)]

#guard jumpCmpTestImmAt 4096 ==
  some [.andi 31 5 (BitVec.ofNat 64 3), .branchEq 31 0 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

private def jumpCmpNotTestImmAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .notTest 5 (.imm 3) ⟨0, 7⟩)

#guard jumpCmpNotTestImmAt 4092 ==
  some [.andi 31 5 (BitVec.ofNat 64 3),
    .branchEq 31 0 (BitVec.ofNat 64 4088)]

#guard jumpCmpNotTestImmAt 4096 ==
  some [.andi 31 5 (BitVec.ofNat 64 3), .branchNe 31 0 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

/-! `a = 4092`: the largest offset Cake still encodes short.  `off12` is
    `a - 4`, the distance from the branch. -/
#guard jumpCmpAt 4092 ==
  some [.ori 31 0 (BitVec.ofNat 64 3), .branchNe 5 31 (BitVec.ofNat 64 4088)]

/-! `a = 4096`: one instruction past the limit, so Cake inverts the branch
    over a `JAL` whose offset is `a - 8`. -/
#guard jumpCmpAt 4096 ==
  some [.ori 31 0 (BitVec.ofNat 64 3), .branchEq 5 31 (BitVec.ofNat 64 8),
    .jal 0 (BitVec.ofNat 64 4088)]

/-! `a = -4092` is `-0xFFC`, which Cake still encodes short. -/
#guard jumpCmpAt (-4092) ==
  some [.ori 31 0 (BitVec.ofNat 64 3),
    .branchNe 5 31 (0 - BitVec.ofNat 64 4096)]

/-! `a = -4096` is past it. -/
#guard jumpCmpAt (-4096) ==
  some [.ori 31 0 (BitVec.ofNat 64 3), .branchEq 5 31 (BitVec.ofNat 64 8),
    .jal 0 (0 - BitVec.ofNat 64 4104)]

/-- A register operand has no prelude, so line and branch coincide and the
    boundary is `a = 4096` measured from either. -/
private def jumpCmpRegAt (a : Int) : Option (List (Instruction 64)) :=
  let position : Nat := 100000
  labCompileAsm (width := 64) ctx 0 [(7, (Int.ofNat position + a).toNat)] position
    (.jumpCmp .equal 5 (.reg 6) ⟨0, 7⟩)

#guard jumpCmpRegAt 4092 == some [.branchNe 5 6 (BitVec.ofNat 64 4092)]
#guard jumpCmpRegAt 4096 ==
  some [.branchEq 5 6 (BitVec.ofNat 64 8), .jal 0 (BitVec.ofNat 64 4092)]

/-! ## `CallFFI` and `Install` take the `Jump` fallback

The exported stub for service 0 sits `(3 + 0) * 16 = 48` bytes behind
`cake_main`, so a call at `position` jumps back `position + 48`.  `Install`
jumps back `position + 32`.  `min21` is inclusive, so a distance of exactly
`2^20` is still a direct `JAL`. -/

#guard labCompileAsm (width := 64) ctx 0 [] (2 ^ 20 - 48) (.callFfi "write") ==
  some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))]

/-! Four bytes further and the offset no longer fits, so Cake's `Jump`
    fallback applies: `AUIPC x31, -256` then `JALR x0, x31, -4` reaches
    `pc - 1048580`. -/
#guard labCompileAsm (width := 64) ctx 0 [] (2 ^ 20 - 44) (.callFfi "write") ==
  some [.auipc 31 (BitVec.ofInt 64 (-256)), .jalr 0 31 (BitVec.ofInt 64 (-4))]

#guard labCompileAsm (width := 64) ctx 0 [] (2 ^ 20 - 32) .install ==
  some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))]

#guard labCompileAsm (width := 64) ctx 0 [] (2 ^ 20 - 28) .install ==
  some [.auipc 31 (BitVec.ofInt 64 (-256)), .jalr 0 31 (BitVec.ofInt 64 (-4))]

/-! The linked-FFI entrypoint resolves the service to an absolute target rather
    than using the exported-stub distance.  It must nevertheless share the
    same inclusive `Jump` boundary and AUIPC/JALR fallback. -/
#guard labCompileAsmProgramWithLinkedFfiBase (width := 64) ctx (labLabelIndexOf [])
    (2 ^ 20) 0
    (.callFfi "write") ==
  some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))]

#guard labCompileAsmProgramWithLinkedFfiBase (width := 64) ctx (labLabelIndexOf [])
    (2 ^ 20 + 4) 0
    (.callFfi "write") ==
  some [.auipc 31 (BitVec.ofInt 64 (-256)), .jalr 0 31 (BitVec.ofInt 64 (-4))]

/-! The linked-image wrappers with an FFI base and halt PC delegate to the
    same Cake transfer rules; pin their direct and fallback boundaries too. -/
#guard labCompileAsmProgramWithFfiBaseAndHalt (width := 64) ctx
    (labLabelIndexOf []) (2 ^ 20 - 48) 0 0 (.callFfi "write") ==
  some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))]

#guard labCompileAsmProgramWithLinkedFfiBaseAndHalt (width := 64) ctx
    (labLabelIndexOf []) (2 ^ 20 + 4) 0 0 (.callFfi "write") ==
  some [.auipc 31 (BitVec.ofInt 64 (-256)), .jalr 0 31 (BitVec.ofInt 64 (-4))]

/-! The plain `Jump` boundary is unchanged and shares `min21`. -/
#guard labJumpInstructions (width := 64) 0 0 (2 ^ 20) ==
  some [.jal 0 (0 - BitVec.ofNat 64 (2 ^ 20))]
#guard labJumpInstructions (width := 64) 0 0 (2 ^ 20 + 4) ==
  some [.auipc 31 (BitVec.ofInt 64 (-256)), .jalr 0 31 (BitVec.ofInt 64 (-4))]

end Flapjack.RiscV
