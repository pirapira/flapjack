import Flapjack.RiscV.Backend

/-!
# RISC-V constant lowering parity

These instruction shapes are the executable port of CakeML's
`riscv_const32`/`riscv_ast (Inst (Const ...))` equations in
`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:89-117`.
-/

namespace Flapjack.Test.RiscVConstantParity

open Flapjack.RiscV

def rv64 (value : Nat) : Word 64 := BitVec.ofNat 64 value


example :
    wordExpToInstructions (width := 64) 1 (.const (rv64 7)) =
      some [.ori 1 0 (rv64 7)] := by
  decide

example :
    wordExpToInstructions (width := 64) 1 (.const (rv64 0x12345678)) =
      some [.lui 1 (BitVec.ofNat 64 0x12345),
        .addi 1 1 (BitVec.ofNat 64 0x678)] := by
  decide

example :
    wordExpToInstructions (width := 64) 1 (.const (rv64 0xffffffff12345678)) =
      some [.lui 31 (BitVec.ofNat 64 0x12345),
        .addi 31 31 (BitVec.ofNat 64 0x678),
        .lui 1 (BitVec.ofNat 64 0),
        .xori 1 1 (BitVec.signExtend 64 (BitVec.ofNat 12 0xfff)),
        .slli 1 1 (rv64 32), .or 1 1 31] := by
  decide

example :
    wordExpToInstructions (width := 64) 1 (.const (rv64 0x0000000080000000)) =
      some [.lui 31 (BitVec.ofNat 64 0x80000),
        .addi 31 31 (BitVec.signExtend 64 (BitVec.ofNat 12 0)),
        .lui 1 (BitVec.ofNat 64 0),
        .xori 1 1 (BitVec.signExtend 64 (BitVec.ofNat 12 0xfff)),
        .slli 1 1 (rv64 32), .xor 1 1 31] := by
  decide

end Flapjack.Test.RiscVConstantParity
