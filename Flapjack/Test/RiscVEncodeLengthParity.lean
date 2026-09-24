import Flapjack.RiscV.CorrectnessEncoding

/-! Direct HOL examples for local `length_riscv_encode` are recorded in
    `scripts/hol-probes/riscv_encode_length_probe.out`.  This Lean guard covers
    represented RV64 integer, branch, and load instructions.  It does not
    identify Lean's narrower `Instruction` datatype with HOL's full
    `riscv$instruction` domain. -/

namespace Flapjack.Test.RiscVEncodeLengthParity

open Flapjack.RiscV

def addi : Instruction 64 := .addi 0 0 0
def add : Instruction 64 := .add 1 2 3
def branch : Instruction 64 := .branchEq 1 2 4
def load : Instruction 64 := .loadWordOffset 1 2 0

def parityGuard : Bool :=
  decide ((encodeInstructionBytes addi).length = 4) &&
    decide ((encodeInstructionBytes add).length = 4) &&
    decide ((encodeInstructionBytes branch).length = 4) &&
    decide ((encodeInstructionBytes load).length = 4)

#guard parityGuard

/-! The matching direct HOL EVAL row `riscv_encode_bytes_addi` checks the
    production encoder's little-endian word-to-byte decomposition. -/
example :
    encodeInstructionBytes
      (.addi 5 3 (BitVec.ofNat 64 2047) : Instruction 64) =
      [0x93, 0x82, 0xf1, 0x7f] := by
  decide

example :
    encodeWordBytes (encodeInstruction (.addi 5 3 (BitVec.ofNat 64 2047) :
      Instruction 64)) =
      [0x93, 0x82, 0xf1, 0x7f] := by
  decide

/-! `riscv_encode_bytes_add` is the matching HOL observation for this R-type
    ADD input. -/
example :
    encodeInstructionBytes (.add 5 3 7 : Instruction 64) =
      [0xb3, 0x82, 0x71, 0x00] := by
  decide

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("RISC-V ADDI encoding has four bytes", decide ((encodeInstructionBytes addi).length = 4)),
      ("RISC-V ADD encoding has four bytes", decide ((encodeInstructionBytes add).length = 4)),
      ("RISC-V branch encoding has four bytes", decide ((encodeInstructionBytes branch).length = 4)),
      ("RISC-V load encoding has four bytes", decide ((encodeInstructionBytes load).length = 4)),
      ("RISC-V ADDI emits HOL-matched little-endian bytes",
        decide (encodeInstructionBytes
          (.addi 5 3 (BitVec.ofNat 64 2047) : Instruction 64) =
            [0x93, 0x82, 0xf1, 0x7f])),
      ("RISC-V ADD emits HOL-matched little-endian bytes",
        decide (encodeInstructionBytes (.add 5 3 7 : Instruction 64) =
          [0xb3, 0x82, 0x71, 0x00])) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVEncodeLengthParity
