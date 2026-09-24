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

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("RISC-V ADDI encoding has four bytes", decide ((encodeInstructionBytes addi).length = 4)),
      ("RISC-V ADD encoding has four bytes", decide ((encodeInstructionBytes add).length = 4)),
      ("RISC-V branch encoding has four bytes", decide ((encodeInstructionBytes branch).length = 4)),
      ("RISC-V load encoding has four bytes", decide ((encodeInstructionBytes load).length = 4)) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVEncodeLengthParity
