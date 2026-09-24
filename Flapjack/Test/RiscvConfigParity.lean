import Flapjack.Compiler.Backend.LabProps

/-!
# RISC-V assembler configuration parity

Checks the check-relevant `riscvConfig` field values against the direct HOL
oracle `scripts/hol-probes/riscv_config_probe.out` (HOL `riscv_config_def`,
`cakeml/compiler/encoders/riscv/riscv_targetScript.sml:277-304`).  `encode`
is the documented placeholder and is not read by any validity predicate.
-/

namespace Flapjack.Test.RiscvConfigParity

open Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps

private def isaIsRiscv (config : AsmConfig width) : Bool :=
  match config.isa with
  | .riscv => true
  | _ => false

private def linkRegOne (config : AsmConfig width) : Bool :=
  match config.linkReg with
  | some 1 => true
  | _ => false

private def w64 (n : Int) : BitVec 64 := BitVec.ofInt 64 n

/-- All 19 oracle rows of `riscv_config_probe.out`. -/
def riscvConfigGuard : Bool :=
  isaIsRiscv riscvConfig &&
  (riscvConfig.regCount == 32) &&
  (riscvConfig.avoidRegs == [0, 2, 3, 4, 31]) &&
  (riscvConfig.fpRegCount == 0) &&
  linkRegOne riscvConfig &&
  (riscvConfig.twoRegArith == false) &&
  (riscvConfig.bigEndian == false) &&
  (riscvConfig.codeAlignment == 2) &&
  (riscvConfig.addrOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfig.hwOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfig.byteOffset == (riscvMin12, riscvMax12)) &&
  (riscvConfig.jumpOffset == (riscvMin32, riscvJumpMax)) &&
  (riscvConfig.cjumpOffset == (riscvMin21 + 8, riscvMax21 + 4)) &&
  (riscvConfig.locOffset == (riscvMin32, riscvJumpMax)) &&
  (riscvConfig.validImm (.inl .sub) (w64 (-2048)) == false) &&
  (riscvConfig.validImm (.inl .sub) (w64 (-2047)) == true) &&
  (riscvConfig.validImm (.inl .add) (w64 (-2048)) == true) &&
  (riscvConfig.validImm (.inl .add) (w64 2047) == true) &&
  (riscvConfig.validImm (.inl .add) (w64 2048) == false)

#guard riscvConfigGuard

-- The config drives the StackProps instruction checks.
private def riscvChecks := asmChecksOfConfig riscvConfig

#guard riscvChecks.instOk (.skip : WordLangInst (BitVec 64)) == true
#guard riscvChecks.regOk 1 == true
#guard riscvChecks.regOk 0 == false
#guard riscvChecks.regOk 31 == false

def runChecks : IO Bool := do
  if riscvConfigGuard then
    IO.println "PASS riscv_config fields match the HOL oracle"
  else
    IO.println "FAIL riscv_config fields match the HOL oracle"
  pure riscvConfigGuard

end Flapjack.Test.RiscvConfigParity