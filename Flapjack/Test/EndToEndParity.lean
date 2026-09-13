import Flapjack.Test.ParsedFullSsaPipeline

/-!
# Source-to-RISC-V execution parity

This fixture intentionally compares two different boundaries. The Lean side
parses Pancake source, lowers it through the full-SSA RISC-V pipeline, links
the sections, and executes the resulting image. The expected result comes
from the checked-in HOL probe
`scripts/hol-probes/pan_sem_e2e_probe.out`, which evaluates the original
Pancake `panSem` `Return` equation. This is stronger evidence than a
compiler-correctness theorem alone: a different compiler can satisfy the same
source theorem while still disagreeing with the original Pancake compiler.

The two small fixtures are deliberately stable and suitable as seeds for a
larger differential/fuzzing corpus. Their original probe sources reference
`cakeml/pancake/semantics/panSemScript.sml:638-643`.
-/

namespace Flapjack.Test.EndToEndParity

open Flapjack Flapjack.RiscV

def source : String :=
  "fun 1 main() { return 41; }"

def declarations : Option (List (Decl (RiscV.Word 64))) :=
  (Parser.parseTopDecs (BitVec.ofInt 64) source).toOption

def linked : Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  declarations.bind (fun declarations =>
    compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      parsedCallPipelineRemoveConfig "main" declarations)

def machineResult : Option (List (RiscV.Word 64)) := do
  let sections ← linked
  let entry ← parsedCallLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 6 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 6)

/-! This value is transcribed from the original HOL probe output. It is not a
    second evaluator: the probe is the source of the expected observation. -/
def originalProbeResult : Option (List (RiscV.Word 64)) :=
  some [BitVec.ofNat 64 41]

def addSource : String :=
  "fun 1 main() { return 6 + 7; }"

def addDeclarations : Option (List (Decl (RiscV.Word 64))) :=
  (Parser.parseTopDecs (BitVec.ofInt 64) addSource).toOption

def addLinked : Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  addDeclarations.bind (fun declarations =>
    compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      parsedCallPipelineRemoveConfig "main" declarations)

def addMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← addLinked
  let entry ← parsedCallLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 6 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 6)

def originalAddProbeResult : Option (List (RiscV.Word 64)) :=
  some [BitVec.ofNat 64 13]

#guard declarations.isSome

#guard machineResult == originalProbeResult
#guard addDeclarations.isSome
#guard addMachineResult == originalAddProbeResult

/-! The second fixture exercises expression lowering and machine execution;
    its expected value is `return_mul_42` in the same original HOL probe. -/
def multiplicationSource : String :=
  "fun 1 main() { return 6 * 7; }"

def multiplicationDeclarations : Option (List (Decl (RiscV.Word 64))) :=
  (Parser.parseTopDecs (BitVec.ofInt 64) multiplicationSource).toOption

def multiplicationLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  multiplicationDeclarations.bind (fun declarations =>
    compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      parsedCallPipelineRemoveConfig "main" declarations)

def multiplicationMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← multiplicationLinked
  let entry ← parsedCallLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 6 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 6)

def multiplicationOriginalProbeResult : Option (List (RiscV.Word 64)) :=
  some [BitVec.ofNat 64 42]

#guard multiplicationDeclarations.isSome
#guard multiplicationMachineResult == multiplicationOriginalProbeResult

/-! The conditional fixture exercises source branch selection and linked
    machine execution; its expected value is `return_if_13` in the original
    panSem probe. -/
def controlSource : String :=
  "fun 1 main() { if (1) { return 13; } else { return 99; } }"

def controlDeclarations : Option (List (Decl (RiscV.Word 64))) :=
  (Parser.parseTopDecs (BitVec.ofInt 64) controlSource).toOption

def controlLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  controlDeclarations.bind (fun declarations =>
    compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      parsedCallPipelineRemoveConfig "main" declarations)

def controlMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← controlLinked
  let entry ← parsedCallLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 6 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 6)

def controlOriginalProbeResult : Option (List (RiscV.Word 64)) :=
  some [BitVec.ofNat 64 13]

#guard controlDeclarations.isSome
#guard controlMachineResult == controlOriginalProbeResult

def runChecks : IO Bool := do
  let returnPass := machineResult == originalProbeResult
  let addPass := addMachineResult == originalAddProbeResult
  let multiplicationPass :=
    multiplicationMachineResult == multiplicationOriginalProbeResult
  let controlPass := controlMachineResult == controlOriginalProbeResult
  if returnPass then
    IO.println "PASS return source-to-RISC-V execution matches original Pancake HOL probe"
  else
    IO.println s!"FAIL return source-to-RISC-V execution: {machineResult}"
  if addPass then
    IO.println "PASS add source-to-RISC-V execution matches original Pancake HOL probe"
  else
    IO.println s!"FAIL add source-to-RISC-V execution: {addMachineResult}"
  if multiplicationPass then
    IO.println "PASS Pancake multiplication source executes to original HOL result"
  else
    IO.println s!"FAIL Pancake multiplication execution: {multiplicationMachineResult}"
  if controlPass then
    IO.println "PASS Pancake conditional source executes to original HOL result"
  else
    IO.println s!"FAIL Pancake conditional execution: {controlMachineResult}"
  pure (returnPass && addPass && multiplicationPass && controlPass)

end Flapjack.Test.EndToEndParity
