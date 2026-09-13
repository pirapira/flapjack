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

The small fixture is deliberately stable and suitable as the seed for a
larger differential/fuzzing corpus. The original probe source is
`pan_sem_e2e_probeScript.sml`, referencing
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

#guard declarations.isSome

theorem compiled_source_executes_to_original_probe :
    machineResult = originalProbeResult := by
  native_decide

def runChecks : IO Bool := do
  if machineResult == originalProbeResult then
    IO.println "PASS source-to-RISC-V execution matches original Pancake HOL probe"
    pure true
  else
    IO.println s!"FAIL source-to-RISC-V execution: {machineResult}"
    pure false

end Flapjack.Test.EndToEndParity
