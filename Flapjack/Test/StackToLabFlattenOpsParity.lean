import Flapjack.Compiler.Backend.LabProps
import Flapjack.Compiler.Encoders.Asm

/-! Parity check for the concrete `flattenOps` instantiation of the
StackToLab `FlattenOps` record over the faithful assembler carriers.

Direct HOL oracle: `scripts/hol-probes/stack_to_lab_flatten_ops_probe.out`
(cakeml/compiler/backend/stack_to_labScript.sml:24-32 `negate_def`, :20-22
`compile_jump_def`). The embedded constructors are config-independent. -/

namespace Flapjack.Test.StackToLabFlattenOpsParity

open Flapjack
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def ops : FlattenOps (WordLangInst W) Flapjack.Cmp (Flapjack.WordRegImm W)
    (AsmData 8) := flattenOps

example : ops.skip = .inst .skip := rfl
example : ops.embedInst (.const 1 (BitVec.ofNat 8 0)) = .inst (.const 1 (BitVec.ofNat 8 0)) := rfl
example : ops.jumpReg 3 = .jumpReg 3 := rfl
example : ops.reg 3 = .reg 3 := rfl
example : ops.lower = Flapjack.Cmp.lower := rfl

-- HOL negate table (stack_to_labScript.sml:24-32)
example : ops.negate .less = .notLess := rfl
example : ops.negate .equal = .notEqual := rfl
example : ops.negate .lower = .notLower := rfl
example : ops.negate .test = .notTest := rfl
example : ops.negate .notLess = .less := rfl
example : ops.negate .notEqual = .equal := rfl
example : ops.negate .notLower = .lower := rfl
example : ops.negate .notTest = .test := rfl

def runChecks : IO Bool := do
  IO.println "PASS stack_to_lab flattenOps embedded constructors and negate table match HOL"
  pure true

end Flapjack.Test.StackToLabFlattenOpsParity
