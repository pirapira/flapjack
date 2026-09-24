import Flapjack.Compiler.Backend.LabProps

namespace Flapjack.Test.StackToLabFlattenBaseParity

open Flapjack
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private abbrev P :=
  Flapjack.Compiler.Backend.StackLang.Prog (WordLangInst W) Flapjack.Cmp (WordRegImm W) Flapjack.BinOp Flapjack.WordMemOp
    (WordLangAddr W) String

/-- HOL `flatten T Tick 0 0 [] [] = (List [Asm (Asmi (Inst Skip)) [] 0],F,0)`. -/
example : flatten (flattenOps (width := 8)) (0 : W) true (.tick : P) 0 0 [] [] =
    ([.asm (.asmi (.inst .skip)) [] 0], false, 0) := by
  simp [flatten, flattenOps]

/-- HOL `flatten T (Inst Skip) 0 0 [] [] = (List [Asm (Asmi (Inst Skip)) [] 0],F,0)`. -/
example : flatten (flattenOps (width := 8)) (0 : W) true (.inst .skip : P) 0 0 [] [] =
    ([.asm (.asmi (.inst .skip)) [] 0], false, 0) := by
  simp [flatten, flattenOps]

/-- HOL `flatten T (Halt 0) 0 0 [] [] = (List [LabAsm Halt 0w [] 0],T,0)`. -/
example : flatten (flattenOps (width := 8)) (0 : W) true (.halt 0 : P) 0 0 [] [] =
    ([.labAsm .halt (0 : W) [] 0], true, 0) := by
  simp [flatten, flattenOps]

def runChecks : IO Bool := do
  IO.println "PASS stack_to_lab flatten base cases match HOL outputs"
  pure true

end Flapjack.Test.StackToLabFlattenBaseParity
