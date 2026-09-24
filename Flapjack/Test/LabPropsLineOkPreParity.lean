import Flapjack.Compiler.Backend.LabProps

/-!
# Cake labProps `line_ok_pre` over a concrete `AsmConfig`

Regression for the concrete configuration instantiation in
`Flapjack/Compiler/Backend/LabProps.lean` (`asmConfigChecks`,
`lineOkPreConfig`, `secOkPreConfig`, `allEncOkPreConfig`). The nine guards
below mirror the direct HOL `EVAL` rows in
`scripts/hol-probes/lab_props_line_ok_pre_probe.out` at an 8-bit
configuration identical to the probe fixture. -/

namespace Flapjack.Test.LabPropsLineOkPreParity

open Flapjack
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n

private def cfg8 : AsmConfig 8 where
  isa := .riscv
  encode := fun _ => []
  bigEndian := false
  codeAlignment := 2
  linkReg := none
  avoidRegs := [3]
  regCount := 8
  fpRegCount := 4
  twoRegArith := true
  validImm := fun _ _ => true
  addrOffset := (w8 0, w8 100)
  hwOffset := (w8 0, w8 100)
  byteOffset := (w8 0, w8 100)
  jumpOffset := (w8 0, w8 100)
  cjumpOffset := (w8 0, w8 100)
  locOffset := (w8 0, w8 100)

private abbrev L := Line (AsmOrCbw (AsmData 8) WordMemOp (WordLangAddr W))
  (AsmWithLab Cmp Nat String) W

private def asmSkipLine : L := .asm (.asmi (.inst .skip)) [] 0
private def asmCbwLine : L := .asm (.cbw 1 2) [] 0
private def labelLine : L := .label 0 1 0
private def labAsmHaltLine : L := .labAsm .halt (w8 0) [] 0
private def asmBadRegLine : L := .asm (.asmi (.inst (.const 9 (w8 0)))) [] 0

private def secOk : Section L := { sectionId := 0, lines := [asmSkipLine] }
private def secBad : Section L := { sectionId := 0, lines := [asmBadRegLine] }

example : lineOkPreConfig cfg8 asmSkipLine = true := by decide
example : lineOkPreConfig cfg8 asmCbwLine = true := by decide
example : lineOkPreConfig cfg8 labelLine = true := by decide
example : lineOkPreConfig cfg8 labAsmHaltLine = true := by decide
example : lineOkPreConfig cfg8 asmBadRegLine = false := by decide
example : allEncOkPreConfig cfg8 [secOk] = true := by decide
example : allEncOkPreConfig cfg8 [secBad] = false := by decide
example : cbwToAsm (asmConfigChecks cfg8) (.cbw 1 2) =
    (.inst (.mem .store8 2 (.addr 1 0)) : AsmData 8) := rfl
example : cbwToAsm (asmConfigChecks cfg8) (.shareMem .load 4 (.addr 5 0)) =
    (.inst (.mem .load 4 (.addr 5 0)) : AsmData 8) := rfl

private def cbwRowOk (instruction : AsmOrCbw (AsmData 8) WordMemOp (WordLangAddr W)) : Bool :=
  match cbwToAsm (asmConfigChecks cfg8) instruction with
  | .inst (.mem .store8 2 (.addr 1 0)) => true
  | .inst (.mem .load 4 (.addr 5 0)) => true
  | _ => false

/-- The emitted base-line reductions of `line_ok_pre` at the concrete config,
mirroring the direct HOL oracle rows. -/
example : lineOkPreConfig cfg8 (.asm (.asmi (.inst .skip)) [] 0 : L) = true := by
  simp [lineOkPreConfig_asm_asmi, Flapjack.Compiler.Encoders.Asm.asmOk,
    Flapjack.Compiler.Encoders.Asm.asmInstOk]

example : lineOkPreConfig cfg8 (.asm (.asmi (.inst (.const 9 0))) [] 0 : L) = false := by
  simp [lineOkPreConfig_asm_asmi, Flapjack.Compiler.Encoders.Asm.asmOk,
    Flapjack.Compiler.Encoders.Asm.asmInstOk, Flapjack.Compiler.Encoders.Asm.asmRegOk, cfg8]

example : lineOkPreConfig cfg8 (.label 0 1 0 : L) = true := by
  simp [lineOkPreConfig_label]

def runChecks : IO Bool := do
  let guards : List Bool :=
    [ decide (lineOkPreConfig cfg8 asmSkipLine = true)
    , decide (lineOkPreConfig cfg8 asmCbwLine = true)
    , decide (lineOkPreConfig cfg8 labelLine = true)
    , decide (lineOkPreConfig cfg8 labAsmHaltLine = true)
    , decide (lineOkPreConfig cfg8 asmBadRegLine = false)
    , decide (allEncOkPreConfig cfg8 [secOk] = true)
    , decide (allEncOkPreConfig cfg8 [secBad] = false)
    , cbwRowOk (.cbw 1 2)
    , cbwRowOk (.shareMem .load 4 (.addr 5 0))
    ]
  let ok := guards.all id
  if ok then
    IO.println "PASS labProps line_ok_pre/all_enc_ok_pre over concrete AsmConfig match all 9 oracle rows"
  else
    IO.println "FAIL labProps line_ok_pre/all_enc_ok_pre over concrete AsmConfig"
  pure ok

end Flapjack.Test.LabPropsLineOkPreParity