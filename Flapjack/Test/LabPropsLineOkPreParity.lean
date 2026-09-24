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

example : lineOkPreConfig cfg8 ((.asm (.asmi flattenOps.skip) [] 0) :
    Line (AsmOrCbw (AsmData 8) WordMemOp (WordLangAddr W)) (AsmWithLab Cmp Nat String) W) = true :=
  lineOkPreConfig_flattenOps_skip cfg8 [] 0

example : lineOkPreConfig cfg8 ((.asm (.asmi (flattenOps.embedInst (.skip : WordLangInst W))) [] 0) :
    Line (AsmOrCbw (AsmData 8) WordMemOp (WordLangAddr W)) (AsmWithLab Cmp Nat String) W) = true := by
  rw [lineOkPreConfig_flattenOps_embedInst]
  simp [Flapjack.Compiler.Encoders.Asm.asmInstOk]

example : lineOkPreConfig cfg8 ((.asm (.asmi (flattenOps.jumpReg 3)) [] 0) :
    Line (AsmOrCbw (AsmData 8) WordMemOp (WordLangAddr W)) (AsmWithLab Cmp Nat String) W) =
      Flapjack.Compiler.Encoders.Asm.asmRegOk cfg8 3 :=
  lineOkPreConfig_flattenOps_jumpReg cfg8 3 [] 0


private abbrev P := Flapjack.Compiler.Backend.StackLang.Prog
  (WordLangInst W) Flapjack.Cmp (WordRegImm W) Flapjack.BinOp WordMemOp (WordLangAddr W) String

/-- The bridge lets `stack_asm_ok` discharge a per-line `instOk` obligation. -/
example : Flapjack.Compiler.Encoders.Asm.asmInstOk cfg8 (WordLangInst.skip : WordLangInst W) = true :=
  stackAsmOk_asmChecksOfConfig_inst cfg8 WordLangInst.skip (by
    simp [Flapjack.Compiler.Backend.StackProps.stackAsmOk,
      Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig, asmInstOk])

/-- The bridge exposes the `stack_asm_ok` register bound for `Raise`. -/
example (h : Flapjack.Compiler.Backend.StackProps.stackAsmOk
      (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8)
      (.raise 2 : P) = true) :
    (2 < cfg8.regCount && !cfg8.avoidRegs.contains 2) = true :=
  stackAsmOk_asmChecksOfConfig_raise cfg8 2 h

/-- The decomposition lemmas split a recursive `stack_asm_ok` obligation. -/
example : (Flapjack.Compiler.Backend.StackProps.stackAsmOk
      (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8)
      (.seq (.tick : P) (.skip : P) : P) = true) ↔
    (Flapjack.Compiler.Backend.StackProps.stackAsmOk
        (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.tick : P) = true ∧
      Flapjack.Compiler.Backend.StackProps.stackAsmOk
        (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.skip : P) = true) :=
  stackAsmOk_asmChecksOfConfig_seq cfg8 _ _

example : (Flapjack.Compiler.Backend.StackProps.stackAsmOk
      (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.loop (.skip : P) : P) = true) ↔
    Flapjack.Compiler.Backend.StackProps.stackAsmOk
      (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.skip : P) = true :=
  stackAsmOk_asmChecksOfConfig_loop cfg8 _

example : (Flapjack.Compiler.Backend.StackProps.stackAsmOk
      (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8)
      (.call (some ((.skip : P), 7, 1, 0)) (.inl 2) (some ((.tick : P), 3, 4)) : P) = true) ↔
    (Flapjack.Compiler.Backend.StackProps.stackAsmOk
        (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.skip : P) = true ∧
      Flapjack.Compiler.Backend.StackProps.stackAsmOk
        (Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig cfg8) (.tick : P) = true) :=
  stackAsmOk_asmChecksOfConfig_call_some_inl_some cfg8 _ 7 1 0 2 _ 3 4

/-- The top-level flat `flatten_line_ok_pre` fires on a concrete program. -/
example : ((Flapjack.Compiler.Backend.StackToLab.flatten (flattenOps (width := 8)) (0 : W) false
      (.tick : P) 0 0 [] []).1.all (lineOkPreConfig cfg8)) = true :=
  flatten_line_ok_pre cfg8 (.tick : P) false 0 0 [] []
    (by decide)
    (by simp [Flapjack.Compiler.Backend.StackProps.stackAsmOk,
      Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig])

/-- The HOL-exact `append`-form `flatten_line_ok_pre` over `flattenApp` fires. -/
example : (appListAppend (.list ([.labAsm .halt (0 : W) [] 0] : List (Flapjack.Compiler.Backend.StackToLab.FlatLine WordMemOp (WordLangAddr W) Flapjack.Cmp (WordRegImm W) String (AsmData 8) W)))).all (lineOkPreConfig cfg8) = true :=
  flattenApp_line_ok_pre cfg8 (.halt 0 : P) true 0 0 [] []
    (.list [.labAsm .halt (0 : W) [] 0]) true 0
    (by decide)
    (by simp [Flapjack.Compiler.Backend.StackProps.stackAsmOk,
      Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig])
    (by simp [Flapjack.Compiler.Backend.StackToLab.flattenApp])

/-- The HOL-exact `append`-form `compile_all_enc_ok_pre` over `progToSectionApp` fires. -/
example : (([(0, (.tick : P))].map (fun entry =>
      Flapjack.Compiler.Backend.StackToLab.progToSectionApp (flattenOps (width := 8))
        (0 : W) entry.1 entry.2)).all (secOkPreConfig cfg8)) = true :=
  compile_all_enc_ok_pre_app cfg8 [(0, (.tick : P))] (by decide)
    (by simp [Flapjack.Compiler.Backend.StackProps.stackAsmOk,
      Flapjack.Compiler.Backend.StackProps.asmChecksOfConfig])

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