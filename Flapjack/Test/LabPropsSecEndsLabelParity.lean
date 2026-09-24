import Flapjack.Compiler.Backend.LabProps
import Flapjack.Compiler.Backend.LabSem

/-!
# LabLang `is_Label` / `sec_ends_with_label` parity

Kernel-checked fixtures matching `scripts/hol-probes/lab_props_sec_ends_label_probe.out`
(direct original-HOL `EVAL` rows for `labSem$is_Label` and
`labProps$sec_ends_with_label`), plus applications of the structural lemma and
the (untagged) `prog_to_section` label-end analogue.
-/

namespace Flapjack.Test.LabPropsSecEndsLabelParity

open Flapjack
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem

private abbrev W := BitVec 8

private abbrev L :=
  Line (AsmOrCbw (Flapjack.Compiler.Encoders.Asm.AsmData 8) WordMemOp (WordLangAddr W))
    (AsmWithLab Flapjack.Cmp Nat String) W

private abbrev P :=
  Flapjack.Compiler.Backend.StackLang.Prog (WordLangInst W) Flapjack.Cmp
    (WordRegImm W) Flapjack.BinOp WordMemOp (WordLangAddr W) String

private def labelLine : L := .label 0 1 0
private def asmLine : L := .asm (.asmi (.inst .skip)) [] 0
private def secLabel : Section L := { sectionId := 0, lines := [labelLine] }
private def secAsm : Section L := { sectionId := 0, lines := [asmLine] }
private def secEmpty : Section L := { sectionId := 0, lines := [] }

example : isLabel labelLine = true := by decide
example : isLabel asmLine = false := by decide
example : secEndsWithLabel secLabel = true := by decide
example : secEndsWithLabel secAsm = false := by decide
example : secEndsWithLabel secEmpty = false := by decide

example : secEndsWithLabel
    ({ sectionId := 0, lines := [asmLine] ++ [.label 0 1 0] } : Section L) = true :=
  secEndsWithLabel_append_label _ 0 1 0

example : ([(0, (Flapjack.Compiler.Backend.StackLang.Prog.tick : P))].map
      (fun entry =>
        Flapjack.Compiler.Backend.StackToLab.progToSection
          (flattenOps (width := 8)) (0 : W) entry.1 entry.2)).all secEndsWithLabel
    = true :=
  everySecEndsWithLabel_map_progToSection (flattenOps (width := 8)) (0 : W)
    [(0, Flapjack.Compiler.Backend.StackLang.Prog.tick)]

private def guards : List Bool :=
  [isLabel labelLine, isLabel asmLine, secEndsWithLabel secLabel,
    secEndsWithLabel secAsm, secEndsWithLabel secEmpty]

private def expected : List Bool := [true, false, true, false, false]

#guard guards == expected

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS labProps is_Label/sec_ends_with_label match all 5 oracle rows"
  else
    IO.println "FAIL labProps is_Label/sec_ends_with_label"
  pure (guards == expected)

end Flapjack.Test.LabPropsSecEndsLabelParity