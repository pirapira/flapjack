/-
  Parity checks for the faithful backend `wordConvs$extract_labels` port over
  the backend `wordLang$prog` datatype.

  The kernel-checked examples below mirror the rows of the direct original-HOL
  oracle `scripts/hol-probes/word_convs_extract_labels_probe.out` (generated
  from `cakeml/compiler/backend/semantics/wordConvsScript.sml:440-459`): the
  `Call` return/handler labels are collected and the return-handler,
  handler, `MustTerminate`, `Seq`, `Loop`, and `If` bodies are descended into,
  while every other constructor contributes no label.  With no `Call` return
  metadata the result is empty even when a handler is present.
-/
import Flapjack.Pancake.WordConvs

open Flapjack

namespace Flapjack.Test.WordLangExtractLabelsParity

private def emptySet : WordLangNumSet := fun _ => none

private def cutsets : WordLangCutsets := (emptySet, emptySet)

private def skipProg : WordLangProg Nat := .skip

private def callNone : WordLangProg Nat := .call none none [] none

private def callRet : WordLangProg Nat :=
  .call (some ([1], cutsets, skipProg, 10, 11)) none [] none

private def callBoth : WordLangProg Nat :=
  .call (some ([1], cutsets, skipProg, 10, 11)) none []
    (some (2, skipProg, 20, 21))

/-- `Inst Skip` carries no labels. -/
example : extractLabels (WordLangProg.inst (WordLangInst.skip : WordLangInst Nat)) = [] := rfl

/-- A `Call` with no return metadata contributes no labels. -/
example : extractLabels callNone = [] := rfl

/-- The return-handler labels of a `Call` are collected. -/
example : extractLabels callRet = [(10, 11)] := rfl

/-- The return-handler and handler labels are collected together. -/
example : extractLabels callBoth = [(10, 11), (20, 21)] := rfl

/-- With no `Call` return metadata the result is empty even with a handler. -/
example : extractLabels (.call none none [] (some (2, callRet, 20, 21))) = [] := rfl

/-- `MustTerminate` descends into its body. -/
example : extractLabels (.mustTerminate callBoth) = [(10, 11), (20, 21)] := rfl

/-- `Seq` descends into both branches. -/
example : extractLabels (.seq callBoth skipProg) = [(10, 11), (20, 21)] := rfl

/-- `Loop` descends into its body. -/
example : extractLabels (.loop emptySet callBoth emptySet) = [(10, 11), (20, 21)] := rfl

/-- `If` descends into both branches. -/
example : extractLabels (.ite .equal 0 (.reg 1) callBoth skipProg) = [(10, 11), (20, 21)] := rfl

/-- Nested handlers concatenate in HOL order. -/
example :
    extractLabels (.call (some ([1], cutsets, callBoth, 10, 11)) none []
      (some (2, callRet, 20, 21))) =
      [(10, 11), (20, 21), (10, 11), (20, 21), (10, 11)] := rfl

#guard extractLabels callNone == ([] : List (Nat × Nat))
#guard extractLabels callRet == [(10, 11)]
#guard extractLabels callBoth == [(10, 11), (20, 21)]
#guard extractLabels (.mustTerminate callBoth) == [(10, 11), (20, 21)]
#guard extractLabels (.seq callBoth skipProg) == [(10, 11), (20, 21)]

def runChecks : IO Bool := do
  if extractLabels callRet == ([(10, 11)] : List (Nat × Nat)) then
    IO.println "PASS wordConvs extract_labels collects Call return labels"
  else IO.println "FAIL wordConvs extract_labels collects Call return labels"
  if extractLabels callBoth == ([(10, 11), (20, 21)] : List (Nat × Nat)) then
    IO.println "PASS wordConvs extract_labels collects return and handler labels"
  else IO.println "FAIL wordConvs extract_labels collects return and handler labels"
  if extractLabels (.call none none [] (some (2, callRet, 20, 21))) == ([] : List (Nat × Nat)) then
    IO.println "PASS wordConvs extract_labels is empty without return metadata"
  else IO.println "FAIL wordConvs extract_labels is empty without return metadata"
  if extractLabels (.seq callBoth skipProg) == ([(10, 11), (20, 21)] : List (Nat × Nat)) then
    IO.println "PASS wordConvs extract_labels descends into composition"
  else IO.println "FAIL wordConvs extract_labels descends into composition"
  pure (extractLabels callRet == ([(10, 11)] : List (Nat × Nat)))

end Flapjack.Test.WordLangExtractLabelsParity