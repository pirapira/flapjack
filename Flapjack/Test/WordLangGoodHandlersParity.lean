/-
  Direct parity check for the ported HOL `wordConvs$good_handlers_def`.

  The oracle rows come from `scripts/hol-probes/word_convs_good_handlers_probe.out`,
  produced by evaluating HOL `good_handlers 5` on the corresponding programs.
-/
import Flapjack.Pancake.WordConvs

namespace Flapjack.Test.WordLangGoodHandlersParity

open Flapjack

private abbrev W := BitVec 8

private def emptySet : WordLangNumSetHOL := .ln

private def badHandler : Option (Nat × WordLangProgHOL W × Nat × Nat) :=
  some (2, .skip, 6, 9)

private def okHandler : Option (Nat × WordLangProgHOL W × Nat × Nat) :=
  some (2, .skip, 5, 9)

private def ret :
    Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL W × Nat × Nat) :=
  some ([1], (emptySet, emptySet), .skip, 10, 11)

private def locProg : WordLangProgHOL W := .locValue 1 7

private def skipProg : WordLangProgHOL W := .skip

private def noHandler : Option (Nat × WordLangProgHOL W × Nat × Nat) := none

private def noReturns :
    Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL W × Nat × Nat) := none

private def innerBad : WordLangProgHOL W := .call ret none [] badHandler

-- Oracle row `gh_call_none`: a `ret = NONE` call ignores its handler entirely.
example : goodHandlersHOL 5 (WordLangProgHOL.call noReturns none [] noHandler) = true := by decide

example : goodHandlersHOL 5 (.call ret (some 7) [] noHandler) = true := by decide
example : goodHandlersHOL 5 (.call ret none [] okHandler) = true := by decide
example : goodHandlersHOL 5 (.call ret none [] badHandler) = false := by decide
example : goodHandlersHOL 5 (.call ret none [] (some (2, innerBad, 5, 9))) = false := by decide
example : goodHandlersHOL 5
    (.call (some ([1], (emptySet, emptySet), innerBad, 10, 11)) none [] noHandler) = false := by decide
example : goodHandlersHOL 5 (.seq skipProg skipProg) = true := by decide
example : goodHandlersHOL 5 (.seq skipProg (.loop emptySet innerBad emptySet)) = false := by decide
example : goodHandlersHOL 5 (.loop emptySet innerBad emptySet) = false := by decide
example : goodHandlersHOL 5 (.ite .equal 0 (.reg 1) skipProg innerBad) = false := by decide
example : goodHandlersHOL 5 (.mustTerminate innerBad) = false := by decide
example : goodHandlersHOL 5 locProg = true := by decide

private def guards : List Bool :=
  [ goodHandlersHOL 5 (.call noReturns none [] noHandler)
  , goodHandlersHOL 5 (.call ret (some 7) [] noHandler)
  , goodHandlersHOL 5 (.call ret none [] okHandler)
  , goodHandlersHOL 5 (.call ret none [] badHandler)
  , goodHandlersHOL 5 (.call ret none [] (some (2, innerBad, 5, 9)))
  , goodHandlersHOL 5 (.call (some ([1], (emptySet, emptySet), innerBad, 10, 11)) none [] noHandler)
  , goodHandlersHOL 5 (.seq skipProg skipProg)
  , goodHandlersHOL 5 (.seq skipProg (.loop emptySet innerBad emptySet))
  , goodHandlersHOL 5 (.loop emptySet innerBad emptySet)
  , goodHandlersHOL 5 (.ite .equal 0 (.reg 1) skipProg innerBad)
  , goodHandlersHOL 5 (.mustTerminate innerBad)
  , goodHandlersHOL 5 locProg
  ]

private def expected : List Bool :=
  [true, true, true, false, false, false, true, false, false, false, false, true]

#guard guards == expected

def runChecks : IO Bool := do
  if guards == expected then
    IO.println "PASS wordConvs good_handlers matches all 12 oracle rows"
    pure true
  else
    IO.println "FAIL wordConvs good_handlers oracle mismatch"
    pure false

end Flapjack.Test.WordLangGoodHandlersParity
