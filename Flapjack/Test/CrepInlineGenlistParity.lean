import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.Test.CrepInlineGenlistParity

open Flapjack

/-! Executable regression for the exact `crep_inlineProofScript.sml` GENLIST
    interval lemmas (`genlist_less_than`, `genlist_not_in`,
    `genlist_all_distinct`) ported in `Flapjack.Pancake.Proofs.CrepInline`. -/

def crepInlineGenlistInterval : List Nat :=
  (List.range 5).map (fun x => 3 + (x + 1))

#guard crepInlineGenlistInterval = [4, 5, 6, 7, 8]

theorem crepInlineGenlistInterval_less_than :
    ∀ v ∈ crepInlineGenlistInterval, 3 < v :=
  fun v hv => genlist_less_than 5 3 v hv

theorem crepInlineGenlistInterval_not_in : (3 : Nat) ∉ crepInlineGenlistInterval :=
  genlist_not_in 5 3 3 (by decide)

theorem crepInlineGenlistInterval_all_distinct :
    crepInlineGenlistInterval.Nodup :=
  genlist_all_distinct 5 3

def crepInlineGenlistIntervalGuard : Bool :=
  crepInlineGenlistInterval.all (fun v => decide (3 < v)) &&
    crepInlineGenlistInterval.Nodup &&
    !crepInlineGenlistInterval.contains 3

#guard crepInlineGenlistIntervalGuard

def runChecks : IO Bool := do
  if crepInlineGenlistIntervalGuard then
    IO.println "PASS crep_inline GENLIST interval lemmas"
    pure true
  else
    IO.println "FAIL crep_inline GENLIST interval lemmas"
    pure false

end Flapjack.Test.CrepInlineGenlistParity