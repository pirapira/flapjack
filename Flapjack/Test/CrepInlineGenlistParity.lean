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

def crepInlineMaxListValues : List Nat := [4, 5, 6, 7, 8]

#guard maxList crepInlineMaxListValues = 8

theorem crepInlineMaxList_not_in : (9 : Nat) ∉ crepInlineMaxListValues :=
  moreThenNotMaxList crepInlineMaxListValues 9 (by decide)

def crepInlineMaxListGuard : Bool :=
  decide (maxList crepInlineMaxListValues = 8) &&
    !crepInlineMaxListValues.contains 9

#guard crepInlineMaxListGuard

theorem crepInlineMaxGenlist_add_suc_val :
    maxList ((List.range 5).map (fun x => (x + 1) + 3)) = 5 + 3 :=
  max_list_genlist_add_suc_val 3 5 (by decide)

def crepInlineMaxGenlistGuard : Bool :=
  decide (maxList ((List.range 5).map (fun x => (x + 1) + 3)) = 8)

#guard crepInlineMaxGenlistGuard

def runChecks : IO Bool := do
  let genlistOk ←
    if crepInlineGenlistIntervalGuard then
      IO.println "PASS crep_inline GENLIST interval lemmas"
      pure true
    else
      IO.println "FAIL crep_inline GENLIST interval lemmas"
      pure false
  let maxListOk ←
    if crepInlineMaxListGuard then
      IO.println "PASS crep_inline MORE_THEN_NOT_MAX_LIST"
      pure true
    else
      IO.println "FAIL crep_inline MORE_THEN_NOT_MAX_LIST"
      pure false
  let maxGenlistOk ←
    if crepInlineMaxGenlistGuard then
      IO.println "PASS crep_inline max_list_genlist_add_suc_val"
      pure true
    else
      IO.println "FAIL crep_inline max_list_genlist_add_suc_val"
      pure false
  pure (genlistOk && maxListOk && maxGenlistOk)

end Flapjack.Test.CrepInlineGenlistParity