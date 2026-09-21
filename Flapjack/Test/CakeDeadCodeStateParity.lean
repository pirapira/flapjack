import Flapjack.RiscV.WordDeadCode

/-! Direct Cake/HOL parity for the `remove_dead` global-store state carried by
    `nlive`.  Cake resets `nlive` after a non-variable `Set`, so an earlier
    global write must remain when a later variable write follows it.  The
    exact output is from canonical `word_allocScript.sml:952-961` and
    `remove_dead_prog_def`; the temporary HOL probe is not checked in. -/

namespace Flapjack.Test.CakeDeadCodeStateParity

open Flapjack Flapjack.RiscV

def nonVariableGlobalReset : WordProg Nat :=
  .seq (.set (.globals : WordStore Nat) (.const 1))
    (.seq (.set (.globals : WordStore Nat) (.var 8)) (.return 0 []))

def nonVariableGlobalResetGuard : Bool :=
  match wordRemoveDeadProgram nonVariableGlobalReset with
  | .seq (.set .globals (.const 1))
      (.seq (.set .globals (.var 8)) (.return 0 [])) => true
  | _ => false

#guard nonVariableGlobalResetGuard

def parityGuard : Bool := nonVariableGlobalResetGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("remove_dead resets Cake nlive after a non-variable global Set",
        nonVariableGlobalResetGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeDeadCodeStateParity
