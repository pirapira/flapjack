import Flapjack.LoopFfi

/-!
# Original-domain parity for `is_load`

`loopFfiIsLoad` corresponds to Pancake's `is_load_def` in
`cakeml/pancake/loop_callScript.sml:10-15`.  The expected booleans are from
the checked-in HOL probe `loop_call_is_load_probe.out`.
-/

namespace Flapjack.Test.LoopIsLoadParity

open Flapjack

def originalLoad : Bool := true
def originalLoad8 : Bool := true
def originalLoad16 : Bool := true
def originalLoad32 : Bool := true
def originalStore : Bool := false
def originalStore8 : Bool := false
def originalStore16 : Bool := false
def originalStore32 : Bool := false

#guard loopFfiIsLoad .load == originalLoad
#guard loopFfiIsLoad .load8 == originalLoad8
#guard loopFfiIsLoad .load16 == originalLoad16
#guard loopFfiIsLoad .load32 == originalLoad32
#guard loopFfiIsLoad .store == originalStore
#guard loopFfiIsLoad .store8 == originalStore8
#guard loopFfiIsLoad .store16 == originalStore16
#guard loopFfiIsLoad .store32 == originalStore32

def check (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "is_load load" (loopFfiIsLoad .load) originalLoad,
    check "is_load load8" (loopFfiIsLoad .load8) originalLoad8,
    check "is_load load16" (loopFfiIsLoad .load16) originalLoad16,
    check "is_load load32" (loopFfiIsLoad .load32) originalLoad32,
    check "is_load store" (loopFfiIsLoad .store) originalStore,
    check "is_load store8" (loopFfiIsLoad .store8) originalStore8,
    check "is_load store16" (loopFfiIsLoad .store16) originalStore16,
    check "is_load store32" (loopFfiIsLoad .store32) originalStore32 ].mapM id
  pure (results.all id)

end Flapjack.Test.LoopIsLoadParity
