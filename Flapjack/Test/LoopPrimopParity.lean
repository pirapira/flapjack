import Flapjack.Pancake.Semantics.LoopSem

/-!
# Original-domain parity for `loopSem.loop_primop`

Expected observations are transcribed from direct HOL-EVAL of
`cakeml/pancake/semantics/loopSemScript.sml:242-252`, checked in at
`scripts/hol-probes/loop_sem_primop_probe.out`.  The `valid_carry` row's
printed low word is the zero word (the probe prints the unreduced numeral);
this test compares against the definition, which yields `[0, 1]`.

The port is exercised over the word-location cells that
`LoopEvaluateHooks.primitive` receives, so the malformed-cell rejection case
uses a `.loc` cell.
-/

namespace Flapjack.Test.LoopPrimopParity

open Flapjack

def originalValidNoCarry : Option (List (LoopValue (BitVec 64))) :=
  some [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 0)]

def originalValidCarry : Option (List (LoopValue (BitVec 64))) :=
  some [.word (BitVec.ofNat 64 0), .word (BitVec.ofNat 64 1)]

def isValidNoCarry : Bool :=
  loopPrimopHOL (width := 64) .addCarry
      [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 4),
        .word (BitVec.ofNat 64 0)] =
    originalValidNoCarry

def isValidCarry : Bool :=
  loopPrimopHOL (width := 64) .addCarry
      [.word (BitVec.ofNat 64 (2 ^ 64 - 1)), .word (BitVec.ofNat 64 0),
        .word (BitVec.ofNat 64 1)] =
    originalValidCarry

def isInvalidArity : Bool :=
  loopPrimopHOL (width := 64) .addCarry
      [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 4)] = none

def isInvalidNonword : Bool :=
  loopPrimopHOL (width := 64) .addCarry
      [.loc 0 0, .word (BitVec.ofNat 64 4), .word (BitVec.ofNat 64 0)] = none

#guard isValidNoCarry
#guard isValidCarry
#guard isInvalidArity
#guard isInvalidNonword

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop loop_primop valid AddCarry without carry", isValidNoCarry),
      ("Loop loop_primop valid AddCarry with carry", isValidCarry),
      ("Loop loop_primop rejects wrong arity", isInvalidArity),
      ("Loop loop_primop rejects non-word cells", isInvalidNonword) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopPrimopParity
