import Flapjack.Pancake.CrepLang

/-!
# Original-domain parity for `crepLang$load_shape`

The expected values are the direct HOL-EVAL observations in
`scripts/hol-probes/crep_load_shape_probe.out`, from
`cakeml/pancake/crepLangScript.sml:82-86`.
-/

namespace Flapjack.Test.CrepeLoadShapeParity

open Flapjack

def probeValue : CrepExp Nat := .const 7

def isZeroOne : List (CrepExp Nat) → Bool
  | [.load (.const value)] => value == 7
  | _ => false

def isZeroTwo : List (CrepExp Nat) → Bool
  | [.load (.const first),
     .load (.op .add [.const second, .const offset])] =>
      first == 7 && second == 7 && offset == 4
  | _ => false

def isNonzeroTwo : List (CrepExp Nat) → Bool
  | [.load (.op .add [.const first, .const firstOffset]),
     .load (.op .add [.const second, .const secondOffset])] =>
      first == 7 && firstOffset == 4 && second == 7 && secondOffset == 8
  | _ => false

def parityGuard : Bool :=
  (loadShape 0 4 0 probeValue).isEmpty &&
  isZeroOne (loadShape 0 4 1 probeValue) &&
  isZeroTwo (loadShape 0 4 2 probeValue) &&
  isNonzeroTwo (loadShape 4 4 2 probeValue)

#eval parityGuard
#guard parityGuard

/-- The same four HOL-EVAL observations through the exact fixed-byte-width
    interface `loadShapeBytes`.  `BitVec 32` instantiates `CrepBytesInWord` with
    `bytesInWord = 4` (`byte$bytes_in_word` for a 32-bit word), matching the
    probe's `32 word` values. -/
def fixedProbeValue : CrepExp (BitVec 32) := .const (BitVec.ofNat 32 7)

def fixedParityGuard : Bool :=
  (loadShapeBytes (0 : BitVec 32) 0 fixedProbeValue).isEmpty &&
  (loadShapeBytes (0 : BitVec 32) 1 fixedProbeValue ==
    [.load (.const (BitVec.ofNat 32 7))]) &&
  (loadShapeBytes (0 : BitVec 32) 2 fixedProbeValue ==
    [.load (.const (BitVec.ofNat 32 7)),
     .load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 4)])]) &&
  (loadShapeBytes (BitVec.ofNat 32 4) 2 fixedProbeValue ==
    [.load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 4)]),
     .load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 8)])])

#eval fixedParityGuard
#guard fixedParityGuard

def check (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "crep load_shape empty" (loadShape 0 4 0 probeValue).isEmpty true,
    check "crep load_shape zero one" (isZeroOne (loadShape 0 4 1 probeValue)) true,
    check "crep load_shape zero two" (isZeroTwo (loadShape 0 4 2 probeValue)) true,
    check "crep load_shape nonzero two"
      (isNonzeroTwo (loadShape 4 4 2 probeValue)) true,
    check "crep load_shape fixed byte width" fixedParityGuard true ].mapM id
  pure (results.all id)

end Flapjack.Test.CrepeLoadShapeParity
