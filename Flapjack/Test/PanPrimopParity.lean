import Flapjack.RiscV.PanSemantics

/-!
Parity test for the faithful source `AddCarry` primitive (`pan_primop`).

The expected values below are transcribed from the checked-in output of the
original Pancake `pan_primop` HOL probe:
`scripts/hol-probes/pan_sem_pan_primop_probe.out`, produced by
`scripts/hol-probes/pan_sem_pan_primop_probeScript.sml` and regenerated with

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml CAKEML=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

Original source: `cakeml/pancake/semantics/panSemScript.sml:196-207`
(`pan_primop_def`). The probe fixes `'a = 8`, so `dimword (:'a) = 256`.
-/

namespace Flapjack.Test.PanPrimopParity

open Flapjack
open Flapjack.RiscV

/-- 8-bit word literal. -/
def w8 (value : Nat) : Word 8 := BitVec.ofNat 8 value

/-- Runs the `AddCarry` handler and reads back the numeric result pair. -/
def addCarry (left right carry : Nat) : Option (Nat × Nat) :=
  match panPrimitiveHandler (width := 8) .addCarry [.word (w8 left), .word (w8 right),
      .word (w8 carry)] with
  | some (.rStruct [.word result, .word carryOut]) => some (result.toNat, carryOut.toNat)
  | _ => none

def basic : Bool := addCarry 40 50 0 == some (90, 0)

def overflow : Bool := addCarry 200 100 0 == some (44, 1)

/-- A non-zero, non-one carry word contributes exactly one. -/
def carryIsBit : Bool := addCarry 5 7 2 == some (13, 0)

def wrongLength : Bool :=
  ((panPrimitiveHandler (width := 8) .addCarry
      [.word (w8 5), .word (w8 7)] : Option (PanValue (Word 8)))).isNone

def nonWord : Bool :=
  ((panPrimitiveHandler (width := 8) .addCarry
      [.word (w8 5), .rStruct [], .word (w8 3)] : Option (PanValue (Word 8)))).isNone

#guard basic
#guard overflow
#guard carryIsBit
#guard wrongLength
#guard nonWord

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Pan pan_primop adds without carry", basic),
    ("Pan pan_primop carries out of range", overflow),
    ("Pan pan_primop treats a non-zero carry as one", carryIsBit),
    ("Pan pan_primop rejects a wrong argument count", wrongLength),
    ("Pan pan_primop rejects a non-word argument", nonWord)]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.PanPrimopParity
