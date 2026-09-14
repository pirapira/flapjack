import Flapjack.CrepPrimop

/-!
# Parity checks for Crepe `crep_primop_def`

The direct HOL fixture in `scripts/hol-probes/crep_primop_probe.out` is
generated from `crepSemScript.sml:221-232`.  It checks the same fixed-width
word cases as the Lean implementation, including an arbitrary non-zero carry
word and malformed arity.
-/

namespace Flapjack.Test.CrepPrimopParity

open Flapjack
open Flapjack.RiscV

def w8 (value : Nat) : Word 8 := BitVec.ofNat 8 value

def addCarry (left right carry : Nat) : Option (Nat × Nat) :=
  match crepPrimop .addCarry [w8 left, w8 right, w8 carry] with
  | some [result, carryOut] => some (result.toNat, carryOut.toNat)
  | _ => none

def basic : Bool := addCarry 40 50 0 == some (90, 0)
def overflow : Bool := addCarry 200 100 0 == some (44, 1)
def carryIsBit : Bool := addCarry 5 7 2 == some (13, 0)
def wrongLength : Bool :=
  (crepPrimop .addCarry [w8 5, w8 7] : Option (List (Word 8))).isNone

#guard basic
#guard overflow
#guard carryIsBit
#guard wrongLength

def runChecks : IO Bool := do
  if basic then IO.println "PASS crep_primop basic" else IO.println "FAIL crep_primop basic"
  if overflow then IO.println "PASS crep_primop overflow" else IO.println "FAIL crep_primop overflow"
  if carryIsBit then IO.println "PASS crep_primop non-zero carry bit" else IO.println "FAIL crep_primop non-zero carry bit"
  if wrongLength then IO.println "PASS crep_primop wrong arity" else IO.println "FAIL crep_primop wrong arity"
  pure (basic && overflow && carryIsBit && wrongLength)

end Flapjack.Test.CrepPrimopParity
