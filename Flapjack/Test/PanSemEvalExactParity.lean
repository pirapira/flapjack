/-
Parity for the exact-carrier `eval_def` port (`Flapjack/Pancake/Semantics/PanSem/EvalExact.lean`,
bead flapjack-pxn.18.3.6.9.15).  The nine rows mirror the direct original-HOL
equalities in `scripts/hol-probes/pan_eval_probe.out` (all `T`), which were
produced from `pan_itreeSemTheory` whose `eval_def` is identical to
`panSemScript.sml:209`.  The exact carriers (`ValueHOL`, `PanSemStateExact`)
derive only `Repr`, so the guards project to `Nat`/`Bool`.
-/
import Flapjack.Pancake.Semantics.PanSem.EvalExact

namespace Flapjack.Test.PanSemEvalExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL)

private abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev exactStructs : Flapjack.Pancake.PanLang.StructContextExact :=
  [(ml "Pair", { fields := [(ml "left", ShapeHOL.one), (ml "right", ShapeHOL.one)], size := 2 })]

private abbrev exactState : PanSemStateExact 8 Unit where
  locals := fun name => if name = ml "x" then some (.val (.word 5)) else none
  globals := fun name => if name = ml "g" then some (.val (.word 6)) else none
  structs := exactStructs
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

private def wordNat? : Option (ValueHOL 8) → Option Nat
  | some (.val (.word value)) => some value.toNat
  | _ => none

private def isNoneResult : Option (ValueHOL 8) → Bool
  | none => true
  | _ => false

private def namedPairEq : Option (ValueHOL 8) → Bool
  | some (.nStruct name fields) =>
      name = ml "Pair" &&
        (match fields with
         | [(leftName, .val (.word leftWord)), (rightName, .val (.word rightWord))] =>
             leftName = ml "left" && rightName = ml "right" &&
             leftWord.toNat = 3 && rightWord.toNat = 4
         | _ => false)
  | _ => false

def evalExactGuard : Bool :=
  wordNat? (evalHOLExact exactState (.const (7 : BitVec 8))) == some 7 &&
  wordNat? (evalHOLExact exactState (.var .local (ml "x"))) == some 5 &&
  wordNat? (evalHOLExact exactState (.var .global (ml "g"))) == some 6 &&
  wordNat? (evalHOLExact exactState
    (.rfield 1 (.rstruct [.const (2 : BitVec 8), .const (9 : BitVec 8)]))) == some 9 &&
  isNoneResult (evalHOLExact exactState (.var .local (ml "missing"))) &&
  namedPairEq (evalHOLExact exactState
    (.nstruct (ml "Pair") [(ml "left", .const (3 : BitVec 8)), (ml "right", .const (4 : BitVec 8))])) &&
  isNoneResult (evalHOLExact exactState
    (.nstruct (ml "Pair") [(ml "left", .const (3 : BitVec 8)), (ml "bad", .const (4 : BitVec 8))])) &&
  isNoneResult (evalHOLExact exactState
    (.nstruct (ml "Pair") [(ml "left", .const (3 : BitVec 8)), (ml "right", .rstruct [])])) &&
  isNoneResult (evalHOLExact { exactState with structs := [] } (.nstruct (ml "Pair") []))

#guard evalExactGuard

def runChecks : IO Bool := do
  if evalExactGuard then
    IO.println "PASS exact panSem eval_def over the exact MlString carrier (9 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem eval_def over the exact MlString carrier"
    pure false

end Flapjack.Test.PanSemEvalExactParity
