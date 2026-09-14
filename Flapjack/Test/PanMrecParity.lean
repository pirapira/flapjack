import Flapjack.PanMrec
import Flapjack.Ffi

/-!
# Parity checks for Pancake `mrec_def`

The direct HOL fixture in `scripts/hol-probes/pan_mrec_probe.out` evaluates
the source `mrec_def` from
`cakeml/pancake/semantics/pan_itreeSemScript.sml:173-190`.  The Lean checks
exercise returns, taus, an internal handler transition, and an external event
whose continuation is wrapped in the source tau.
-/

namespace Flapjack.Test.PanMrecParity

open Flapjack

def identityHandler : Unit → PanMrecTree Unit Unit FfiName Unit :=
  fun _ => .ret ()

def tauHandler : Unit → PanMrecTree Unit Unit FfiName Unit :=
  fun _ => .tau (.ret ())

def retTree : PanMrecTree Unit Unit FfiName Unit := .ret ()

def tauTree : PanMrecTree Unit Unit FfiName Unit := .tau (.ret ())

def internalTree : PanMrecTree Unit Unit FfiName Unit :=
  .visInternal () (fun _ => .ret ())

def externalTree : PanMrecTree Unit Unit FfiName Unit :=
  .visExternal (FfiName.extCall "foo") (fun _ => .ret ())

def observeRet : Bool :=
  match (panMrecFuel 1 identityHandler retTree : PanMrecTree Unit Unit FfiName Unit) with
  | .ret () => true
  | _ => false

def observeTau : Bool :=
  match (panMrecFuel 1 identityHandler tauTree : PanMrecTree Unit Unit FfiName Unit) with
  | .tau (.ret ()) => true
  | _ => false

def observeInternal : Bool :=
  match (panMrecFuel 2 identityHandler internalTree : PanMrecTree Unit Unit FfiName Unit) with
  | .tau (.ret ()) => true
  | _ => false

def observeInternalIntermediate : Bool :=
  match (panMrecFuel 2 tauHandler internalTree : PanMrecTree Unit Unit FfiName Unit) with
  | .tau (.tau (.ret ())) => true
  | _ => false

def observeExternal : Bool :=
  match (panMrecFuel 1 identityHandler externalTree : PanMrecTree Unit Unit FfiName Unit) with
  | .visExternal (FfiName.extCall "foo") continuation =>
      match continuation () with
      | .tau (.ret ()) => true
      | _ => false
  | _ => false

#guard observeRet
#guard observeTau
#guard observeInternal
#guard observeInternalIntermediate
#guard observeExternal

def runChecks : IO Bool := do
  if observeRet then IO.println "PASS mrec Ret" else IO.println "FAIL mrec Ret"
  if observeTau then IO.println "PASS mrec Tau" else IO.println "FAIL mrec Tau"
  if observeInternal then IO.println "PASS mrec internal event" else IO.println "FAIL mrec internal event"
  if observeInternalIntermediate then
    IO.println "PASS mrec internal intermediate bind"
  else
    IO.println "FAIL mrec internal intermediate bind"
  if observeExternal then IO.println "PASS mrec external event" else IO.println "FAIL mrec external event"
  pure (observeRet && observeTau && observeInternal &&
    observeInternalIntermediate && observeExternal)

end Flapjack.Test.PanMrecParity
