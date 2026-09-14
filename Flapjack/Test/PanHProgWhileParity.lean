import Flapjack.PanHProgWhile

/-!
# Parity checks for Pancake `h_prog_while_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_while_probe.out` comes from
`pan_itreeSemScript.sml:318-336`.  These checks cover zero guard exit,
guard failure, body event emission, break, continue/normal re-entry, event
failure, and finite fuel exhaustion.
-/

namespace Flapjack.Test.PanHProgWhileParity

open Flapjack

def evalGuard : Nat → Exp Nat → Option (PanValue Nat)
  | _, .const value => some (.word value)
  | _, _ => none

def body : Prog Nat := .skip

def observeZeroGuard : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 0) body with
  | some (.ret .normal state) => state == 7
  | _ => false

def observeBodyEvent : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 1) body with
  | some (.vis selected state _) =>
      state == 7 &&
        match selected with
        | .skip => true
        | _ => false
  | _ => false

def observeBreak : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 1) body with
  | some (.vis _ _ k) =>
      match k (.returned .break 8) with
      | some (.ret .normal state) => state == 8
      | _ => false
  | _ => false

def observeContinue : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 1) body with
  | some (.vis _ _ k) =>
      match k (.returned .continue 8) with
      | some (.tau (.vis _ state _)) => state == 8
      | _ => false
  | _ => false

def observeNormalReentry : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 1) body with
  | some (.vis _ _ k) =>
      match k (.returned .normal 8) with
      | some (.tau (.vis _ state _)) => state == 8
      | _ => false
  | _ => false

def observeFailed : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.const 1) body with
  | some (.vis _ _ k) =>
      match k .failed with
      | some (.ret .error state) => state == 7
      | _ => false
  | _ => false

def observeInvalidGuard : Bool :=
  match panHProgWhileFuel 2 evalGuard 7 (.var .local "missing") body with
  | some (.ret .error state) => state == 7
  | _ => false

def observeExhaustion : Bool :=
  (panHProgWhileFuel 0 evalGuard 7 (.const 1) body).isNone

#guard observeZeroGuard
#guard observeBodyEvent
#guard observeBreak
#guard observeContinue
#guard observeNormalReentry
#guard observeFailed
#guard observeInvalidGuard
#guard observeExhaustion

def runChecks : IO Bool := do
  if observeZeroGuard then IO.println "PASS h_prog_while zero guard" else IO.println "FAIL h_prog_while zero guard"
  if observeBodyEvent then IO.println "PASS h_prog_while body event" else IO.println "FAIL h_prog_while body event"
  if observeBreak then IO.println "PASS h_prog_while break" else IO.println "FAIL h_prog_while break"
  if observeContinue then IO.println "PASS h_prog_while continue re-entry" else IO.println "FAIL h_prog_while continue re-entry"
  if observeNormalReentry then IO.println "PASS h_prog_while normal re-entry" else IO.println "FAIL h_prog_while normal re-entry"
  if observeFailed then IO.println "PASS h_prog_while failed event" else IO.println "FAIL h_prog_while failed event"
  if observeInvalidGuard then IO.println "PASS h_prog_while invalid guard" else IO.println "FAIL h_prog_while invalid guard"
  if observeExhaustion then IO.println "PASS h_prog_while fuel exhaustion" else IO.println "FAIL h_prog_while fuel exhaustion"
  pure (observeZeroGuard && observeBodyEvent && observeBreak && observeContinue &&
    observeNormalReentry && observeFailed && observeInvalidGuard && observeExhaustion)

end Flapjack.Test.PanHProgWhileParity
