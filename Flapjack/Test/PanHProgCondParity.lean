import Flapjack.PanHProgCond

/-!
# Parity checks for Pancake `h_prog_cond_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_cond_probe.out` comes from
`pan_itreeSemScript.sml:307-317`.  These checks cover true/false branch
selection, invalid guard evaluation, and the source-state response rules.
-/

namespace Flapjack.Test.PanHProgCondParity

open Flapjack

def evalGuard : Nat → Exp Nat → Option (PanValue Nat)
  | _, .const value => some (.word value)
  | _, _ => none

def thenBranch : Prog Nat := .skip
def elseBranch : Prog Nat := .tick

def observeThen : Bool :=
  match panHProgCond evalGuard 7 (.const 1) thenBranch elseBranch with
  | .vis selected state _ =>
      state == 7 &&
        match selected with
        | .skip => true
        | _ => false
  | _ => false

def observeElse : Bool :=
  match panHProgCond evalGuard 7 (.const 0) thenBranch elseBranch with
  | .vis selected state _ =>
      state == 7 &&
        match selected with
        | .tick => true
        | _ => false
  | _ => false

def observeReturned : Bool :=
  match panHProgCond evalGuard 7 (.const 1) thenBranch elseBranch with
  | .vis _ _ k =>
      match k (.returned .normal 9) with
      | .ret .normal state => state == 9
      | _ => false
  | _ => false

def observeFailed : Bool :=
  match panHProgCond evalGuard 7 (.const 1) thenBranch elseBranch with
  | .vis _ _ k =>
      match k .failed with
      | .ret .error state => state == 7
      | _ => false
  | _ => false

def observeInvalid : Bool :=
  match panHProgCond evalGuard 7 (.var .local "missing") thenBranch elseBranch with
  | .ret .error state => state == 7
  | _ => false

#guard observeThen
#guard observeElse
#guard observeReturned
#guard observeFailed
#guard observeInvalid

def runChecks : IO Bool := do
  if observeThen then IO.println "PASS h_prog_cond true branch" else IO.println "FAIL h_prog_cond true branch"
  if observeElse then IO.println "PASS h_prog_cond false branch" else IO.println "FAIL h_prog_cond false branch"
  if observeReturned then IO.println "PASS h_prog_cond returned state" else IO.println "FAIL h_prog_cond returned state"
  if observeFailed then IO.println "PASS h_prog_cond failed source state" else IO.println "FAIL h_prog_cond failed source state"
  if observeInvalid then IO.println "PASS h_prog_cond invalid guard" else IO.println "FAIL h_prog_cond invalid guard"
  pure (observeThen && observeElse && observeReturned && observeFailed && observeInvalid)

end Flapjack.Test.PanHProgCondParity
