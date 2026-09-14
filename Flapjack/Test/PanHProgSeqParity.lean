import Flapjack.PanHProgSeq

/-!
# Parity checks for Pancake `h_prog_seq_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_seq_probe.out` comes from
`pan_itreeSemScript.sml:240-254`.  These checks cover first-event emission,
second-event sequencing after a normal result, and the source-state behavior
of failed and non-normal responses.
-/

namespace Flapjack.Test.PanHProgSeqParity

open Flapjack

def first : Prog Nat := .skip
def second : Prog Nat := .return (.const 0)
def sequence : PanHProgSeqTree Nat Nat := panHProgSeq 7 first second

def observeSecondEvent : Bool :=
  match sequence with
  | .vis _ firstState k =>
      firstState == 7 &&
        match k (.returned .normal 8) with
        | .vis returnedSecond secondState _ =>
            (match returnedSecond with
             | .return (.const 0) => true
             | _ => false) && secondState == 8
        | _ => false
  | _ => false

def observeSecondNormal : Bool :=
  match sequence with
  | .vis _ _ k =>
      match k (.returned .normal 8) with
      | .vis _ _ secondK =>
          match secondK (.returned .normal 9) with
          | .ret .normal state => state == 9
          | _ => false
      | _ => false
  | _ => false

def observeFirstError : Bool :=
  match sequence with
  | .vis _ _ k =>
      match k (.returned .error 8) with
      | .ret .error state => state == 8
      | _ => false
  | _ => false

def observeFirstFailure : Bool :=
  match sequence with
  | .vis _ _ k =>
      match k .failed with
      | .ret .error state => state == 7
      | _ => false
  | _ => false

def observeSecondFailure : Bool :=
  match sequence with
  | .vis _ _ k =>
      match k (.returned .normal 8) with
      | .vis _ _ secondK =>
          match secondK .failed with
          | .ret .error state => state == 7
          | _ => false
      | _ => false
  | _ => false

#guard observeSecondEvent
#guard observeSecondNormal
#guard observeFirstError
#guard observeFirstFailure
#guard observeSecondFailure

def runChecks : IO Bool := do
  if observeSecondEvent then
    IO.println "PASS h_prog_seq emits second program event"
  else
    IO.println "FAIL h_prog_seq emits second program event"
  if observeSecondNormal then
    IO.println "PASS h_prog_seq normal result"
  else
    IO.println "FAIL h_prog_seq normal result"
  if observeFirstError then
    IO.println "PASS h_prog_seq first error state"
  else
    IO.println "FAIL h_prog_seq first error state"
  if observeFirstFailure then
    IO.println "PASS h_prog_seq first failure state"
  else
    IO.println "FAIL h_prog_seq first failure state"
  if observeSecondFailure then
    IO.println "PASS h_prog_seq second failure uses source state"
  else
    IO.println "FAIL h_prog_seq second failure uses source state"
  pure (observeSecondEvent && observeSecondNormal && observeFirstError &&
    observeFirstFailure && observeSecondFailure)

end Flapjack.Test.PanHProgSeqParity
