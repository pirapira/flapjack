import Flapjack.Pancake.CrepLang

/-!
# `crepEveryExp` parity guards

Direct Lean guards for the `every_exp` traversal ported from
`cakeml/pancake/semantics/crepPropsScript.sml:1300`. The expected values are the
rows of the direct HOL probe `scripts/hol-probes/crep_every_exp_probe.out`:
`const_hit=T`, `op_not_const=F`, `op_argument_not_const=F`, `load_hit=T`,
`load_of_op_miss=F`, `always_op_nested=T`.
-/

namespace Flapjack.Test.CrepEveryExpParity

open Flapjack

/-- Holds only of constant expressions. -/
def isConst : CrepExp Nat → Bool
  | .const _ => true
  | _ => false

/-- Holds of every expression except `Op` nodes. -/
def notOp : CrepExp Nat → Bool
  | .op _ _ => false
  | _ => true

def constant : CrepExp Nat := .const 1
def constantTwo : CrepExp Nat := .const 2
def constantThree : CrepExp Nat := .const 3

theorem constHit : crepEveryExp isConst constant = true := rfl

theorem opNotConst :
    crepEveryExp isConst (.op .add [constant, constantTwo]) = false := rfl

theorem opArgumentNotConst :
    crepEveryExp isConst (.op .add [constant, .load constantThree]) = false := rfl

theorem loadHit :
    crepEveryExp notOp (.load (.load constant)) = true := rfl

theorem loadOfOpMiss :
    crepEveryExp notOp (.load (.op .add [constant])) = false := rfl

theorem alwaysOpNested :
    crepEveryExp (fun _ => true) (.op .add [.load constant, constantTwo]) = true :=
  rfl

def parityGuard : Bool :=
  crepEveryExp isConst constant &&
  !crepEveryExp isConst (.op .add [constant, constantTwo]) &&
  !crepEveryExp isConst (.op .add [constant, .load constantThree]) &&
  crepEveryExp notOp (.load (.load constant)) &&
  !crepEveryExp notOp (.load (.op .add [constant])) &&
  crepEveryExp (fun _ => true) (.op .add [.load constant, constantTwo])

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks := [
    ("Crep crepEveryExp traversal matches HOL every_exp", parityGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.CrepEveryExpParity
