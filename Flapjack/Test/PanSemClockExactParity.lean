import Flapjack.Pancake.Semantics.PanSem.ClockExact

/-!
# Parity for the exact `panSem` clock bounds (`flapjack-pxn.18.3.6.9.23`)

Build-checked fixtures for the tagged exact `fix_clock_IMP_LESS_EQ` port and the
untagged clock-bound interface in `PanSem/ClockExact.lean`, over concrete width-8
exact states. The clock semantics are the HOL `fix_clock`/`dec_clock` ones
(`panSemScript.sml:441/446/451`).
-/

namespace Flapjack.Test.PanSemClockExactParity

open Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- `mlstring` literal helper. -/
abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

/-- A concrete exact state with the given clock. -/
abbrev baseState (clock : Nat) : PanSemStateExact 8 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

/-- A clause evaluator that returns normally without changing the state. -/
def noopEvaluate : ProgHOL 8 → PanSemStateExact 8 Unit →
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  fun _ state => (none, state)

/-- A recursive `While` callback that returns normally without changing the state. -/
def noopRecurse : PanSemStateExact 8 Unit →
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  fun state => (none, state)

/-- An expression evaluator that fails, selecting the error branch. -/
def noopEvalExpression : PanSemStateExact 8 Unit → ExpHOL 8 → Option (ValueHOL 8) :=
  fun _ _ => none

/-- The tagged exact `fix_clock_IMP_LESS_EQ` instantiated at clock 9 / new clock 4. -/
example :
    (fixClockHOLExact (baseState 9) ((none : Option Nat), baseState 4)).2.clock ≤
      (baseState 9).clock :=
  fixClockHOLExact_IMP_LESS_EQ (baseState 9) (none : Option Nat)
    (fixClockHOLExact (baseState 9) ((none : Option Nat), baseState 4)).2
    ((none : Option Nat), baseState 4) rfl

/-- The untagged `fix_clock` bound keeps a smaller new clock and clamps a larger one. -/
example : ((fixClockHOLExact (baseState 9) ((none : Option Nat), baseState 4)).2.clock,
    (fixClockHOLExact (baseState 2) ((none : Option Nat), baseState 7)).2.clock) =
    (4, 2) := rfl

/-- The untagged `dec_clock` bound. -/
example : (decClockHOLExact (baseState 5)).clock ≤ (baseState 5).clock :=
  decClockHOLExact_clock_le (baseState 5)

/-- `set_var`/`set_kvar` keep the clock. -/
example : (setVarHOLExact (ml "x") (.val (.word 3)) (baseState 5)).clock = 5 :=
  setVarHOLExact_clock (ml "x") (.val (.word 3)) (baseState 5)

example : (setKvarHOLExact VarKind.global (ml "g") (.val (.word 3)) (baseState 5)).clock = 5 :=
  setKvarHOLExact_clock VarKind.global (ml "g") (.val (.word 3)) (baseState 5)

/-- `Tick` keeps the clock at both the timeout and the normal branch. -/
example : (tickStepHOLExact (baseState 0)).2.clock ≤ (baseState 0).clock :=
  tickStepHOLExact_clock_le (baseState 0)

example : (tickStepHOLExact (baseState 5)).2.clock ≤ (baseState 5).clock :=
  tickStepHOLExact_clock_le (baseState 5)

/-- The `If`/`Seq`/`While` steps keep the clock. -/
example :
    (ifStepHOLExact (baseState 5) (.const 1) .skip .skip noopEvalExpression
      noopEvaluate).2.clock ≤ (baseState 5).clock :=
  ifStepHOLExact_clock_le (baseState 5) (.const 1) .skip .skip noopEvalExpression
    noopEvaluate (fun _ _ => Nat.le_refl _)

example :
    (seqStepHOLExact (baseState 5) .skip .skip noopEvaluate).2.clock ≤
      (baseState 5).clock :=
  seqStepHOLExact_clock_le (baseState 5) .skip .skip noopEvaluate
    (fun _ _ => Nat.le_refl _)

example :
    (whileStepHOLExact (baseState 5) (.const 1) .skip noopEvalExpression noopEvaluate
      noopRecurse).2.clock ≤ (baseState 5).clock :=
  whileStepHOLExact_clock_le (baseState 5) (.const 1) .skip noopEvalExpression
    noopEvaluate noopRecurse (fun _ => Nat.le_refl _)

#guard (fixClockHOLExact (baseState 9) ((none : Option Nat), baseState 4)).2.clock == 4
#guard (fixClockHOLExact (baseState 2) ((none : Option Nat), baseState 7)).2.clock == 2
#guard (tickStepHOLExact (baseState 0)).2.clock == 0
#guard (tickStepHOLExact (baseState 5)).2.clock == 4

/-- The parity checks for the exact clock bounds. -/
def clockBoundsGuard : Bool :=
  ((fixClockHOLExact (baseState 9) ((none : Option Nat), baseState 4)).2.clock == 4) &&
    ((fixClockHOLExact (baseState 2) ((none : Option Nat), baseState 7)).2.clock == 2) &&
    ((tickStepHOLExact (baseState 0)).2.clock == 0) &&
    ((tickStepHOLExact (baseState 5)).2.clock == 4)

#eval clockBoundsGuard

#guard clockBoundsGuard

/-- Run the exact clock-bound parity checks. -/
def runChecks : IO Bool := do
  if clockBoundsGuard then
    IO.println "PASS exact panSem fix_clock/dec_clock/control-step clock bounds"
    pure true
  else
    IO.println "FAIL exact panSem fix_clock/dec_clock/control-step clock bounds"
    pure false

end Flapjack.Test.PanSemClockExactParity
