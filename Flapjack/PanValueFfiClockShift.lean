import Flapjack.PanValueFfiClockSemantics

/-!
# Clock-shift prerequisite for the clocked stateful-FFI evaluators

Cake's `evaluate_add_clock_eq`
(`cakeml/pancake/semantics/panPropsScript.sml:698`) says that a successful
non-timeout run is unchanged when the input clock is increased by a constant,
with the result clock increased by the same constant.  Cake's evaluator only
decrements the clock on `While`/`Tick`/`Call`, so the shift commutes with
every clock decrement.

This file records the arithmetic fact that makes the same shift go through
for the structural-fuel-indexed clocked evaluator
(`Flapjack.PanValueFfiClockSemantics`): on a nonzero clock,
`decPanClock (clock + ck) = decPanClock clock + ck`.  It is the sole
clock-arithmetic obligation that a whole-program clock-shift theorem (the
mutually-recursive analogue of `evalPanValueFfiClock_clock_le`) needs, and it
is used to state where the missing whole-program invariant must come from.

Added while auditing Cake `evaluate_add_clock_eq` against the current
clocked evaluator; see `flapjack-pxn.11` for the structural-fuel adequacy
framework that the full shift invariant is gated on.
-/

namespace Flapjack

/-- The clock decrement commutes with adding a constant to a nonzero clock.
This is the arithmetic core of Cake `evaluate_add_clock_eq` for the clocked
evaluator. -/
theorem decPanClock_add (clock ck : Nat) (h : clock ≠ 0) :
    decPanClock (clock + ck) = decPanClock clock + ck := by
  unfold decPanClock
  omega

/-- There is exactly one clock tick from `clock` to `clock - 1`; the result
clock of a nonzero-clock `Tick` run therefore also shifts by `ck`. -/
theorem decPanClock_add_of_pos (clock ck : Nat) (h : 0 < clock) :
    decPanClock (clock + ck) = decPanClock clock + ck :=
  decPanClock_add clock ck (Nat.pos_iff_ne_zero.mp h)

end Flapjack