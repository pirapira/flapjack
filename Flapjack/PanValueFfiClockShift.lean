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

/-- Program-level clock-shift instance for the clock-spending `Tick`
constructor: on a nonzero clock, increasing the input clock by `ck` increases
the returned clock by `ck` with the same `normal` outcome.  This is the
simplest genuinely clock-spending case of the missing whole-program shift
invariant (Cake `evaluate_add_clock_eq`). -/
theorem evalPanValueFfiClockProg_tick_shift
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel ck : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hclock : clock ≠ 0) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.tick : Prog α)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
    some (.control (.normal locals globals memory ffi), decPanClock clock + ck) := by
  have hpos : clock + ck ≠ 0 := by omega
  simp only [evalPanValueFfiClockProg, if_neg hpos, Option.pure_def]
  rw [decPanClock_add clock ck hclock]

end Flapjack