import Flapjack.HolRef
import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement
import Flapjack.Misc.BinaryIeeeConvert

/-!
# HOL `binary_ieee` rounding and `float_sqrt` over Mathlib reals

Literal renderings, over Mathlib's `ℝ` as the carrier of HOL `real`, of the HOL
`binary_ieeeScript.sml` definitions that `fp64_sqrt` passes through:
`float_value`/`float_to_real` (41-63), `is_closest`/`closest_such`/`closest`
(253-353), `largest`/`threshold` (355-365), `round` (411-443), `float_round`
(505-515), `float_round_with_flags` (517-532) and `float_sqrt` (574-585), with
HOL `sqrt` as `Real.sqrt`. Unlike the sqrt-specialised real renderings of
`RoundAgreement` (which read every comparison directly against `sqrt r` and drop
the `abs` that `sqrt r ≥ 0` makes redundant), these take an arbitrary real
argument and keep every HOL clause, `abs` and flag test as written; HOL's choice
operator is `Classical.epsilon` and propositions are decided classically.

The theorems prove that at `x = Real.sqrt r` these literal renderings coincide
with the sqrt-specialised real renderings, so by `holFloatSqrt_agreement` the
executed rational-cut `holFloatSqrt` equals the literal real `holFloatSqrtR`
for every rounding mode and input, with no supplied agreement, radicand,
success or target premise. The generated `fp64_sqrt` over this carrier and its
agreement are in `Flapjack.Misc.MachineIeee.SqrtReal`.

Everything is proved inside Lean; no HOL-to-Lean equivalence is assumed or
established (Mathlib `ℝ` as HOL `real` is the standard carrier reading). Since
the `HolFloat t w` carrier binds HOL's positive type dimensions as
`[NeZero t] [NeZero w]` (bead `flapjack-h29l.6.2.12`), the generic arbitrary-real
`is_closest`, `closest_such`, `closest`, `round`, `float_round`,
`float_round_with_flags`, `real_to_float`, `real_to_float_with_flags` and
`float_sqrt` renderings are source-tagged (beads `flapjack-h29l.6.2.9`,
`flapjack-h29l.6.3.1.1`, `flapjack-h29l.6.3.2.3`); their `Rat`/cut counterparts
stay untagged. `largest`/`threshold` stay untagged (two word-free type
dimensions, no reviewed qualifier), and `holFloatToRealR`/`holFloatValueR`
duplicate the tagged `Rat` renderings of the always-rational float values. In
`float_sqrt` HOL `sqrt` is `Real.sqrt`; it is applied only to the value of a
float with sign `0w`, which is nonnegative, where both are the nonnegative
square root. The executed compiler continues using the cut rendering, with the
unconditional equality below connecting it to the reviewed binary64 real
specification.
-/

namespace Flapjack

open Classical

/-- HOL `float_value = Float real | Infinity | NaN` (`binary_ieeeScript.sml:41-42`)
with HOL `real` as Mathlib `ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_value"
  (reals_as_rational_cuts)]
inductive HolFloatValueR where
  | float (r : ℝ)
  | infinity
  | nan

/-- HOL `float_to_real_def` (`binary_ieeeScript.sml:47-56`) over `ℝ`. -/
noncomputable def holFloatToRealR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : ℝ :=
  let s : ℝ := (-1) ^ x.sign.toNat
  if x.exponent = 0 then
    s * (2 / 2 ^ holFloatBias w) * ((x.significand.toNat : ℝ) / 2 ^ t)
  else
    s * (2 ^ x.exponent.toNat / 2 ^ holFloatBias w) * (1 + (x.significand.toNat : ℝ) / 2 ^ t)

/-- HOL `float_value_def` (`binary_ieeeScript.sml:58-63`) over `ℝ`. -/
noncomputable def holFloatValueR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) : HolFloatValueR :=
  if x.exponent = BitVec.allOnes w then
    if x.significand = 0 then .infinity else .nan
  else .float (holFloatToRealR x)

/-- HOL `is_closest_def` (`binary_ieeeScript.sml:253-257`) over `ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "is_closest_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
def holIsClosestR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (x : ℝ) (a : HolFloat t w) : Prop :=
  s a ∧ ∀ b, s b → |holFloatToRealR a - x| ≤ |holFloatToRealR b - x|

/-- HOL `closest_such_def` (`binary_ieeeScript.sml:347-350`) over `ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "closest_such_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holClosestSuchR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (p : HolFloat t w → Prop)
    (s : HolFloat t w → Prop) (x : ℝ) : HolFloat t w :=
  Classical.epsilon (fun a => holIsClosestR s x a ∧ ∀ b, holIsClosestR s x b ∧ p b → p a)

/-- HOL `closest_def` (`binary_ieeeScript.sml:352-353`) over `ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "closest_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holClosestR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (x : ℝ) : HolFloat t w :=
  holClosestSuchR (fun _ => True) s x

/-- HOL `largest_def` (`binary_ieeeScript.sml:355-359`) over arbitrary Mathlib
reals. The two independent type dimensions are numeric only: `t` retains
`dimindex (:'t)` and `w` controls UINT_MAX/INT_MAX, each with its own NeZero.
No word-valued carrier, extra bound, or rational-domain restriction occurs. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
  (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts)]
noncomputable def holFloatLargestR (t : Nat) (w : Nat) [NeZero t] [NeZero w] : ℝ :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ t : ℝ)⁻¹)

/-- HOL `threshold_def` (`binary_ieeeScript.sml:361-365`) over arbitrary Mathlib
reals. The two independent type dimensions are numeric only: `t` retains
`dimindex (:'t)` and `w` controls UINT_MAX/INT_MAX, each with its own NeZero.
No word-valued carrier, extra bound, or rational-domain restriction occurs. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "threshold_def"
  (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts)]
noncomputable def holFloatThresholdR (t : Nat) (w : Nat) [NeZero t] [NeZero w] : ℝ :=
  (2 ^ (holUintMax w - 1) / 2 ^ holFloatBias w) * (2 - (2 ^ (t + 1) : ℝ)⁻¹)

/-- HOL `round_def` (`binary_ieeeScript.sml:411-443`) over `ℝ`, all four modes. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "round_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holRoundR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : ℝ) : HolFloat t w :=
  match mode with
  | .roundTiesToEven =>
      let th := holFloatThresholdR t w
      if x ≤ -th then holFloatMinusInfinity t w
      else if x ≥ th then holFloatPlusInfinity t w
      else holClosestSuchR (fun a => a.significand.getLsbD 0 = false)
        (fun a => holFloatIsFinite a = true) x
  | .roundTowardZero =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ |holFloatToRealR a| ≤ |x|) x
  | .roundTowardPositive =>
      let th := holFloatLargestR t w
      if x < -th then holFloatBottom t w
      else if x > th then holFloatPlusInfinity t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ holFloatToRealR a ≥ x) x
  | .roundTowardNegative =>
      let th := holFloatLargestR t w
      if x < -th then holFloatMinusInfinity t w
      else if x > th then holFloatTop t w
      else holClosestR (fun a => holFloatIsFinite a = true ∧ holFloatToRealR a ≤ x) x

/-- HOL `float_round_def` (`binary_ieeeScript.sml:507-515`) over `ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_round_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatRoundR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toneg : Bool) (r : ℝ) :
    HolFloat t w :=
  let x : HolFloat t w := holRoundR mode r
  if holFloatIsZero x then
    if toneg then holFloatMinusZero t w else holFloatPlusZero t w
  else x

/-- HOL `float_round_with_flags_def` (`binary_ieeeScript.sml:517-532`) over `ℝ`;
`a = abs r` and `inexact = (float_value x ≠ Float r)` as in HOL. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_round_with_flags_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatRoundWithFlagsR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toNeg : Bool)
    (r : ℝ) : HolFloatFlags × HolFloat t w :=
  let x : HolFloat t w := holFloatRoundR mode toNeg r
  let a := |r|
  let inexact := decide (holFloatValueR x ≠ .float r)
  ({ holClearFlags with
      overflow := holFloatIsInfinite x || decide ((2 : ℝ) ^ holIntMin w ≤ a)
      underflowBeforeRounding := inexact && decide (a < 2 / 2 ^ holFloatBias w)
      underflowAfterRounding := inexact &&
        decide ((holFloatRoundR mode toNeg r : HolFloat t (w + 1)).exponent ≤
          BitVec.ofNat (w + 1) (holIntMin w))
      precision := inexact }, x)

/-- HOL `real_to_float_def` (`binary_ieeeScript.sml:539-541`) over `ℝ`:
`real_to_float m = float_round m (m = roundTowardNegative)`, for an arbitrary
real argument (HOL's point-free equation applied to `r`). The `Rat`
`holRealToFloat` is its restriction to rational inputs. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "real_to_float_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holRealToFloatR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (r : ℝ) :
    HolFloat t w :=
  holFloatRoundR mode (decide (mode = .roundTowardNegative)) r

/-- HOL `real_to_float_with_flags_def` (`binary_ieeeScript.sml:543-546`) over
`ℝ`: `float_round_with_flags m (m = roundTowardNegative)`, applied to `r`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "real_to_float_with_flags_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holRealToFloatWithFlagsR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (r : ℝ) : HolFloatFlags × HolFloat t w :=
  holFloatRoundWithFlagsR mode (decide (mode = .roundTowardNegative)) r

/-- HOL `float_to_int_def` (`binary_ieeeScript.sml:555-572`) over `ℝ`: a finite
float `Float r` is converted by the mode (ties-to-even takes `f = INT_FLOOR r`
when `abs (r - real_of_int f) < 1/2`, or `= 1/2` with `EVEN (Num (ABS f))`, and
`INT_CEILING r` otherwise; toward positive the ceiling; toward negative the
floor; toward zero the ceiling for sign `1w`, else the floor); infinities and
NaNs give `NONE`. HOL `INT_FLOOR`/`INT_CEILING` are `Int.floor`/`Int.ceil` on
`ℝ`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_to_int_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatToIntR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x : HolFloat t w) : Option Int :=
  match holFloatValueR x with
  | .float r =>
      some (match mode with
        | .roundTiesToEven =>
            let f := ⌊r⌋
            let df := |r - (f : ℝ)|
            if df < 1 / 2 ∨ (df = 1 / 2 ∧ f.natAbs % 2 = 0) then f else ⌈r⌉
        | .roundTowardPositive => ⌈r⌉
        | .roundTowardNegative => ⌊r⌋
        | .roundTowardZero => if x.sign = 1 then ⌈r⌉ else ⌊r⌋)
  | _ => none

/-- HOL `float_sqrt_def` (`binary_ieeeScript.sml:574-585`) over `ℝ`, with HOL `sqrt`
as `Real.sqrt`. -/
@[hol "HOL/src/floating-point/binary_ieeeScript.sml" "float_sqrt_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def holFloatSqrtR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : HolFloat t w) :
    HolFloatFlags × HolFloat t w :=
  if x.sign = 0 then
    match holFloatValueR x with
    | .nan => (holCheckForSignalling [x], holFloatSomeQnan (.fpSqrt mode x))
    | .infinity => (holClearFlags, holFloatPlusInfinity t w)
    | .float r => holFloatRoundWithFlagsR mode false (Real.sqrt r)
  else if x = holFloatMinusZero t w then (holClearFlags, holFloatMinusZero t w)
  else (holInvalidopFlags, holFloatSomeQnan (.fpSqrt mode x))

/-! ## The real carrier at `Real.sqrt r` is the sqrt-specialised real rendering -/

theorem holFloatToRealR_eq_cast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) :
    holFloatToRealR x = (holFloatToReal x : ℝ) := by
  unfold holFloatToRealR holFloatToReal
  split <;> push_cast <;> rfl

theorem holFloatValueR_eq {t : Nat} {w : Nat} [NeZero t] [NeZero w] (x : HolFloat t w) :
    holFloatValueR x = match holFloatValue x with
      | .float q => .float (q : ℝ)
      | .infinity => .infinity
      | .nan => .nan := by
  unfold holFloatValueR holFloatValue
  split
  · split <;> rfl
  · simp [holFloatToRealR_eq_cast]

theorem holFloatLargestR_eq_cast (t : Nat) (w : Nat) [NeZero t] [NeZero w] :
    holFloatLargestR t w = (holFloatLargest t w : ℝ) := by
  unfold holFloatLargestR holFloatLargest; push_cast; rfl

theorem holFloatThresholdR_eq_cast (t : Nat) (w : Nat) [NeZero t] [NeZero w] :
    holFloatThresholdR t w = (holFloatThreshold t w : ℝ) := by
  unfold holFloatThresholdR holFloatThreshold; push_cast; rfl

theorem holRatAbs_cast (q : Rat) : ((holRatAbs q : Rat) : ℝ) = |(q : ℝ)| := by
  unfold holRatAbs
  split
  · rename_i h
    have : (q : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg this]; push_cast; rfl
  · rename_i h
    have : (0 : ℝ) ≤ q := by exact_mod_cast (not_lt.mp h)
    rw [abs_of_nonneg this]

theorem holIsClosestR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (r : Rat) (a : HolFloat t w) :
    holIsClosestR s (realSqrtOfRat r) a ↔ holIsClosestSqrtReal s r a := by
  unfold holIsClosestR holIsClosestSqrtReal realSqrtDistLe
  simp only [holFloatToRealR_eq_cast]

theorem holClosestSuchR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (p s : HolFloat t w → Prop) (r : Rat) :
    holClosestSuchR p s (realSqrtOfRat r) = holClosestSuchSqrtReal p s r := by
  unfold holClosestSuchR holClosestSuchSqrtReal
  congr 1
  funext a
  simp only [holIsClosestR_sqrt]

theorem holClosestR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (r : Rat) :
    holClosestR s (realSqrtOfRat r) = holClosestSqrtReal s r :=
  holClosestSuchR_sqrt (fun _ => True) s r

/-- HOL `round mode (sqrt r)` over the real carrier is the sqrt-specialised real
rendering, for every mode and every rational `r` (`Real.sqrt` is nonnegative). -/
theorem holRoundR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (r : Rat) :
    (holRoundR mode (realSqrtOfRat r) : HolFloat t w) = holRoundSqrtReal mode r := by
  have hs : |realSqrtOfRat r| = realSqrtOfRat r := abs_of_nonneg (realSqrtOfRat_nonneg r)
  cases mode with
  | roundTiesToEven =>
      simp only [holRoundR, holRoundSqrtReal, holFloatThresholdR_eq_cast, holClosestSuchR_sqrt]
      push_cast; rfl
  | roundTowardZero =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast, hs]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast, holRatAbs_cast]
  | roundTowardPositive =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast]
  | roundTowardNegative =>
      simp only [holRoundR, holRoundSqrtReal, holFloatLargestR_eq_cast]
      push_cast
      congr 2
      rw [holClosestR_sqrt]
      congr 1
      funext a
      rw [holFloatToRealR_eq_cast]

theorem holFloatRoundR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toneg : Bool) (r : Rat) :
    (holFloatRoundR mode toneg (realSqrtOfRat r) : HolFloat t w) =
      holFloatRoundSqrtReal mode toneg r := by
  unfold holFloatRoundR holFloatRoundSqrtReal
  rw [holRoundR_sqrt mode r]

theorem holFloatRoundWithFlagsR_sqrt {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toNeg : Bool) (r : Rat) :
    (holFloatRoundWithFlagsR mode toNeg (realSqrtOfRat r) : HolFloatFlags × HolFloat t w) =
      holFloatRoundWithFlagsSqrtReal mode toNeg r := by
  have hs : |realSqrtOfRat r| = realSqrtOfRat r := abs_of_nonneg (realSqrtOfRat_nonneg r)
  unfold holFloatRoundWithFlagsR holFloatRoundWithFlagsSqrtReal
  simp only [holFloatRoundR_sqrt mode toNeg r, hs, holFloatValueR_eq]
  push_cast
  cases holFloatValue (holFloatRoundSqrtReal mode toNeg r : HolFloat t w) <;> simp

/-- HOL `float_sqrt mode` over the real carrier is the sqrt-specialised real
rendering, for every mode and input. -/
theorem holFloatSqrtR_eq_real {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : HolFloat t w) :
    holFloatSqrtR mode x = holFloatSqrtReal mode x := by
  unfold holFloatSqrtR holFloatSqrtReal
  rw [holFloatValueR_eq]
  cases holFloatValue x with
  | nan => rfl
  | infinity => rfl
  | float q =>
      simp only [← holFloatRoundWithFlagsR_sqrt]
      rfl

/-- The executed rational-cut `float_sqrt` equals the literal real-carrier HOL
`float_sqrt`, for every rounding mode and input (no premise). -/
theorem holFloatSqrt_eq_holFloatSqrtR {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (x : HolFloat t w) :
    holFloatSqrt mode x = holFloatSqrtR mode x :=
  (holFloatSqrt_agreement mode x).trans (holFloatSqrtR_eq_real mode x).symm

/-! ## At rational arguments the real carrier is the `Rat` rendering

The executed `Rat` renderings of `round`, `float_round`,
`float_round_with_flags` and `real_to_float` are the restrictions of the
tagged arbitrary-real ports to rational arguments, for every mode, with no
range, success or agreement premise. -/

theorem holIsClosestR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (q : Rat)
    (a : HolFloat t w) :
    holIsClosestR s (q : ℝ) a ↔ holIsClosest s q a := by
  have key : ∀ u v : Rat, (|(u : ℝ) - q| ≤ |(v : ℝ) - q|) ↔ holRatAbs (u - q) ≤ holRatAbs (v - q) := by
    intro u v
    rw [← Rat.cast_sub, ← Rat.cast_sub, ← holRatAbs_cast, ← holRatAbs_cast, Rat.cast_le]
  unfold holIsClosestR holIsClosest
  simp only [holFloatToRealR_eq_cast, key]

theorem holClosestSuchR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (p s : HolFloat t w → Prop) (q : Rat) :
    holClosestSuchR p s (q : ℝ) = holClosestSuch p s q := by
  unfold holClosestSuchR holClosestSuch
  simp only [holIsClosestR_ratCast]

theorem holClosestR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (s : HolFloat t w → Prop) (q : Rat) :
    holClosestR s (q : ℝ) = holClosest s q :=
  holClosestSuchR_ratCast (fun _ => True) s q

theorem holRoundR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (q : Rat) :
    (holRoundR mode (q : ℝ) : HolFloat t w) = holRound mode q := by
  cases mode <;>
    simp only [holRoundR, holRound, holFloatThresholdR_eq_cast, holFloatLargestR_eq_cast,
      holFloatToRealR_eq_cast, ← holRatAbs_cast, ← Rat.cast_neg, Rat.cast_le, Rat.cast_lt,
      holClosestR_ratCast, holClosestSuchR_ratCast]

theorem holFloatRoundR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (toneg : Bool)
    (q : Rat) :
    (holFloatRoundR mode toneg (q : ℝ) : HolFloat t w) = holFloatRound mode toneg q := by
  unfold holFloatRoundR holFloatRound
  rw [holRoundR_ratCast]

theorem holFloatRoundWithFlagsR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (toNeg : Bool) (q : Rat) :
    (holFloatRoundWithFlagsR mode toNeg (q : ℝ) : HolFloatFlags × HolFloat t w) =
      holFloatRoundWithFlags mode toNeg q := by
  have ha : |(q : ℝ)| = ((holRatAbs q : Rat) : ℝ) := (holRatAbs_cast q).symm
  have h1 : ((2 : ℝ) ^ holIntMin w ≤ ((holRatAbs q : Rat) : ℝ)) ↔
      ((2 : Rat) ^ holIntMin w ≤ holRatAbs q) := by
    constructor <;> intro h <;> exact_mod_cast h
  have h2 : (((holRatAbs q : Rat) : ℝ) < (2 : ℝ) / (2 : ℝ) ^ holFloatBias w) ↔
      (holRatAbs q < (2 : Rat) / (2 : Rat) ^ holFloatBias w) := by
    have hc : (2 : ℝ) / (2 : ℝ) ^ holFloatBias w =
        (((2 : Rat) / (2 : Rat) ^ holFloatBias w : Rat) : ℝ) := by
      push_cast; rfl
    rw [hc, Rat.cast_lt]
  unfold holFloatRoundWithFlagsR holFloatRoundWithFlags
  simp only [holFloatRoundR_ratCast, holFloatValueR_eq, ha, h1, h2]
  cases holFloatValue (holFloatRound mode toNeg q : HolFloat t w) <;> simp

/-- The general-real `real_to_float` at a rational is the executed `Rat`
`holRealToFloat` (used by `int_to_fp64`), for every mode. -/
theorem holRealToFloatR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding) (q : Rat) :
    (holRealToFloatR mode (q : ℝ) : HolFloat t w) = holRealToFloat mode q :=
  holFloatRoundR_ratCast mode _ q

theorem holRealToFloatWithFlagsR_ratCast {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (q : Rat) :
    (holRealToFloatWithFlagsR mode (q : ℝ) : HolFloatFlags × HolFloat t w) =
      holFloatRoundWithFlags mode (decide (mode = .roundTowardNegative)) q :=
  holFloatRoundWithFlagsR_ratCast mode _ q

/-- The arbitrary-real `float_to_int` equals the executed `Rat` rendering
`holFloatToInt` on every float and mode (float values are rational). -/
theorem holFloatToIntR_eq {t : Nat} {w : Nat} [NeZero t] [NeZero w] (mode : HolRounding)
    (x : HolFloat t w) :
    holFloatToIntR mode x = holFloatToInt mode x := by
  unfold holFloatToIntR holFloatToInt
  rw [holFloatValueR_eq]
  cases holFloatValue x with
  | nan => rfl
  | infinity => rfl
  | float q =>
      have hd : |(q : ℝ) - ((⌊q⌋ : ℤ) : ℝ)| = ((holRatAbs (q - (⌊q⌋ : ℚ)) : ℚ) : ℝ) := by
        rw [holRatAbs_cast]; push_cast; rfl
      have c : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; rfl
      have h1 : (((holRatAbs (q - (⌊q⌋ : ℚ)) : ℚ) : ℝ) < 1 / 2) ↔
          (holRatAbs (q - (⌊q⌋ : ℚ)) < 1 / 2) := by
        rw [c, Rat.cast_lt]
      have h2 : (((holRatAbs (q - (⌊q⌋ : ℚ)) : ℚ) : ℝ) = 1 / 2) ↔
          (holRatAbs (q - (⌊q⌋ : ℚ)) = 1 / 2) := by
        rw [c, Rat.cast_inj]
      have hf : ⌊q⌋ = q.floor := rfl
      have hc : ⌈q⌉ = q.ceil := by
        rw [Rat.ceil_eq_neg_floor_neg, show (-q).floor = ⌊-q⌋ from rfl, Int.floor_neg, neg_neg]
      cases mode with
      | roundTiesToEven =>
          simp only [Rat.floor_cast, Rat.ceil_cast, hd, h1, h2]
          rw [hf, hc]
      | roundTowardPositive => simp only [Rat.ceil_cast, hc]
      | roundTowardNegative => simp only [Rat.floor_cast, hf]
      | roundTowardZero => simp only [Rat.floor_cast, Rat.ceil_cast, hf, hc]

end Flapjack
