import Flapjack.HolRef
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Semantics.CrepSem.Eval

/-! Theorem counterparts and Flapjack support for CakeML's
    `crep_arithProofScript.sml`. The tagged `dest_const_def` and
    `dest_const_thm` statements use the canonical positive-width HOL word
    carrier `Fin width → Bool`, with `[NeZero width]`. They do not quantify
    over arbitrary value carriers or arbitrary finite-index types. Separate
    untagged helpers support explicit `HolFiniteDimension` transports and
    executable RISC-V `BitVec` arithmetic. -/

namespace Flapjack

/-! The finite-index word instance is transported through `BitVec`, so the
    power-of-two recognizer returns the same exponent after representation
    conversion. This is the arithmetic-simplifier bridge needed before its
    preservation proof can be lifted from `BitVec` to finite-index HOL words. -/
/-- Flapjack-only finite-word transport lemma for the executable recognizer;
    HOL has no corresponding declaration because its recognizer already acts
    directly on the polymorphic word type. -/
private theorem crepDest2ExpFuel_holWordBits {width : Nat}
    (fuel start : Nat) (word : Fin width → Bool) :
    crepDest2ExpFuel fuel start word =
      crepDest2ExpFuel fuel start (holWordBitsToBitVec word) := by
  induction fuel generalizing start word with
  | zero => simp [crepDest2ExpFuel]
  | succ fuel ih =>
      have hzero : (word == (0 : Fin width → Bool)) =
          (holWordBitsToBitVec word == (0 : BitVec width)) := by
        simp
      have hone : (word == (1 : Fin width → Bool)) =
          (holWordBitsToBitVec word == (1 : BitVec width)) := by
        simp
      have hlow : (AndOp.and word 1 != (0 : Fin width → Bool)) =
          (AndOp.and (holWordBitsToBitVec word) 1 != (0 : BitVec width)) := by
        change (!(AndOp.and word 1 == (0 : Fin width → Bool))) =
          (!(AndOp.and (holWordBitsToBitVec word) 1 == (0 : BitVec width)))
        rw [holWordBitsToBitVec_beq]
        simp [holWordBitsToBitVec_andOp, holWordBitsToBitVec_one,
          holWordBitsToBitVec_zero]
      simp only [crepDest2ExpFuel, hzero, hone, hlow]
      rw [ih (start + 1) (ShiftRight.shiftRight word 1)]
      simp only [holWordBitsToBitVec_shiftRight, holWordBitsToBitVec_one]
      rfl

/-- Flapjack-only width-bounded wrapper around the finite-word recognizer
transport lemma; it has no separate HOL declaration. -/
private theorem crepDest2Exp_holWordBits {width : Nat}
    (start : Nat) (word : Fin width → Bool) :
    crepDest2Exp start word = crepDest2Exp start (holWordBitsToBitVec word) := by
  change crepDest2ExpFuel (width + 1) start word =
    crepDest2ExpFuel (width + 1) start (holWordBitsToBitVec word)
  exact crepDest2ExpFuel_holWordBits (width + 1) start word

/-! The recognizer transport now works for any explicitly enumerated HOL
    finite dimension, rather than only the canonical `Fin width` presentation.
    The enumeration record is the representation of HOL's finite nonempty
    dimension type in Lean core. -/
private theorem crepDest2ExpFuel_holFiniteDimension {ι : Type u}
    [dimension : HolFiniteDimension ι] (fuel start : Nat) (word : ι → Bool) :
    crepDest2ExpFuel fuel start word =
      crepDest2ExpFuel fuel start (holWordToBitVec dimension word) := by
  induction fuel generalizing start word with
  | zero => simp [crepDest2ExpFuel]
  | succ fuel ih =>
      have hzero : (word == (0 : ι → Bool)) =
          (holWordToBitVec dimension word == (0 : BitVec dimension.width)) := by
        change (holWordToBitVec dimension word ==
            holWordToBitVec dimension (0 : ι → Bool)) =
          (holWordToBitVec dimension word == (0 : BitVec dimension.width))
        rw [holFiniteWordToBitVec_zero]
      have hone : (word == (1 : ι → Bool)) =
          (holWordToBitVec dimension word == (1 : BitVec dimension.width)) := by
        change (holWordToBitVec dimension word ==
            holWordToBitVec dimension (1 : ι → Bool)) =
          (holWordToBitVec dimension word == (1 : BitVec dimension.width))
        rw [holFiniteWordToBitVec_one]
      have hlow : (AndOp.and word 1 != (0 : ι → Bool)) =
          (AndOp.and (holWordToBitVec dimension word) 1 !=
            (0 : BitVec dimension.width)) := by
        change (!(holWordToBitVec dimension (AndOp.and word 1) ==
            holWordToBitVec dimension (0 : ι → Bool))) =
          (!(AndOp.and (holWordToBitVec dimension word) 1 ==
            (0 : BitVec dimension.width)))
        rw [holFiniteWordToBitVec_and, holFiniteWordToBitVec_one,
          holFiniteWordToBitVec_zero]
      simp only [crepDest2ExpFuel, hzero, hone, hlow]
      rw [ih (start + 1) (ShiftRight.shiftRight word 1)]
      rw [holFiniteWordToBitVec_shiftRight, holFiniteWordToBitVec_one]

private theorem crepDest2Exp_holFiniteDimension {ι : Type u}
    [dimension : HolFiniteDimension ι] (start : Nat) (word : ι → Bool) :
    crepDest2Exp start word =
      crepDest2Exp start (holWordToBitVec dimension word) := by
  change crepDest2ExpFuel (dimension.width + 1) start word =
    crepDest2ExpFuel (dimension.width + 1) start (holWordToBitVec dimension word)
  exact crepDest2ExpFuel_holFiniteDimension
    (dimension.width + 1) start word

/-! This adapter law keeps the arithmetic pass natural under the canonical
    representation of an arbitrary finite bit index. It is the remaining
    bridge needed to lift the source-shaped evaluator proof from BitVec to
    `Fin width → Bool`; it is Flapjack-only infrastructure. -/
private theorem crepMulConst_holWordBits {width : Nat} [NeZero width]
    (expression : CrepExp (Fin width → Bool)) (constant : Fin width → Bool) :
    mapCrepExpWord holWordBitsToBitVec
        (crepMulConst (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
          expression constant) =
      crepMulConst (BitVec.ofNat width)
        (mapCrepExpWord holWordBitsToBitVec expression)
        (holWordBitsToBitVec constant) := by
  unfold crepMulConst
  have hzero : (constant == (0 : Fin width → Bool)) =
      (holWordBitsToBitVec constant == (0 : BitVec width)) := by simp
  have hone : (constant == (1 : Fin width → Bool)) =
      (holWordBitsToBitVec constant == (1 : BitVec width)) := by simp
  rw [hzero, hone]
  by_cases hzero : holWordBitsToBitVec constant == 0
  · have hzeroEq : holWordBitsToBitVec constant = 0 := of_decide_eq_true hzero
    simp [hzeroEq, mapCrepExpWord]
  · by_cases hone : holWordBitsToBitVec constant == 1
    · have honeEq : holWordBitsToBitVec constant = 1 := of_decide_eq_true hone
      simp [honeEq, NeZero.ne width]
    · simp only [if_neg hzero, if_neg hone]
      rw [crepDest2Exp_holWordBits]
      cases crepDest2Exp 0 (holWordBitsToBitVec constant) with
      | none => simp [mapCrepExpWord]
      | some exponent =>
          simp only [mapCrepExpWord]
          exact congrArg (fun word => CrepExp.shift Shift.lsl
            (mapCrepExpWord holWordBitsToBitVec expression) (CrepExp.const word))
            (holWordBitsToBitVec_bitVecToHolWordBits _)

private theorem crepMulConst_holFiniteDimension {ι : Type}
    [dimension : HolFiniteDimension ι] (expression : CrepExp (ι → Bool))
    (constant : ι → Bool) :
    mapCrepExpWord (holWordToBitVec dimension)
        (crepMulConst
          (fun value => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width value)) expression constant) =
      crepMulConst (BitVec.ofNat dimension.width)
        (mapCrepExpWord (holWordToBitVec dimension) expression)
        (holWordToBitVec dimension constant) := by
  unfold crepMulConst
  have hzero : (constant == (0 : ι → Bool)) =
      (holWordToBitVec dimension constant == (0 : BitVec dimension.width)) := by
    change (holWordToBitVec dimension constant ==
        holWordToBitVec dimension (0 : ι → Bool)) =
      (holWordToBitVec dimension constant == (0 : BitVec dimension.width))
    rw [holFiniteWordToBitVec_zero]
  have hone : (constant == (1 : ι → Bool)) =
      (holWordToBitVec dimension constant == (1 : BitVec dimension.width)) := by
    change (holWordToBitVec dimension constant ==
        holWordToBitVec dimension (1 : ι → Bool)) =
      (holWordToBitVec dimension constant == (1 : BitVec dimension.width))
    rw [holFiniteWordToBitVec_one]
  rw [hzero, hone]
  by_cases hzero : holWordToBitVec dimension constant == 0
  · have hzeroEq : holWordToBitVec dimension constant = 0 := of_decide_eq_true hzero
    simp [hzeroEq, mapCrepExpWord, holFiniteWordToBitVec_zero]
  · by_cases hone : holWordToBitVec dimension constant == 1
    · have honeEq : holWordToBitVec dimension constant = 1 := of_decide_eq_true hone
      simp [honeEq, NeZero.ne dimension.width]
    · simp only [if_neg hzero, if_neg hone]
      rw [crepDest2Exp_holFiniteDimension]
      cases crepDest2Exp 0 (holWordToBitVec dimension constant) with
      | none => simp [mapCrepExpWord]
      | some exponent =>
          simp only [mapCrepExpWord]
          exact congrArg (fun word => CrepExp.shift Shift.lsl
            (mapCrepExpWord (holWordToBitVec dimension) expression)
            (CrepExp.const word))
            (holWordToBitVec_bitVecToHolWord dimension _)

/-- Generic Flapjack support lemma: a successful destination test identifies
    the expression as exactly that constant. This is not tagged as HOL's
    `dest_const_thm`, whose expression and value are restricted to the HOL
    word type. The faithful positive-width word specialization is tagged below;
    this arbitrary-carrier helper remains untagged for the local simp proof. -/
theorem crepDestConst_eq_const {α : Type} (expression : CrepExp α)
    (value : α)
    (h : crepDestConst expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConst]

/-- Width-specialized word form of CakeML's `dest_const_thm`
    (`crep_arithProofScript.sml:64`). The carrier is `Fin width → Bool` and
    `NeZero width` supplies HOL's nonempty finite-index condition. The
    arbitrary-carrier production helper remains untagged.

    Type-convention note (see the direct HOL rows `word_carrier_bool`,
    `dimindex_8`, `dimindex_pos` in
    `scripts/hol-probes/crep_arith_dest_const_probe.out`): HOL `'a word` is
    literally the finite boolean function space `bool[dimindex(:'a)]`, and
    `dimindex` is always positive. Instantiating the HOL index type at
    cardinality `width` therefore yields exactly the Lean carrier
    `Fin width → Bool`, and `[NeZero width]` encodes `dimindex > 0`; no HOL word
    dimension lies outside this family, so the width-indexed statement is the
    exact HOL theorem, not a specialization. The paired Lean fixture lives in
    `Flapjack/Test/CrepeDestConstParity.lean`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm"]
theorem crepDestConstHolWord_eq_const {width : Nat} [NeZero width]
    (expression : CrepExp (Fin width → Bool))
    (value : Fin width → Bool)
    (h : crepDestConstHolWord expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConstHolWord]

/-- Canonical width-indexed BitVec support specialization of the generic
    HOL-word `dest_const_thm` port above. Kept untagged because the theorem
    itself is already stated over HOL's polymorphic word carrier. -/
theorem crepDestConstWord_eq_const {width : Nat} [NeZero width]
    (expression : CrepExp (RiscV.Word width))
    (value : RiscV.Word width)
    (h : crepDestConst expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConst]

/-- Exact generic list-success monotonicity helper from HOL's local
    `OPT_MMAP_EQ_SOME_MONO` (`crep_arithProofScript.sml:93`).  `List.mapM` with
    the `Option` monad is the Lean encoding of HOL's `OPT_MMAP`; this lemma is
    independent of the Crep evaluator and is used for pointwise successful
    result preservation in the arithmetic simplifier proof. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "OPT_MMAP_EQ_SOME_MONO" 93]
theorem optMmapEqSomeMono {α β : Type} (f g : α → Option β)
    (xs : List α) (ys : List β)
    (hf : xs.mapM f = some ys)
    (hmono : ∀ x z, x ∈ xs → f x = some z → g x = some z) :
    xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil =>
      simp_all
  | cons x xs ih =>
      simp only [List.mapM_cons] at hf ⊢
      cases hfx : f x with
      | none => simp [hfx] at hf
      | some z =>
          cases htail : xs.mapM f with
          | none => simp [hfx, htail] at hf
          | some tail =>
              have hys : z :: tail = ys := by
                simpa [hfx, htail] using hf
              have hgx : g x = some z :=
                hmono x z (by simp) hfx
              have hgtail : xs.mapM g = some tail :=
                ih tail htail (by
                  intro y value hy hvalue
                  exact hmono y value (by simp [hy]) hvalue)
              simp [hgx, hgtail, hys]

private theorem crepDestConst_mapCrepExpWord {α β : Type}
    (convert : α → β) (expression : CrepExp α) :
    crepDestConst (mapCrepExpWord convert expression) =
      (crepDestConst expression).map convert := by
  cases expression <;> simp [crepDestConst, mapCrepExpWord]

/-! The binary multiply case of simplifier naturality across the canonical
    finite-word representation. -/
private theorem crepSimpMul_holWordBits {width : Nat} [NeZero width]
    (left right : CrepExp (Fin width → Bool))
    (hleft : mapCrepExpWord holWordBitsToBitVec
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) left) =
      crepSimpExp (BitVec.ofNat width) (mapCrepExpWord holWordBitsToBitVec left))
    (hright : mapCrepExpWord holWordBitsToBitVec
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) right) =
      crepSimpExp (BitVec.ofNat width) (mapCrepExpWord holWordBitsToBitVec right)) :
    mapCrepExpWord holWordBitsToBitVec
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
          (.crepOp .mul [left, right])) =
      crepSimpExp (BitVec.ofNat width)
        (.crepOp .mul [mapCrepExpWord holWordBitsToBitVec left,
          mapCrepExpWord holWordBitsToBitVec right]) := by
  let simpFin := fun expression => crepSimpExp
    (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) expression
  let simpBV := fun expression => crepSimpExp (BitVec.ofNat width) expression
  change mapCrepExpWord holWordBitsToBitVec (simpFin (.crepOp .mul [left, right])) =
    simpBV (.crepOp .mul [mapCrepExpWord holWordBitsToBitVec left,
      mapCrepExpWord holWordBitsToBitVec right])
  cases hL : crepDestConst (simpFin left) with
  | some leftConstant =>
    have hLshape := crepDestConst_eq_const (simpFin left) leftConstant hL
    have hLtarget : simpBV (mapCrepExpWord holWordBitsToBitVec left) =
        .const (holWordBitsToBitVec leftConstant) := by
      calc
        simpBV (mapCrepExpWord holWordBitsToBitVec left) =
            mapCrepExpWord holWordBitsToBitVec (simpFin left) := hleft.symm
        _ = .const (holWordBitsToBitVec leftConstant) := by
          rw [hLshape]
          simp [mapCrepExpWord]
    cases hR : crepDestConst (simpFin right) with
    | some rightConstant =>
      have hRshape := crepDestConst_eq_const (simpFin right) rightConstant hR
      have hRtarget : simpBV (mapCrepExpWord holWordBitsToBitVec right) =
          .const (holWordBitsToBitVec rightConstant) := by
        calc
          simpBV (mapCrepExpWord holWordBitsToBitVec right) =
              mapCrepExpWord holWordBitsToBitVec (simpFin right) := hright.symm
          _ = .const (holWordBitsToBitVec rightConstant) := by
            rw [hRshape]
            simp [mapCrepExpWord]
      have hsource := crepSimpExp.eq_5
        (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        [left, right] leftConstant rightConstant (by simp [simpFin, hLshape, hRshape])
      have htarget := crepSimpExp.eq_5 (BitVec.ofNat width)
        [mapCrepExpWord holWordBitsToBitVec left,
          mapCrepExpWord holWordBitsToBitVec right]
        (holWordBitsToBitVec leftConstant) (holWordBitsToBitVec rightConstant)
        (by simp [simpBV, hLtarget, hRtarget])
      dsimp [simpFin, simpBV] at hsource htarget ⊢
      rw [hsource, htarget]
      simp [mapCrepExpWord, crepDestConst]
    | none =>
      have hRtargetNone : crepDestConst (simpBV
          (mapCrepExpWord holWordBitsToBitVec right)) = none := by
        change crepDestConst (crepSimpExp (BitVec.ofNat width)
          (mapCrepExpWord holWordBitsToBitVec right)) = none
        rw [← hright, crepDestConst_mapCrepExpWord]
        change Option.map holWordBitsToBitVec (crepDestConst (simpFin right)) = none
        rw [hR]
        rfl
      have hRnotConst : ∀ value, simpFin right = .const value → False := by
        intro value heq
        simp [heq, crepDestConst] at hR
      have hRtargetNotConst : ∀ value,
          simpBV (mapCrepExpWord holWordBitsToBitVec right) = .const value → False := by
        intro value heq
        simp [heq, crepDestConst] at hRtargetNone
      have hsource := crepSimpExp.eq_6
        (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        [left, right] leftConstant (simpFin right) hRnotConst
        (by simp [simpFin, hLshape])
      have htarget := crepSimpExp.eq_6 (BitVec.ofNat width)
        [mapCrepExpWord holWordBitsToBitVec left,
          mapCrepExpWord holWordBitsToBitVec right]
        (holWordBitsToBitVec leftConstant)
        (simpBV (mapCrepExpWord holWordBitsToBitVec right)) hRtargetNotConst
        (by simp [simpBV, hLtarget])
      dsimp [simpFin, simpBV] at hsource htarget ⊢
      rw [hsource, htarget]
      calc
        mapCrepExpWord holWordBitsToBitVec
            (crepMulConst (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
              (simpFin right) leftConstant) =
            crepMulConst (BitVec.ofNat width)
              (mapCrepExpWord holWordBitsToBitVec (simpFin right))
              (holWordBitsToBitVec leftConstant) :=
          crepMulConst_holWordBits (simpFin right) leftConstant
        _ = crepMulConst (BitVec.ofNat width) (simpBV
              (mapCrepExpWord holWordBitsToBitVec right))
              (holWordBitsToBitVec leftConstant) := by rw [hright]
  | none =>
    have hLtargetNone : crepDestConst (simpBV
        (mapCrepExpWord holWordBitsToBitVec left)) = none := by
      change crepDestConst (crepSimpExp (BitVec.ofNat width)
        (mapCrepExpWord holWordBitsToBitVec left)) = none
      rw [← hleft, crepDestConst_mapCrepExpWord]
      change Option.map holWordBitsToBitVec (crepDestConst (simpFin left)) = none
      rw [hL]
      rfl
    have hLnotConst : ∀ value, simpFin left = .const value → False := by
      intro value heq
      simp [heq, crepDestConst] at hL
    have hLtargetNotConst : ∀ value,
        simpBV (mapCrepExpWord holWordBitsToBitVec left) = .const value → False := by
      intro value heq
      simp [heq, crepDestConst] at hLtargetNone
    cases hR : crepDestConst (simpFin right) with
    | some rightConstant =>
      have hRshape := crepDestConst_eq_const (simpFin right) rightConstant hR
      have hRtarget : simpBV (mapCrepExpWord holWordBitsToBitVec right) =
          .const (holWordBitsToBitVec rightConstant) := by
        calc
          simpBV (mapCrepExpWord holWordBitsToBitVec right) =
              mapCrepExpWord holWordBitsToBitVec (simpFin right) := hright.symm
          _ = .const (holWordBitsToBitVec rightConstant) := by
            rw [hRshape]
            simp [mapCrepExpWord]
      have hsource := crepSimpExp.eq_7
        (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        [left, right] (simpFin left) rightConstant hLnotConst
        (by simp [simpFin, hRshape])
      have htarget := crepSimpExp.eq_7 (BitVec.ofNat width)
        [mapCrepExpWord holWordBitsToBitVec left,
          mapCrepExpWord holWordBitsToBitVec right]
        (simpBV (mapCrepExpWord holWordBitsToBitVec left))
        (holWordBitsToBitVec rightConstant) hLtargetNotConst
        (by simp [simpBV, hRtarget])
      dsimp [simpFin, simpBV] at hsource htarget ⊢
      rw [hsource, htarget]
      calc
        mapCrepExpWord holWordBitsToBitVec
            (crepMulConst (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
              (simpFin left) rightConstant) =
            crepMulConst (BitVec.ofNat width)
              (mapCrepExpWord holWordBitsToBitVec (simpFin left))
              (holWordBitsToBitVec rightConstant) :=
          crepMulConst_holWordBits (simpFin left) rightConstant
        _ = crepMulConst (BitVec.ofNat width)
              (simpBV (mapCrepExpWord holWordBitsToBitVec left))
              (holWordBitsToBitVec rightConstant) := by rw [hleft]
    | none =>
      have hRtargetNone : crepDestConst (simpBV
          (mapCrepExpWord holWordBitsToBitVec right)) = none := by
        change crepDestConst (crepSimpExp (BitVec.ofNat width)
          (mapCrepExpWord holWordBitsToBitVec right)) = none
        rw [← hright, crepDestConst_mapCrepExpWord]
        change Option.map holWordBitsToBitVec (crepDestConst (simpFin right)) = none
        rw [hR]
        rfl
      have hRnotConst : ∀ value, simpFin right = .const value → False := by
        intro value heq
        simp [heq, crepDestConst] at hR
      have hRtargetNotConst : ∀ value,
          simpBV (mapCrepExpWord holWordBitsToBitVec right) = .const value → False := by
        intro value heq
        simp [heq, crepDestConst] at hRtargetNone
      have hnotConstConst : ∀ a b, CrepOp.mul = CrepOp.mul →
          List.map simpFin [left, right] = [.const a, .const b] → False := by
        intro a b _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hLnotConst a hmap.1
      have hnotLeftConst : ∀ c expression, CrepOp.mul = CrepOp.mul →
          List.map simpFin [left, right] = [.const c, expression] → False := by
        intro c expression _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hLnotConst c hmap.1
      have hnotRightConst : ∀ expression c, CrepOp.mul = CrepOp.mul →
          List.map simpFin [left, right] = [expression, .const c] → False := by
        intro expression c _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hRnotConst c hmap.2.1
      have hsource := crepSimpExp.eq_8
        (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        [left, right] CrepOp.mul hnotConstConst hnotLeftConst hnotRightConst
      have hnotConstConstTarget : ∀ a b, CrepOp.mul = CrepOp.mul →
          List.map (simpBV ∘ mapCrepExpWord holWordBitsToBitVec) [left, right] =
            [.const a, .const b] → False := by
        intro a b _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hLtargetNotConst a hmap.1
      have hnotLeftConstTarget : ∀ c expression, CrepOp.mul = CrepOp.mul →
          List.map (simpBV ∘ mapCrepExpWord holWordBitsToBitVec) [left, right] =
            [.const c, expression] → False := by
        intro c expression _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hLtargetNotConst c hmap.1
      have hnotRightConstTarget : ∀ expression c, CrepOp.mul = CrepOp.mul →
          List.map (simpBV ∘ mapCrepExpWord holWordBitsToBitVec) [left, right] =
            [expression, .const c] → False := by
        intro expression c _ hmap
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
        exact hRtargetNotConst c hmap.2.1
      have htarget := crepSimpExp.eq_8 (BitVec.ofNat width)
        [mapCrepExpWord holWordBitsToBitVec left,
          mapCrepExpWord holWordBitsToBitVec right]
        CrepOp.mul hnotConstConstTarget hnotLeftConstTarget hnotRightConstTarget
      dsimp [simpFin, simpBV] at hsource htarget ⊢
      rw [hsource, htarget]
      simp [mapCrepExpWord, hleft, hright]

/-! The full bottom-up simplifier is natural under the finite-index/BitVec
    word isomorphism at every positive width. -/
private theorem crepSimpExp_holWordBits {width : Nat} [NeZero width]
    (expression : CrepExp (Fin width → Bool)) :
    mapCrepExpWord holWordBitsToBitVec
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
          expression) =
      crepSimpExp (BitVec.ofNat width)
        (mapCrepExpWord holWordBitsToBitVec expression) := by
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions →
          mapCrepExpWord holWordBitsToBitVec
              (crepSimpExp
                (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) e) =
            crepSimpExp (BitVec.ofNat width)
              (mapCrepExpWord holWordBitsToBitVec e)) ∧
        List.map (mapCrepExpWord holWordBitsToBitVec)
            (List.map (crepSimpExp
              (fun value => bitVecToHolWordBits (BitVec.ofNat width value))) expressions) =
          List.map (crepSimpExp (BitVec.ofNat width))
            (List.map (mapCrepExpWord holWordBitsToBitVec) expressions)))
  case const value => simp [crepSimpExp, mapCrepExpWord]
  case var name => simp [crepSimpExp, mapCrepExpWord]
  case load address ih => simp [crepSimpExp, mapCrepExpWord, ih]
  case load32 address ih => simp [crepSimpExp, mapCrepExpWord, ih]
  case loadByte address ih => simp [crepSimpExp, mapCrepExpWord, ih]
  case loadGlob address => simp [crepSimpExp, mapCrepExpWord]
  case op operator expressions ih =>
    simp only [crepSimpExp, mapCrepExpWord, ih.2]
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil => simp [crepSimpExp, mapCrepExpWord]
    | cons first tail =>
      have hfirst := ih.1 first (by simp)
      cases tail with
      | nil => simp [crepSimpExp, mapCrepExpWord, hfirst]
      | cons second tail =>
        have hsecond := ih.1 second (by simp)
        cases tail with
        | nil =>
          simpa [mapCrepExpWord] using crepSimpMul_holWordBits first second hfirst hsecond
        | cons extra rest =>
          have hnotConstConst : ∀ a b, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp
                (fun value => bitVecToHolWordBits (BitVec.ofNat width value)))
                (first :: second :: extra :: rest) = [.const a, .const b] → False := by
            intro a b _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have hnotLeftConst : ∀ c e, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp
                (fun value => bitVecToHolWordBits (BitVec.ofNat width value)))
                (first :: second :: extra :: rest) = [.const c, e] → False := by
            intro c e _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have hnotRightConst : ∀ e c, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp
                (fun value => bitVecToHolWordBits (BitVec.ofNat width value)))
                (first :: second :: extra :: rest) = [e, .const c] → False := by
            intro e c _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have hsource := crepSimpExp.eq_8
            (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
            (first :: second :: extra :: rest) CrepOp.mul
            hnotConstConst hnotLeftConst hnotRightConst
          have hnotConstConstTarget : ∀ a b, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat width))
                (List.map (mapCrepExpWord holWordBitsToBitVec)
                  (first :: second :: extra :: rest)) = [.const a, .const b] → False := by
            intro a b _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have hnotLeftConstTarget : ∀ c e, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat width))
                (List.map (mapCrepExpWord holWordBitsToBitVec)
                  (first :: second :: extra :: rest)) = [.const c, e] → False := by
            intro c e _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have hnotRightConstTarget : ∀ e c, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat width))
                (List.map (mapCrepExpWord holWordBitsToBitVec)
                  (first :: second :: extra :: rest)) = [e, .const c] → False := by
            intro e c _ hmap
            have hlen := congrArg List.length hmap
            simp at hlen
          have htarget := crepSimpExp.eq_8 (BitVec.ofNat width)
            (List.map (mapCrepExpWord holWordBitsToBitVec)
              (first :: second :: extra :: rest)) CrepOp.mul
            hnotConstConstTarget hnotLeftConstTarget hnotRightConstTarget
          rw [hsource]
          rw [mapCrepExpWord.eq_8 holWordBitsToBitVec CrepOp.mul
            (List.map (crepSimpExp
              (fun value => bitVecToHolWordBits (BitVec.ofNat width value)))
              (first :: second :: extra :: rest))]
          rw [mapCrepExpWord.eq_8 holWordBitsToBitVec CrepOp.mul
            (first :: second :: extra :: rest)]
          rw [htarget]
          exact congrArg (CrepExp.crepOp CrepOp.mul) ih.2
  case cmp operator left right ihLeft ihRight =>
    rw [crepSimpExp.eq_9 (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
      operator left right]
    rw [mapCrepExpWord.eq_9 holWordBitsToBitVec operator
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) left)
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) right)]
    rw [mapCrepExpWord.eq_9 holWordBitsToBitVec operator left right]
    rw [crepSimpExp.eq_9 (BitVec.ofNat width) operator
      (mapCrepExpWord holWordBitsToBitVec left) (mapCrepExpWord holWordBitsToBitVec right)]
    rw [ihLeft, ihRight]
  case shift operator left right ihLeft ihRight =>
    rw [crepSimpExp.eq_10 (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
      operator left right]
    rw [mapCrepExpWord.eq_10 holWordBitsToBitVec operator
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) left)
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) right)]
    rw [mapCrepExpWord.eq_10 holWordBitsToBitVec operator left right]
    rw [crepSimpExp.eq_10 (BitVec.ofNat width) operator
      (mapCrepExpWord holWordBitsToBitVec left) (mapCrepExpWord holWordBitsToBitVec right)]
    rw [ihLeft, ihRight]
  case baseAddr => simp [crepSimpExp.eq_11, mapCrepExpWord]
  case topAddr => simp [crepSimpExp.eq_11, mapCrepExpWord]
  case nil => constructor <;> simp
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead
      · exact ihTail.1 e he
    · simp only [List.map_cons]
      rw [ihHead, ihTail.2]

/-! The following private BitVec arithmetic lemmas support the RISC-V
    specialization of HOL's destination facts. They are generic Lean helpers
    and have no declaration in the CakeML HOL development. -/

private theorem bitVec_even_shift_double {n : Nat} (word : BitVec n)
    (heven : word.toNat % 2 = 0) :
    word.toNat = 2 * (BitVec.ushiftRight word 1).toNat := by
  change word.toNat = 2 * (word.toNat >>> 1)
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.mod_add_div word.toNat 2
  omega

private theorem one_lt_pow_two {n : Nat} [NeZero n] : 1 < 2 ^ n := by
  cases n with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ n => simp

private theorem bitVec_one_toNat {n : Nat} [NeZero n] :
    (1 : BitVec n).toNat = 1 := by
  change (BitVec.ofNat n 1).toNat = 1
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt one_lt_pow_two

private theorem bitVec_lowBit_zero_even {n : Nat} [NeZero n]
    (word : RiscV.Word n) (h : AndOp.and word 1 = 0) :
    word.toNat % 2 = 0 := by
  have ht := congrArg BitVec.toNat h
  change (word &&& (1 : BitVec n)).toNat = 0 at ht
  rw [BitVec.toNat_and] at ht
  rw [bitVec_one_toNat, Nat.and_one_is_mod] at ht
  exact ht

private theorem bitVec_even_shiftRight_one_double {n : Nat} [NeZero n]
    (word : RiscV.Word n) (heven : word.toNat % 2 = 0) :
    word.toNat = 2 * (ShiftRight.shiftRight word 1).toNat := by
  have hnat := bitVec_even_shift_double word heven
  have hshift : ShiftRight.shiftRight word (1 : RiscV.Word n) =
      BitVec.ushiftRight word 1 := by
    change BitVec.ushiftRight word (1 : RiscV.Word n).toNat =
      BitVec.ushiftRight word 1
    rw [bitVec_one_toNat]
  rw [hshift]
  exact hnat

private theorem crepDest2ExpFuel_sound {n : Nat} [NeZero n]
    (fuel start : Nat) (word : RiscV.Word n) (result : Nat)
    (h : crepDest2ExpFuel fuel start word = some result) :
    start ≤ result ∧ result - start < n ∧
      word.toNat = 2 ^ (result - start) % 2 ^ n := by
  induction fuel generalizing start word result with
  | zero => simp [crepDest2ExpFuel] at h
  | succ fuel ih =>
      simp only [crepDest2ExpFuel] at h
      split at h
      · contradiction
      · split at h
        · have heval : some start = some result := h
          have hr : result = start := by cases heval; rfl
          subst result
          have hw : word = 1 := by simpa using ‹(word == 1) = true›
          have hword : word.toNat = 1 := by
            rw [hw, bitVec_one_toNat]
          have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
          refine ⟨by omega, by omega, ?_⟩
          simp [hword, Nat.mod_eq_of_lt one_lt_pow_two]
        · split at h
          · contradiction
          · have hrec :
              crepDest2ExpFuel fuel (start + 1) (ShiftRight.shiftRight word 1) =
                  some result := h
            have hand : AndOp.and word 1 = 0 := by
              have hbit : (AndOp.and word 1 != 0) = false := by
                cases hb : (AndOp.and word 1 != 0) <;> simp_all
              simpa using hbit
            have ihResult := ih (start + 1) (ShiftRight.shiftRight word 1)
              result hrec
            obtain ⟨hstart, hwidth, hword⟩ := ihResult
            have hdouble := bitVec_even_shiftRight_one_double word
              (bitVec_lowBit_zero_even word hand)
            have hd : result - (start + 1) < n := hwidth
            have hdiff : result - start = result - (start + 1) + 1 := by omega
            have hmod : 2 ^ (result - (start + 1)) % 2 ^ n =
                2 ^ (result - (start + 1)) :=
              Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hd)
            have hlt : word.toNat < 2 ^ n := word.isLt
            rw [hdouble, hword, hmod] at hlt
            have hpowlt : 2 ^ (result - (start + 1) + 1) < 2 ^ n := by
              rw [Nat.pow_succ, Nat.mul_comm]
              exact hlt
            have hdlt : result - (start + 1) + 1 < n :=
              (Nat.pow_lt_pow_iff_right (by decide)).mp hpowlt
            refine ⟨by omega, by omega, ?_⟩
            calc
              word.toNat = 2 * (ShiftRight.shiftRight word 1).toNat := hdouble
              _ = 2 ^ (result - (start + 1) + 1) := by
                rw [hword, hmod, Nat.pow_succ]
                omega
              _ = 2 ^ (result - start) % 2 ^ n := by
                rw [hdiff, Nat.mod_eq_of_lt hpowlt]

/-- Width-parametric BitVec support for HOL's `dest_2exp_bound`
    (`crep_arithProofScript.sml:10`). HOL defines `word_log2 w` as
    `n2w (LOG2 (w2n w))`; `BitVec.ofNat` and `BitVec.toNat` express those
    operations for the Lean width-indexed word representation. This follows
    from production `crepDest2Exp` soundness without assuming an
    evaluator-preservation result. It is intentionally untagged: the Lean
    theorem quantifies over `BitVec n`, while HOL quantifies over its
    polymorphic `'a word`/implicit `dimindex`; the finite-index carrier
    identification needed to claim the exact polymorphic HOL declaration has
    not been established. -/
theorem crepDest2ExpBound {n : Nat} [NeZero n]
    (start : Nat) (word : BitVec n) (result : Nat)
    (h : crepDest2Exp start word = some result) :
    result ≤ start + (BitVec.ofNat n (Nat.log2 word.toNat)).toNat := by
  change crepDest2ExpFuel (n + 1) start word = some result at h
  have hs := crepDest2ExpFuel_sound (n + 1) start word result h
  obtain ⟨hstart, hwidth, hword⟩ := hs
  have hdiff : result - start < n := hwidth
  have hpowlt : 2 ^ (result - start) < 2 ^ n :=
    Nat.pow_lt_pow_right (by decide) hdiff
  have hwordNat : word.toNat = 2 ^ (result - start) := by
    rw [hword, Nat.mod_eq_of_lt hpowlt]
  have hlog : Nat.log2 word.toNat = result - start := by
    rw [hwordNat, Nat.log2_two_pow]
  have hlogWrap : (BitVec.ofNat n (Nat.log2 word.toNat)).toNat = result - start := by
    rw [hlog, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans hdiff (Nat.lt_two_pow_self (n := n))
  rw [hlogWrap]
  omega

/-- Flapjack support for CakeML's `dest_2exp_bound`
    (`crep_arithProofScript.sml:10`) over every explicit finite word
    dimension. The right side encodes `w2n (word_log2 word)` by transporting
    through `BitVec` and computing `Nat.log2`. It remains untagged: the
    equality of this explicit `HolFiniteDimension`/`Nat.log2` encoding with
    HOL's implicit `finite_index`/`word_log2` interpretation has not been
    separately established. This recognizer bound does not assume either
    `eval_mul_const` or `simp_exp_correct1`. -/
theorem crepDest2ExpHolFiniteDimensionBoundSupport {ι : Type}
    (dimension : HolFiniteDimension ι)
    (start : Nat) (word : ι → Bool) (result : Nat)
    (h : crepDest2Exp start word = some result) :
    result ≤ start +
      (holWordToBitVec dimension
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width
          (Nat.log2 (holWordToBitVec dimension word).toNat)))).toNat := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hBits : crepDest2Exp start (holWordToBitVec dimension word) =
      some result := by
    rw [← crepDest2Exp_holFiniteDimension start word]
    exact h
  have hBound := crepDest2ExpBound start
    (holWordToBitVec dimension word) result hBits
  simpa only [holWordToBitVec_bitVecToHolWord] using hBound

/-- Fixed-width support instance of HOL `dest_2exp_thm`. The HOL theorem is
    polymorphic in `'a word`; this declaration proves only the `RiscV.Word n`
    representation and therefore has no HOL tag. A genuinely generic theorem
    over the finite-index word carrier remains open. -/
theorem crepDest2Exp_eq_shift {n : Nat} [NeZero n] (word : RiscV.Word n)
    (exponent : Nat) (h : crepDest2Exp 0 word = some exponent) :
    word = BitVec.shiftLeft (1 : RiscV.Word n) exponent := by
  change crepDest2ExpFuel (n + 1) 0 word = some exponent at h
  have hs := crepDest2ExpFuel_sound (n + 1) 0 word exponent h
  obtain ⟨_, hbound, hword⟩ := hs
  have hbound : exponent < n := by simpa using hbound
  apply BitVec.eq_of_toNat_eq
  change word.toNat = (BitVec.shiftLeft (1 : RiscV.Word n) exponent).toNat
  rw [BitVec.shiftLeft_eq]
  rw [BitVec.toNat_shiftLeft]
  rw [bitVec_one_toNat]
  rw [Nat.mod_eq_of_lt (by
    have : 2 ^ exponent < 2 ^ n := Nat.pow_lt_pow_right (by decide) hbound
    simpa [Nat.shiftLeft_eq, Nat.one_mul] using this)]
  have hword' : word.toNat = 2 ^ exponent % 2 ^ n := by simpa using hword
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hbound)] at hword'
  simpa [Nat.shiftLeft_eq, Nat.one_mul] using hword'

/-- All-width support for HOL `dest_2exp_thm` over the canonical word carrier.
    `Fin width → Bool` is the numeric-index presentation of one HOL word
    dimension, and the result transports `word_lsl 1w exponent` through the
    proved bitwise `BitVec` equivalence. This remains untagged: the theorem's
    carrier uses an explicit `Fin width` index instead of HOL's implicit
    `finite_index` type and instance, so the polymorphic HOL statement has not
    yet been identified with this canonical presentation. -/
theorem crepDest2ExpHolWordBits_eq_lsl_support {width : Nat} [NeZero width]
    (word : Fin width → Bool) (exponent : Nat)
    (h : crepDest2Exp 0 word = some exponent) :
    word = bitVecToHolWordBits
      (BitVec.shiftLeft (1 : BitVec width) exponent) := by
  have hBits : crepDest2Exp 0 (holWordBitsToBitVec word) = some exponent := by
    rw [← crepDest2Exp_holWordBits 0 word]
    exact h
  have hShift := crepDest2Exp_eq_shift (holWordBitsToBitVec word)
    exponent hBits
  apply holWordBitsToBitVec_injective
  simpa only [holWordBitsToBitVec_bitVecToHolWordBits] using hShift

/-- Fixed-width support instance of HOL `dest_2exp_bound'`. The HOL result
    quantifies over any word type and concludes `exponent < dimindex`; this
    theorem fixes `RiscV.Word n` and is not a faithful tagged port. -/
theorem crepDest2Exp_lt_width {n : Nat} [NeZero n] (word : RiscV.Word n)
    (exponent : Nat) (h : crepDest2Exp 0 word = some exponent) :
    exponent < n := by
  change crepDest2ExpFuel (n + 1) 0 word = some exponent at h
  have hs := crepDest2ExpFuel_sound (n + 1) 0 word exponent h
  exact (by simpa using hs.2.1)

/-- Finite-dimension support for HOL `dest_2exp_bound'`. Unlike the
    fixed-width helper, this ranges over every explicit finite index
    enumeration, but remains untagged because the Lean enumeration witness
    has not been identified with HOL's implicit `finite_index` choice. -/
theorem crepDest2ExpHolFiniteDimension_lt_width {ι : Type}
    (dimension : HolFiniteDimension ι) (word : ι → Bool)
    (exponent : Nat)
    (h : crepDest2Exp 0 word = some exponent) :
    exponent < dimension.width := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hBits : crepDest2Exp 0 (holWordToBitVec dimension word) =
      some exponent := by
    rw [← crepDest2Exp_holFiniteDimension 0 word]
    exact h
  exact crepDest2Exp_lt_width (holWordToBitVec dimension word) exponent hBits

/-- Finite-dimension support for HOL `dest_2exp_thm`, retaining its exponent
    result while translating `word_lsl` through the explicit bit-index
    enumeration. It is not tagged until that enumeration is related to HOL's
    implicit `finite_index` representation. -/
theorem crepDest2ExpHolFiniteDimension_eq_shift {ι : Type}
    (dimension : HolFiniteDimension ι) (word : ι → Bool)
    (exponent : Nat)
    (h : crepDest2Exp 0 word = some exponent) :
    word = ShiftLeft.shiftLeft (1 : ι → Bool)
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hbound := crepDest2ExpHolFiniteDimension_lt_width dimension word exponent h
  have hBits : crepDest2Exp 0 (holWordToBitVec dimension word) =
      some exponent := by
    rw [← crepDest2Exp_holFiniteDimension 0 word]
    exact h
  have hBitsPower := crepDest2Exp_eq_shift
    (holWordToBitVec dimension word) exponent hBits
  have hShiftMap : holWordToBitVec dimension
      (ShiftLeft.shiftLeft (1 : ι → Bool)
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent))) =
      BitVec.shiftLeft (1 : BitVec dimension.width) exponent := by
    rw [holFiniteWordToBitVec_shiftLeft, holFiniteWordToBitVec_one,
      holWordToBitVec_bitVecToHolWord]
    change BitVec.shiftLeft (1 : BitVec dimension.width)
      (BitVec.ofNat dimension.width exponent).toNat = _
    have hfromNat : (BitVec.ofNat dimension.width exponent).toNat = exponent := by
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
        (Nat.pow_lt_pow_right (by decide) hbound)
    simp [hfromNat]
  calc
    word = bitVecToHolWord dimension (holWordToBitVec dimension word) :=
      (bitVecToHolWord_holWordToBitVec dimension word).symm
    _ = bitVecToHolWord dimension
        (holWordToBitVec dimension
          (ShiftLeft.shiftLeft (1 : ι → Bool)
            (bitVecToHolWord dimension
              (BitVec.ofNat dimension.width exponent)))) := by
          rw [hShiftMap, hBitsPower]
    _ = ShiftLeft.shiftLeft (1 : ι → Bool)
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)) :=
          bitVecToHolWord_holWordToBitVec dimension _

/-- Flapjack-only natural-exponent shift adapter for an explicit finite word
    dimension. It converts the production `ShiftLeft` operation, whose amount
    is a word, to the source-style `BitVec.shiftLeft` amount used for HOL
    `word_lsl`. The `HolFiniteDimension`/HOL `finite_index` correspondence is
    still an open review gap, so this carries no HOL tag. -/
theorem holFiniteDimension_wordLsl_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (word : ι → Bool)
    (exponent : Nat) (hbound : exponent < dimension.width) :
    holWordToBitVec dimension
        (ShiftLeft.shiftLeft word
          (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent))) =
      BitVec.shiftLeft (holWordToBitVec dimension word) exponent := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  rw [holFiniteWordToBitVec_shiftLeft, holWordToBitVec_bitVecToHolWord]
  change BitVec.shiftLeft (holWordToBitVec dimension word)
      (BitVec.ofNat dimension.width exponent).toNat = _
  have hfromNat : (BitVec.ofNat dimension.width exponent).toNat = exponent := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
      (Nat.pow_lt_pow_right (by decide) hbound)
  rw [hfromNat]

/-- Transported `dest_2exp` source support: successful recognition proves the
    input is `word_lsl 1 exponent`, with natural-exponent left shift represented
    on the canonical BitVec image. Kept untagged because the finite-index
    witness and evaluator are not yet identified with HOL's implicit choice. -/
theorem crepDest2ExpHolFiniteDimension_eq_lsl {ι : Type}
    (dimension : HolFiniteDimension ι) (word : ι → Bool)
    (exponent : Nat)
    (h : crepDest2Exp 0 word = some exponent) :
    word = bitVecToHolWord dimension
      (BitVec.shiftLeft (holWordToBitVec dimension (1 : ι → Bool)) exponent) := by
  have hbound := crepDest2ExpHolFiniteDimension_lt_width dimension word exponent h
  have hshift := crepDest2ExpHolFiniteDimension_eq_shift dimension word exponent h
  have hshiftEq : ShiftLeft.shiftLeft (1 : ι → Bool)
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)) =
      bitVecToHolWord dimension
        (BitVec.shiftLeft (holWordToBitVec dimension (1 : ι → Bool)) exponent) := by
    apply holWordToBitVec_injective dimension
    rw [holFiniteDimension_wordLsl_toBitVec dimension (1 : ι → Bool)
      exponent hbound, holWordToBitVec_bitVecToHolWord]
  exact hshift.trans hshiftEq

/- The arithmetic half of `eval_mul_const` only needs the target model's
left-shift operation to agree with the fixed-width word shift for amounts
below the word width. Isolating that exact operation contract lets finite
word models reuse the proof without assuming the complete canonical RISC-V
target. This remains Flapjack support, not a HOL port: the contract is an
explicit premise and must be proved from the chosen model's `word_sh` bridge. -/
theorem crepEvalMulConstForModel {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n))
    (constant value : RiscV.Word n)
    (hShift : ∀ word exponent, exponent < n →
      state.memoryModel.shift .lsl word (BitVec.ofNat n exponent) =
        some (word <<< exponent))
    (h : evalCrepRuntimeExp state expression = some value) :
    evalCrepRuntimeExp state
      (crepMulConst (BitVec.ofNat n) expression constant) =
        some (value * constant) := by
  by_cases hzero : constant = (0 : RiscV.Word n)
  · simp [crepMulConst, hzero, evalCrepRuntimeExp]
  · by_cases hone : constant = (1 : RiscV.Word n)
    · simp [crepMulConst, hone, h, NeZero.ne n]
    · have hzeroCond : ¬((constant == 0) = true) := by
        intro hb
        have heq : constant = 0 := by simpa using hb
        exact hzero heq
      have honeCond : ¬((constant == 1) = true) := by
        intro hb
        have heq : constant = 1 := by simpa using hb
        exact hone heq
      cases hdest : crepDest2Exp 0 constant with
      | none =>
          have hmul : crepMulConst (BitVec.ofNat n) expression constant =
              .crepOp .mul [expression, .const constant] := by
            unfold crepMulConst
            simp only [if_neg hzeroCond, if_neg honeCond, hdest]
          rw [hmul]
          simp [evalCrepRuntimeExp, crepOpCrep, h]
      | some exponent =>
          have hbound : exponent < n :=
            crepDest2Exp_lt_width constant exponent hdest
          have hpower : constant = BitVec.twoPow n exponent := by
            simpa [BitVec.twoPow, BitVec.shiftLeft_eq] using
              crepDest2Exp_eq_shift constant exponent hdest
          have hfromNat : (BitVec.ofNat n exponent).toNat = exponent := by
            rw [BitVec.toNat_ofNat]
            apply Nat.mod_eq_of_lt
            exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
              (Nat.pow_lt_pow_right (by decide) hbound)
          have hmulShift : value <<< exponent = value * constant := by
            calc
              value <<< exponent = value * BitVec.twoPow n exponent :=
                BitVec.shiftLeft_eq_mul_twoPow value exponent
              _ = value * constant := by rw [← hpower]
          have hmodelShift :
              state.memoryModel.shift .lsl value (BitVec.ofNat n exponent) =
                some (value * constant) := by
            rw [hShift value exponent hbound, hmulShift]
          have hmul : crepMulConst (BitVec.ofNat n) expression constant =
              .shift .lsl expression (.const (BitVec.ofNat n exponent)) := by
            unfold crepMulConst
            simp only [if_neg hzeroCond, if_neg honeCond, hdest]
          rw [hmul]
          simp [evalCrepRuntimeExp, h, hmodelShift]

/-! The finite-word version isolates the two evaluator operations used by
    HOL `eval_mul_const`: binary multiplication and left shift. This is
    Flapjack support, not a HOL port. It can be instantiated with an arbitrary
    runtime memory model after those operation equations are established. -/
theorem crepEvalMulConstFiniteWordForModel {ι : Type}
    [dimension : HolFiniteDimension ι] {σ : Type}
    (state : CrepRuntimeState (ι → Bool) σ)
    (fromNat : Nat → ι → Bool)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (hFromNat : fromNat = fun n =>
      bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
    (hShift : ∀ word exponent, exponent < dimension.width →
      state.memoryModel.shift .lsl word
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)) =
        some (word * ShiftLeft.shiftLeft (1 : ι → Bool)
          (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent))))
    (h : evalCrepRuntimeExp state expression = some value) :
    evalCrepRuntimeExp state (crepMulConst fromNat expression constant) =
      some (value * constant) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hzeroMap : (constant == (0 : ι → Bool)) =
      (holWordToBitVec dimension constant == (0 : BitVec dimension.width)) := by
    change (holWordToBitVec dimension constant ==
        holWordToBitVec dimension (0 : ι → Bool)) = _
    rw [holFiniteWordToBitVec_zero]
  have honeMap : (constant == (1 : ι → Bool)) =
      (holWordToBitVec dimension constant == (1 : BitVec dimension.width)) := by
    change (holWordToBitVec dimension constant ==
        holWordToBitVec dimension (1 : ι → Bool)) = _
    rw [holFiniteWordToBitVec_one]
  have hMulZero (word : ι → Bool) : word * (0 : ι → Bool) = 0 := by
    calc
      word * (0 : ι → Bool) = bitVecToHolWord dimension
          (holWordToBitVec dimension (word * 0)) := by
            symm
            exact bitVecToHolWord_holWordToBitVec dimension _
      _ = bitVecToHolWord dimension 0 := by
            rw [holFiniteWordToBitVec_mul, holFiniteWordToBitVec_zero]
            simp
      _ = 0 := by
            have hback := bitVecToHolWord_holWordToBitVec dimension (0 : ι → Bool)
            rw [holFiniteWordToBitVec_zero] at hback
            exact hback
  have hMulOne (word : ι → Bool) : word * (1 : ι → Bool) = word := by
    calc
      word * (1 : ι → Bool) = bitVecToHolWord dimension
          (holWordToBitVec dimension (word * 1)) := by
            symm
            exact bitVecToHolWord_holWordToBitVec dimension _
      _ = bitVecToHolWord dimension (holWordToBitVec dimension word) := by
            rw [holFiniteWordToBitVec_mul, holFiniteWordToBitVec_one]
            simp
      _ = word := bitVecToHolWord_holWordToBitVec dimension _
  unfold crepMulConst
  rw [hzeroMap, honeMap]
  by_cases hzero : holWordToBitVec dimension constant == 0
  · have hzeroEq : holWordToBitVec dimension constant = 0 := of_decide_eq_true hzero
    have hconstant : constant = 0 := by
      calc
        constant = bitVecToHolWord dimension (holWordToBitVec dimension constant) :=
          (bitVecToHolWord_holWordToBitVec dimension constant).symm
        _ = bitVecToHolWord dimension 0 := congrArg _ hzeroEq
        _ = 0 := by
          have hback := bitVecToHolWord_holWordToBitVec dimension (0 : ι → Bool)
          rw [holFiniteWordToBitVec_zero] at hback
          exact hback
    simp only [hzero, if_pos]
    rw [hconstant]
    simp [evalCrepRuntimeExp, hMulZero]
  · by_cases hone : holWordToBitVec dimension constant == 1
    · have honeEq : holWordToBitVec dimension constant = 1 := of_decide_eq_true hone
      have hconstant : constant = 1 := by
        calc
          constant = bitVecToHolWord dimension (holWordToBitVec dimension constant) :=
            (bitVecToHolWord_holWordToBitVec dimension constant).symm
          _ = bitVecToHolWord dimension 1 := congrArg _ honeEq
          _ = 1 := by
            have hback := bitVecToHolWord_holWordToBitVec dimension (1 : ι → Bool)
            rw [holFiniteWordToBitVec_one] at hback
            exact hback
      simp only [hzero, hone, if_pos]
      rw [hconstant]
      simp [h, hMulOne]
    · simp only [if_neg hzero, if_neg hone]
      cases hdest : crepDest2Exp 0 constant with
      | none =>
          simp [evalCrepRuntimeExp, crepOpCrep, h]
      | some exponent =>
          have hbound := crepDest2ExpHolFiniteDimension_lt_width
            dimension constant exponent hdest
          have hpower := crepDest2ExpHolFiniteDimension_eq_shift
            dimension constant exponent hdest
          have hmodelShift :
              state.memoryModel.shift .lsl value (fromNat exponent) =
                some (value * constant) := by
            rw [hFromNat, hShift value exponent hbound, hpower]
          simp [evalCrepRuntimeExp, h, hmodelShift]

/-! Source-runtime specialization of the finite-word model lemma. The only
    model obligation is its RISC-V-backed shift field; the load operations may
    be the source-shaped finite-word model rather than the RISC-V byte model. -/
theorem crepEvalMulConstHolFiniteWordSource {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (h : evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension) expression =
      some value) :
    evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression constant) = some (value * constant) := by
  letI : HolFiniteDimension ι := dimension
  let runtime := state.toHolFiniteWordSourceRuntime dimension
  have hShift : ∀ word exponent, exponent < dimension.width →
      runtime.memoryModel.shift .lsl word
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)) =
        some (word * ShiftLeft.shiftLeft (1 : ι → Bool)
          (bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent))) := by
    intro word exponent hbound
    let amount := bitVecToHolWord dimension (BitVec.ofNat dimension.width exponent)
    have hamount : (holWordToBitVec dimension amount).toNat = exponent := by
      rw [holWordToBitVec_bitVecToHolWord, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
        (Nat.pow_lt_pow_right (by decide) hbound)
    have hleftBits :
        holWordToBitVec dimension (ShiftLeft.shiftLeft word amount) =
          BitVec.shiftLeft (holWordToBitVec dimension word) exponent := by
      rw [holFiniteWordToBitVec_shiftLeft]
      change BitVec.shiftLeft (holWordToBitVec dimension word)
        (holWordToBitVec dimension amount).toNat = _
      rw [hamount]
    have hshiftWordBits :
        holWordToBitVec dimension
            (ShiftLeft.shiftLeft (1 : ι → Bool) amount) =
          BitVec.shiftLeft (1 : BitVec dimension.width) exponent := by
      rw [holFiniteWordToBitVec_shiftLeft, holFiniteWordToBitVec_one]
      change BitVec.shiftLeft (1 : BitVec dimension.width)
        (holWordToBitVec dimension amount).toNat = _
      rw [hamount]
    have hpow : BitVec.shiftLeft (1 : BitVec dimension.width) exponent =
        BitVec.twoPow dimension.width exponent := by
      simp [BitVec.twoPow, BitVec.shiftLeft_eq]
    have hmulBits :
        holWordToBitVec dimension
            (word * ShiftLeft.shiftLeft (1 : ι → Bool) amount) =
          (holWordToBitVec dimension word) <<< exponent := by
      rw [holFiniteWordToBitVec_mul, hshiftWordBits]
      rw [BitVec.shiftLeft_eq_mul_twoPow]
      rw [← hpow]
    have hWordToBitVecInjective : Function.Injective (holWordToBitVec dimension) := by
      intro left right heq
      calc
        left = bitVecToHolWord dimension (holWordToBitVec dimension left) := by
          rw [bitVecToHolWord_holWordToBitVec]
        _ = bitVecToHolWord dimension (holWordToBitVec dimension right) :=
          congrArg (bitVecToHolWord dimension) heq
        _ = right := bitVecToHolWord_holWordToBitVec dimension right
    have hshiftMul : ShiftLeft.shiftLeft word amount =
        word * ShiftLeft.shiftLeft (1 : ι → Bool) amount := by
      apply hWordToBitVecInjective
      rw [hleftBits, hmulBits]
      simp [BitVec.shiftLeft_eq]
    have hpanAmount : PanShiftWidth.amount (α := ι → Bool) amount = exponent := by
      change (holWordToBitVec dimension amount).toNat = exponent
      exact hamount
    change (holFiniteWordSourceMemoryModel dimension state.bigEndian).shift
      .lsl word amount = _
    rw [holFiniteWordSourceMemoryModel_shift_eq_evalPanShiftFull]
    change evalPanShiftFull .lsl word amount = _
    simp only [evalPanShiftFull, hpanAmount]
    have hnotWidth : ¬ PanShiftWidth.width (α := ι → Bool) ≤ exponent :=
      Nat.not_le_of_gt hbound
    have hcondition : ¬ (exponent ≠ 0 ∧
        PanShiftWidth.width (α := ι → Bool) ≤ exponent) :=
      fun hcondition => hnotWidth hcondition.2
    rw [if_neg hcondition]
    exact congrArg some hshiftMul
  exact crepEvalMulConstFiniteWordForModel runtime
    (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
    expression constant value rfl hShift h

/-- Production-evaluator `eval_mul_const` support over every explicit
    finite-index word carrier, stated with HOL's complete
    `Option (word_lab word)` result shape. This uses the source-shaped runtime
    adapter and the production `evalCrepRuntimeExp`; it remains untagged until
    that adapter's word primitives are formally identified with HOL's
    polymorphic `crepSem$eval` definitions. -/
theorem crepEvalMulConstHolFiniteWordSourceRuntimeLab {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (h : (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression).map
        PanWordLab.word = some (.word value)) :
    (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression constant)).map
        PanWordLab.word = some (.word (value * constant)) := by
  have wordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hRaw : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression = some value := by
    apply Option.map_injective wordInjective
    simpa using h
  have hPreserved := crepEvalMulConstHolFiniteWordSource dimension state
    expression constant value hRaw
  exact congrArg (Option.map PanWordLab.word) hPreserved

/-- Finite-dimension source-evaluator form of HOL `eval_mul_const`. It has
    the source evaluator's complete `Option (word_lab word)` premise and
    conclusion, and is proved by the production evaluator bridge above. It
    remains untagged because the explicit `HolFiniteDimension` and
    `CrepHolState` encodings have not yet been reviewed as exact representations
    of HOL's implicit finite-index word type and state. -/
theorem crepEvalMulConstHolFiniteWordSourceEval {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (h : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word = some (.word value)) :
    (evalCrepHolFiniteWordSourceExp dimension state
      (crepMulConst
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression constant)).map
      PanWordLab.word = some (.word (value * constant)) := by
  letI : HolFiniteDimension ι := dimension
  have wordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hRuntimeWrapped : (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression).map
        PanWordLab.word = some (.word value) := by
    rw [evalCrepRuntimeExp_sourceWord_eq dimension]
    exact h
  have hResult := crepEvalMulConstHolFiniteWordSourceRuntimeLab
    dimension state expression constant value hRuntimeWrapped
  have hResultRaw : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression constant) =
      some (value * constant) := by
    apply Option.map_injective wordInjective
    simpa using hResult
  have hSourceResult : evalCrepHolFiniteWordSourceExp dimension state
      (crepMulConst
        (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression constant) =
      some (value * constant) := by
    rw [← evalCrepRuntimeExp_sourceWord_eq dimension state]
    exact hResultRaw
  simpa using congrArg (Option.map PanWordLab.word) hSourceResult

/-- Flapjack support for HOL `eval_mul_const`, deliberately untagged. HOL's
    statement is `crepSem$eval s exp = SOME (Word w) ->
    crepSem$eval s (mul_const exp c) = SOME (Word (w * c))`, over its
    polymorphic word carrier and arbitrary `crepSem` state. This Lean support
    instead fixes values to `RiscV.Word n`, evaluates the state through
    `riscvCrepWordTarget`, and wraps the result in the `PanWordLab.word`
    constructor. The helper proves the shift arithmetic for that target;
    there is no theorem relating the resulting production evaluator to HOL's
    `eval_def`/`crep_op_def`/`word_sh` for arbitrary HOL states and word types.
    The prior `@[hol]` claim was removed and its theorem-map row is classified
    `documented_mismatch`. Keep this support untagged until the exact evaluator
    relation and HOL-shaped polymorphic statement are proved. -/
theorem crepEvalMulConst {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n)) (constant value : RiscV.Word n)
    (h : (evalCrepRuntimeExp (riscvCrepWordTarget state) expression).map
        PanWordLab.word = some (.word value)) :
    (evalCrepRuntimeExp (riscvCrepWordTarget state)
        (crepMulConst (BitVec.ofNat n) expression constant)).map
      PanWordLab.word = some (.word (value * constant)) := by
  have hInjective : Function.Injective (PanWordLab.word : RiscV.Word n →
      PanWordLab (RiscV.Word n)) := by
    intro left right hEq
    cases hEq
    rfl
  have hRaw : evalCrepRuntimeExp (riscvCrepWordTarget state) expression =
      some value := by
    apply Option.map_injective hInjective
    simpa using h
  have hShift : ∀ word exponent, exponent < n →
      (riscvCrepWordTarget state).memoryModel.shift .lsl word
          (BitVec.ofNat n exponent) = some (word <<< exponent) := by
    intro word exponent hbound
    change RiscV.panRiscVShift .lsl word (BitVec.ofNat n exponent) = _
    have hfromNat : (BitVec.ofNat n exponent).toNat = exponent := by
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
        (Nat.pow_lt_pow_right (by decide) hbound)
    unfold RiscV.panRiscVShift
    rw [hfromNat]
    simp [hbound]
  have hResult := crepEvalMulConstForModel (riscvCrepWordTarget state)
    expression constant value hShift hRaw
  simpa using congrArg (Option.map PanWordLab.word) hResult

/-! Lean-only adapter from the explicit `PanWordLab.word` result shape to the
    raw production evaluator result used by the recursive simp proof. -/
theorem crepEvalMulConstRaw {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n)) (constant value : RiscV.Word n)
    (h : evalCrepRuntimeExp (riscvCrepWordTarget state) expression = some value) :
    evalCrepRuntimeExp (riscvCrepWordTarget state)
      (crepMulConst (BitVec.ofNat n) expression constant) = some (value * constant) := by
  have wordInjective : Function.Injective (PanWordLab.word : RiscV.Word n →
      PanWordLab (RiscV.Word n)) := by
    intro left right hEq
    cases hEq
    rfl
  have hWrapped :
      (evalCrepRuntimeExp (riscvCrepWordTarget state) expression).map
        PanWordLab.word = some (.word value) := by
    simpa using congrArg (Option.map PanWordLab.word) h
  have hResult := crepEvalMulConst state expression constant value hWrapped
  apply Option.map_injective wordInjective
  simpa using hResult

/-! Transport the production constant-multiplication support across the
    explicit finite-dimension representation. This is Flapjack-only proof
    infrastructure: it reduces the operation to the BitVec target, while the
    exact HOL-polymorphic theorem remains subject to the evaluator audit. -/
theorem crepEvalMulConstHolFiniteDimension {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) (constant value : ι → Bool)
    (h : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression =
      some value) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension)
      (crepMulConst
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression constant) = some (value * constant) := by
  letI : HolFiniteDimension ι := dimension
  have hSource := evalCrepRuntimeExp_finiteDimension_eq dimension state expression
  rw [hSource] at h
  simp only [evalCrepHolFiniteDimensionExp] at h
  cases hBits : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) expression) with
  | none => simp [hBits] at h
  | some bitVecValue =>
      have hValue : bitVecToHolWord dimension bitVecValue = value := by
        simpa [hBits] using h
      have hBitVecValue : bitVecValue = holWordToBitVec dimension value := by
        calc
          bitVecValue = holWordToBitVec dimension
              (bitVecToHolWord dimension bitVecValue) := by
                rw [holWordToBitVec_bitVecToHolWord]
          _ = holWordToBitVec dimension value := congrArg _ hValue
      have hBitVecEval :
          evalCrepRuntimeExp
            (riscvCrepWordTarget
              (state.toHolFiniteBitVecState dimension).toRuntime)
            (mapCrepExpWord (holWordToBitVec dimension) expression) =
            some (holWordToBitVec dimension value) := by
        rw [evalCrepRuntimeExp_toRuntime_eq]
        simpa [hBitVecValue] using hBits
      have hMul := crepEvalMulConstRaw
        ((state.toHolFiniteBitVecState dimension).toRuntime)
        (mapCrepExpWord (holWordToBitVec dimension) expression)
        (holWordToBitVec dimension constant) (holWordToBitVec dimension value)
        hBitVecEval
      have hRewrite := crepMulConst_holFiniteDimension expression constant
      have hResult := evalCrepRuntimeExp_finiteDimension_eq dimension state
        (crepMulConst
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression constant)
      rw [hResult]
      simp only [evalCrepHolFiniteDimensionExp]
      rw [hRewrite]
      rw [← evalCrepRuntimeExp_toRuntime_eq
        (state.toHolFiniteBitVecState dimension)
        (crepMulConst (BitVec.ofNat dimension.width)
          (mapCrepExpWord (holWordToBitVec dimension) expression)
          (holWordToBitVec dimension constant))]
      rw [hMul]
      simp only [Option.map_some]
      exact congrArg some (calc
        bitVecToHolWord dimension
            (holWordToBitVec dimension value * holWordToBitVec dimension constant) =
            bitVecToHolWord dimension
              (holWordToBitVec dimension (value * constant)) := by
                rw [holFiniteWordToBitVec_mul]
        _ = value * constant := bitVecToHolWord_holWordToBitVec dimension _)

private theorem holFiniteWord_mul_comm {ι : Type}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    right * left = left * right := by
  calc
    right * left = bitVecToHolWord dimension
        (holWordToBitVec dimension (right * left)) :=
          (bitVecToHolWord_holWordToBitVec dimension _).symm
    _ = bitVecToHolWord dimension
        (holWordToBitVec dimension right * holWordToBitVec dimension left) := by
          rw [holFiniteWordToBitVec_mul]
    _ = bitVecToHolWord dimension
        (holWordToBitVec dimension left * holWordToBitVec dimension right) := by
          rw [BitVec.mul_comm]
    _ = left * right := by
          rw [← holFiniteWordToBitVec_mul]
          exact bitVecToHolWord_holWordToBitVec dimension _

private theorem crepSimpMulEvalHolFiniteDimension {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (toRuntime : CrepHolState (ι → Bool) σ → CrepRuntimeState (ι → Bool) σ)
    (mulConst : ∀ (sourceState : CrepHolState (ι → Bool) σ)
      (expression : CrepExp (ι → Bool)) (constant value : ι → Bool),
      evalCrepRuntimeExp (toRuntime sourceState) expression = some value →
      evalCrepRuntimeExp (toRuntime sourceState)
        (crepMulConst
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression constant) = some (value * constant))
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hleft : evalCrepRuntimeExp (toRuntime state) (crepSimpExp
      (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)) left) =
        some leftValue)
    (hright : evalCrepRuntimeExp (toRuntime state) (crepSimpExp
      (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)) right) =
        some rightValue) :
    evalCrepRuntimeExp (toRuntime state) (crepSimpExp
      (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
      (.crepOp .mul [left, right])) = some (leftValue * rightValue) := by
  let fromNat := fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  let simpExp := fun expression => crepSimpExp fromNat expression
  change evalCrepRuntimeExp (toRuntime state) (simpExp left) = some leftValue at hleft
  change evalCrepRuntimeExp (toRuntime state) (simpExp right) = some rightValue at hright
  cases hL : crepDestConst (simpExp left) with
  | some leftConstant =>
      have hLshape := crepDestConst_eq_const (simpExp left) leftConstant hL
      cases hR : crepDestConst (simpExp right) with
      | some rightConstant =>
          have hRshape := crepDestConst_eq_const (simpExp right) rightConstant hR
          have hmulShape := crepSimpExp.eq_5 fromNat [left, right]
            leftConstant rightConstant (by simp [simpExp, hLshape, hRshape])
          rw [hmulShape]
          have hleftValue : leftConstant = leftValue := by
            rw [hLshape] at hleft
            simpa [evalCrepRuntimeExp] using hleft
          have hrightValue : rightConstant = rightValue := by
            rw [hRshape] at hright
            simpa [evalCrepRuntimeExp] using hright
          simp [evalCrepRuntimeExp, hleftValue, hrightValue, crepDestConst]
      | none =>
          have hRnotConst : ∀ value, simpExp right = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hR
          have hmulShape := crepSimpExp.eq_6 fromNat [left, right] leftConstant
            (simpExp right) hRnotConst (by simp [simpExp, hLshape])
          rw [hmulShape]
          have hleftValue : leftConstant = leftValue := by
            rw [hLshape] at hleft
            simpa [evalCrepRuntimeExp] using hleft
          have hmul := mulConst state (simpExp right) leftConstant rightValue hright
          calc
            evalCrepRuntimeExp (toRuntime state)
                (crepMulConst fromNat (simpExp right) leftConstant) =
                some (rightValue * leftConstant) := hmul
            _ = some (leftValue * rightValue) := by
              rw [hleftValue, holFiniteWord_mul_comm]
  | none =>
      cases hR : crepDestConst (simpExp right) with
      | some rightConstant =>
          have hRshape := crepDestConst_eq_const (simpExp right) rightConstant hR
          have hLnotConst : ∀ value, simpExp left = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hL
          have hmulShape := crepSimpExp.eq_7 fromNat [left, right]
            (simpExp left) rightConstant hLnotConst (by simp [simpExp, hRshape])
          rw [hmulShape]
          have hrightValue : rightConstant = rightValue := by
            rw [hRshape] at hright
            simpa [evalCrepRuntimeExp] using hright
          have hmul := mulConst state (simpExp left) rightConstant leftValue
            (by simpa [simpExp] using hleft)
          simpa [hrightValue, crepDestConst] using hmul
      | none =>
          have hLnotConst : ∀ value, simpExp left = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hL
          have hRnotConst : ∀ value, simpExp right = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hR
          have hnotConstConst : ∀ a b, CrepOp.mul = CrepOp.mul →
              List.map simpExp [left, right] = [.const a, .const b] → False := by
            intro a b _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hLnotConst a hmap.1
          have hnotLeftConst : ∀ c expression, CrepOp.mul = CrepOp.mul →
              List.map simpExp [left, right] = [.const c, expression] → False := by
            intro c expression _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hLnotConst c hmap.1
          have hnotRightConst : ∀ expression c, CrepOp.mul = CrepOp.mul →
              List.map simpExp [left, right] = [expression, .const c] → False := by
            intro expression c _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hRnotConst c hmap.2.1
          have hmulShape := crepSimpExp.eq_8 fromNat [left, right]
            CrepOp.mul hnotConstConst hnotLeftConst hnotRightConst
          rw [hmulShape]
          simp [evalCrepRuntimeExp, crepOpCrep, simpExp, hleft, hright]

/-! All-width preservation for the production evaluator on an explicitly
    enumerated Boolean-index word. The statement mirrors HOL's successful-
    evaluation premise and evaluator equality, but remains untagged because
    its Lean word representation and operation instances are the explicit
    finite-dimension/BitVec interpretation described above. -/
private theorem crepSimpExpEvalPreservesHolFiniteDimensionWithRuntime {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (toRuntime : CrepHolState (ι → Bool) σ → CrepRuntimeState (ι → Bool) σ)
    (mulConst : ∀ (sourceState : CrepHolState (ι → Bool) σ)
      (expression : CrepExp (ι → Bool)) (constant value : ι → Bool),
      evalCrepRuntimeExp (toRuntime sourceState) expression = some value →
      evalCrepRuntimeExp (toRuntime sourceState)
        (crepMulConst
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression constant) = some (value * constant))
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool))
    (h : evalCrepRuntimeExp (toRuntime state) expression ≠ none) :
    evalCrepRuntimeExp (toRuntime state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)) expression) =
    evalCrepRuntimeExp (toRuntime state) expression := by
  let fromNat := fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  have evalExpsMapM (sourceState : CrepHolState (ι → Bool) σ) :
      ∀ expressions,
        evalCrepRuntimeExps (toRuntime sourceState) expressions =
          expressions.mapM
            (evalCrepRuntimeExp (toRuntime sourceState)) := by
    intro expressions
    induction expressions with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExp (toRuntime state) e ≠ none →
            evalCrepRuntimeExp (toRuntime state)
              (crepSimpExp fromNat e) =
            evalCrepRuntimeExp (toRuntime state) e) ∧
        (∀ (state : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExps (toRuntime state) expressions ≠ none →
            evalCrepRuntimeExps (toRuntime state)
              (expressions.map (crepSimpExp fromNat)) =
            evalCrepRuntimeExps (toRuntime state) expressions)))
      generalizing state
  case const value => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case var name => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case load address ih =>
    rw [crepSimpExp.eq_1]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (toRuntime state) address with
    | none => simp [hx] at h
    | some value =>
        have hi := ih state (by simp [hx])
        rw [hi, hx]
  case load32 address ih =>
    rw [crepSimpExp.eq_2]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (toRuntime state) address with
    | none => simp [hx] at h
    | some value =>
        have hi := ih state (by simp [hx])
        rw [hi, hx]
  case loadByte address ih =>
    rw [crepSimpExp.eq_3]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (toRuntime state) address with
    | none => simp [hx] at h
    | some value =>
        have hi := ih state (by simp [hx])
        rw [hi, hx]
  case loadGlob address => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case op operator expressions ih =>
    rw [crepSimpExp.eq_4]
    simp only [evalCrepRuntimeExp] at h ⊢
    rw [← evalExpsMapM state expressions] at h
    cases hx : evalCrepRuntimeExps
        (toRuntime state) expressions with
    | none => simp [hx] at h
    | some values =>
        have hOriginal : expressions.mapM
            (evalCrepRuntimeExp (toRuntime state)) = some values := by
          rw [← evalExpsMapM state expressions]
          exact hx
        have hSimplified : expressions.mapM
            (fun expression => evalCrepRuntimeExp (toRuntime state)
              (crepSimpExp fromNat expression)) = some values := by
          apply optMmapEqSomeMono
            (evalCrepRuntimeExp (toRuntime state))
            (fun expression => evalCrepRuntimeExp (toRuntime state)
              (crepSimpExp fromNat expression)) expressions values hOriginal
          intro expression value hmem heval
          have hSuccessful :
              evalCrepRuntimeExp (toRuntime state) expression ≠ none := by
            rw [heval]
            simp
          have hPreserved := ih.1 expression hmem state hSuccessful
          rw [hPreserved, heval]
        have hMapMapM (xs : List (CrepExp (ι → Bool))) :
            (xs.map (crepSimpExp fromNat)).mapM
                (evalCrepRuntimeExp (toRuntime state)) =
              xs.mapM (fun expression => evalCrepRuntimeExp (toRuntime state)
                (crepSimpExp fromNat expression)) := by
          induction xs with
          | nil => rfl
          | cons head tail ihTail => simp [List.mapM_cons, ihTail]
        have hSimplifiedMapped :
            (expressions.map (crepSimpExp fromNat)).mapM
                (evalCrepRuntimeExp (toRuntime state)) = some values := by
          rw [hMapMapM]
          exact hSimplified
        rw [hSimplifiedMapped, hOriginal]
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil => simp [evalCrepRuntimeExp] at h
    | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp] at h
      | cons right rest =>
        cases rest with
        | cons extra tail => simp [evalCrepRuntimeExp] at h
        | nil =>
          have hleft : evalCrepRuntimeExp
              (toRuntime state) (crepSimpExp fromNat left) ≠ none := by
            have hleftRaw : evalCrepRuntimeExp (toRuntime state) left ≠ none := by
              intro hn
              simp [evalCrepRuntimeExp, hn] at h
            rw [ih.1 left (by simp) state hleftRaw]
            exact hleftRaw
          have hright : evalCrepRuntimeExp
              (toRuntime state) (crepSimpExp fromNat right) ≠ none := by
            have hrightRaw : evalCrepRuntimeExp (toRuntime state) right ≠ none := by
              intro hn
              simp [evalCrepRuntimeExp, hn] at h
            rw [ih.1 right (by simp) state hrightRaw]
            exact hrightRaw
          obtain ⟨leftValue, hleftValue⟩ := Option.ne_none_iff_exists'.mp hleft
          obtain ⟨rightValue, hrightValue⟩ := Option.ne_none_iff_exists'.mp hright
          have hmul := crepSimpMulEvalHolFiniteDimension dimension toRuntime mulConst
            state left right leftValue rightValue hleftValue hrightValue
          calc
            evalCrepRuntimeExp (toRuntime state)
                (crepSimpExp fromNat (.crepOp .mul [left, right])) =
                some (leftValue * rightValue) := hmul
            _ = evalCrepRuntimeExp (toRuntime state)
                  (.crepOp .mul [left, right]) := by
                simp [evalCrepRuntimeExp, crepOpCrep, ← ih.1 left (by simp) state
                  (by intro hn; simp [evalCrepRuntimeExp, hn] at h),
                  ← ih.1 right (by simp) state
                    (by intro hn; simp [evalCrepRuntimeExp, hn] at h),
                  hleftValue, hrightValue]
  case cmp operator left right ihLeft ihRight =>
    rw [crepSimpExp.eq_9]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (toRuntime state) left with
    | none => simp [hx] at h
    | some leftValue =>
      cases hy : evalCrepRuntimeExp (toRuntime state) right with
      | none => simp [hx, hy] at h
      | some rightValue =>
        have hleft := ihLeft state (by simp [hx])
        have hright := ihRight state (by simp [hy])
        rw [hleft, hright, hx, hy]
  case shift operator left right ihLeft ihRight =>
    rw [crepSimpExp.eq_10]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (toRuntime state) left with
    | none => simp [hx] at h
    | some leftValue =>
      cases hy : evalCrepRuntimeExp (toRuntime state) right with
      | none => simp [hx, hy] at h
      | some rightValue =>
        have hleft := ihLeft state (by simp [hx])
        have hright := ihRight state (by simp [hy])
        rw [hleft, hright, hx, hy]
  case baseAddr => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case topAddr => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state h
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state h
      · exact ihTail.1 e he state h
    · intro state h
      rw [evalExpsMapM state (List.map (crepSimpExp fromNat) (head :: tail))]
      rw [evalExpsMapM state (head :: tail)]
      simp only [List.map_cons]
      cases hx : evalCrepRuntimeExp
          (toRuntime state) head with
      | none => simp [evalCrepRuntimeExps, hx] at h
      | some headValue =>
        cases hy : evalCrepRuntimeExps (toRuntime state) tail with
        | none => simp [evalCrepRuntimeExps, hx, hy] at h
        | some tailValues =>
          have hHead := ihHead state (by simp [hx])
          have hTail := ihTail.2 state (by simp [hy])
          rw [hx] at hHead
          change evalCrepRuntimeExp (toRuntime state)
              (crepSimpExp fromNat head) = some headValue at hHead
          rw [evalExpsMapM state (List.map (crepSimpExp fromNat) tail)] at hTail
          rw [hy] at hTail
          have hTailOriginal :
              List.mapM (evalCrepRuntimeExp (toRuntime state)) tail = some tailValues := by
            rw [← evalExpsMapM state tail]
            exact hy
          simp [hHead, hx, hTail, hTailOriginal]

theorem crepSimpExpEvalPreservesHolFiniteDimension {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool))
    (h : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression ≠ none) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)) expression) =
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression := by
  apply crepSimpExpEvalPreservesHolFiniteDimensionWithRuntime dimension
    (fun sourceState => sourceState.toHolFiniteWordRuntime dimension)
    (fun sourceState expression constant value hEval =>
      crepEvalMulConstHolFiniteDimension dimension sourceState expression constant value hEval)
    state expression h

/-! This target-specific helper proves the hard `CrepOp.mul` case of the
    recursive `simp_exp` preservation argument. It uses the generated
    `crepSimpExp` equations, the width-parametric word port of HOL
    `dest_const_thm`, and the untagged RISC-V multiplication support; the HOL
    evaluator correspondence gap documented above remains open. -/
theorem crepSimpMulEval {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (left right : CrepExp (RiscV.Word n)) (leftValue rightValue : RiscV.Word n)
    (hleft : evalCrepRuntimeExp (riscvCrepWordTarget state)
      (crepSimpExp (BitVec.ofNat n) left) = some leftValue)
    (hright : evalCrepRuntimeExp (riscvCrepWordTarget state)
      (crepSimpExp (BitVec.ofNat n) right) = some rightValue) :
    evalCrepRuntimeExp (riscvCrepWordTarget state)
      (crepSimpExp (BitVec.ofNat n) (.crepOp .mul [left, right])) =
        some (leftValue * rightValue) := by
  cases hL : crepDestConst (crepSimpExp (BitVec.ofNat n) left) with
  | some leftConstant =>
      have hLshape := crepDestConstWord_eq_const
        (crepSimpExp (BitVec.ofNat n) left) leftConstant hL
      cases hR : crepDestConst (crepSimpExp (BitVec.ofNat n) right) with
      | some rightConstant =>
          have hRshape := crepDestConstWord_eq_const
            (crepSimpExp (BitVec.ofNat n) right) rightConstant hR
          have hmulShape := crepSimpExp.eq_5 (BitVec.ofNat n) [left, right]
            leftConstant rightConstant (by simp [hLshape, hRshape])
          rw [hmulShape]
          have hleftValue : leftConstant = leftValue := by
            simpa [hLshape, evalCrepRuntimeExp] using hleft
          have hrightValue : rightConstant = rightValue := by
            simpa [hRshape, evalCrepRuntimeExp] using hright
          simp [evalCrepRuntimeExp, hleftValue, hrightValue, crepDestConst]
      | none =>
          have hRnotConst : ∀ value,
              crepSimpExp (BitVec.ofNat n) right = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hR
          have hmulShape := crepSimpExp.eq_6 (BitVec.ofNat n) [left, right]
            leftConstant (crepSimpExp (BitVec.ofNat n) right) hRnotConst
            (by simp [hLshape])
          rw [hmulShape]
          have hleftValue : leftConstant = leftValue := by
            simpa [hLshape, evalCrepRuntimeExp] using hleft
          have hmul := crepEvalMulConstRaw state (crepSimpExp (BitVec.ofNat n) right)
            leftConstant rightValue hright
          simpa [hleftValue, BitVec.mul_comm, crepDestConst] using hmul
  | none =>
      cases hR : crepDestConst (crepSimpExp (BitVec.ofNat n) right) with
      | some rightConstant =>
          have hRshape := crepDestConstWord_eq_const
            (crepSimpExp (BitVec.ofNat n) right) rightConstant hR
          have hLnotConst : ∀ value,
              crepSimpExp (BitVec.ofNat n) left = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hL
          have hmulShape := crepSimpExp.eq_7 (BitVec.ofNat n) [left, right]
            (crepSimpExp (BitVec.ofNat n) left) rightConstant hLnotConst
            (by simp [hRshape])
          rw [hmulShape]
          have hrightValue : rightConstant = rightValue := by
            simpa [hRshape, evalCrepRuntimeExp] using hright
          have hmul := crepEvalMulConstRaw state (crepSimpExp (BitVec.ofNat n) left)
            rightConstant leftValue (by simpa [hRshape] using hleft)
          simpa [hrightValue, crepDestConst] using hmul
      | none =>
          have hLnotConst : ∀ value,
              crepSimpExp (BitVec.ofNat n) left = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hL
          have hRnotConst : ∀ value,
              crepSimpExp (BitVec.ofNat n) right = .const value → False := by
            intro value heq
            simp [heq, crepDestConst] at hR
          have hnotConstConst : ∀ a b, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat n)) [left, right] =
                [.const a, .const b] → False := by
            intro a b _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hLnotConst a hmap.1
          have hnotLeftConst : ∀ c expression, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat n)) [left, right] =
                [.const c, expression] → False := by
            intro c expression _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hLnotConst c hmap.1
          have hnotRightConst : ∀ expression c, CrepOp.mul = CrepOp.mul →
              List.map (crepSimpExp (BitVec.ofNat n)) [left, right] =
                [expression, .const c] → False := by
            intro expression c _ hmap
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmap
            exact hRnotConst c hmap.2.1
          have hmulShape := crepSimpExp.eq_8 (BitVec.ofNat n) [left, right]
            CrepOp.mul hnotConstConst hnotLeftConst hnotRightConst
          rw [hmulShape]
          simp [evalCrepRuntimeExp, crepOpCrep, hleft, hright]

/-! This width-generic preservation lemma follows the successful-evaluation
    induction for HOL simp_exp_correct1, but its evaluator remains the
    RISC-V-specialized production evalCrepRuntimeExp; it is not tagged as a
    HOL theorem. -/
theorem crepSimpExpEvalPreserves {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n))
    (h : evalCrepRuntimeExp (riscvCrepWordTarget state) expression ≠ none) :
    evalCrepRuntimeExp (riscvCrepWordTarget state)
      (crepSimpExp (BitVec.ofNat n) expression) =
    evalCrepRuntimeExp (riscvCrepWordTarget state) expression := by
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepRuntimeState (RiscV.Word n) σ),
          evalCrepRuntimeExp (riscvCrepWordTarget state) e ≠ none →
            evalCrepRuntimeExp (riscvCrepWordTarget state) (crepSimpExp (BitVec.ofNat n) e) =
              evalCrepRuntimeExp (riscvCrepWordTarget state) e) ∧
        (∀ (state : CrepRuntimeState (RiscV.Word n) σ),
          evalCrepRuntimeExps (riscvCrepWordTarget state) expressions ≠ none →
            evalCrepRuntimeExps (riscvCrepWordTarget state)
              (expressions.map (crepSimpExp (BitVec.ofNat n))) =
            evalCrepRuntimeExps (riscvCrepWordTarget state) expressions)))
      generalizing state
  case const value => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case var name => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case load address ih =>
    rw [crepSimpExp.eq_1]
    simp only [evalCrepRuntimeExp]
    cases hx : evalCrepRuntimeExp (riscvCrepWordTarget state) address with
    | none => simp [hx, evalCrepRuntimeExp] at h
    | some value =>
      have hi := ih state (by simp [hx])
      rw [hi, hx]
  case load32 address ih =>
    rw [crepSimpExp.eq_2]
    simp only [evalCrepRuntimeExp]
    cases hx : evalCrepRuntimeExp (riscvCrepWordTarget state) address with
    | none => simp [hx, evalCrepRuntimeExp] at h
    | some value =>
      have hi := ih state (by simp [hx])
      rw [hi, hx]
  case loadByte address ih =>
    rw [crepSimpExp.eq_3]
    simp only [evalCrepRuntimeExp]
    cases hx : evalCrepRuntimeExp (riscvCrepWordTarget state) address with
    | none => simp [hx, evalCrepRuntimeExp] at h
    | some value =>
      have hi := ih state (by simp [hx])
      rw [hi, hx]
  case loadGlob address => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case op operator expressions ih =>
    have evalExpsMapM (targetState : CrepRuntimeState (RiscV.Word n) σ) :
        ∀ expressions,
          evalCrepRuntimeExps (riscvCrepWordTarget targetState) expressions =
            expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget targetState)) := by
      intro xs
      induction xs with
      | nil => simp [evalCrepRuntimeExps]
      | cons head tail ih => simp [evalCrepRuntimeExps, ih]
    rw [crepSimpExp.eq_4]
    simp only [evalCrepRuntimeExp] at h ⊢
    rw [← evalExpsMapM state expressions] at h
    cases hx : evalCrepRuntimeExps (riscvCrepWordTarget state) expressions with
    | none => simp [hx] at h
    | some values =>
      have hi := ih.2 state (by simp [hx])
      rw [← evalExpsMapM state (expressions.map (crepSimpExp (BitVec.ofNat n))),
        ← evalExpsMapM state expressions, hi]
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil => simp [evalCrepRuntimeExp] at h
    | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp] at h
      | cons right rest =>
        cases rest with
        | cons extra tail => simp [evalCrepRuntimeExp] at h
        | nil =>
          have hleft : evalCrepRuntimeExp (riscvCrepWordTarget state) left ≠ none := by
            intro hn
            simp [evalCrepRuntimeExp, hn] at h
          have hright : evalCrepRuntimeExp (riscvCrepWordTarget state) right ≠ none := by
            intro hn
            simp [evalCrepRuntimeExp, hn] at h
          have hleftSimp := ih.1 left (by simp) state hleft
          have hrightSimp := ih.1 right (by simp) state hright
          have hleftSimpNe : evalCrepRuntimeExp (riscvCrepWordTarget state)
              (crepSimpExp (BitVec.ofNat n) left) ≠ none := by
            rw [hleftSimp]
            exact hleft
          have hrightSimpNe : evalCrepRuntimeExp (riscvCrepWordTarget state)
              (crepSimpExp (BitVec.ofNat n) right) ≠ none := by
            rw [hrightSimp]
            exact hright
          obtain ⟨leftValue, hleftValue⟩ := Option.ne_none_iff_exists'.mp hleftSimpNe
          obtain ⟨rightValue, hrightValue⟩ := Option.ne_none_iff_exists'.mp hrightSimpNe
          have hmul := crepSimpMulEval state left right leftValue rightValue
            hleftValue hrightValue
          calc
            evalCrepRuntimeExp (riscvCrepWordTarget state)
                (crepSimpExp (BitVec.ofNat n) (.crepOp .mul [left, right])) =
                some (leftValue * rightValue) := hmul
            _ = evalCrepRuntimeExp (riscvCrepWordTarget state) (.crepOp .mul [left, right]) := by
              simp [evalCrepRuntimeExp, crepOpCrep, ← hleftSimp, ← hrightSimp,
                hleftValue, hrightValue]
  case cmp operator left right ihl ihr =>
    rw [crepSimpExp.eq_9]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (riscvCrepWordTarget state) left with
    | none => simp [hx] at h
    | some leftValue =>
      cases hy : evalCrepRuntimeExp (riscvCrepWordTarget state) right with
      | none => simp [hx, hy] at h
      | some rightValue =>
        have hleft := ihl state (by simp [hx])
        have hright := ihr state (by simp [hy])
        rw [hleft, hright, hx, hy]
  case shift operator left right ihl ihr =>
    rw [crepSimpExp.eq_10]
    simp only [evalCrepRuntimeExp] at h ⊢
    cases hx : evalCrepRuntimeExp (riscvCrepWordTarget state) left with
    | none => simp [hx] at h
    | some leftValue =>
      cases hy : evalCrepRuntimeExp (riscvCrepWordTarget state) right with
      | none => simp [hx, hy] at h
      | some rightValue =>
        have hleft := ihl state (by simp [hx])
        have hright := ihr state (by simp [hy])
        rw [hleft, hright, hx, hy]
  case baseAddr => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case topAddr => simp [crepSimpExp.eq_11, evalCrepRuntimeExp]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state heval
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state heval
      · exact ihTail.1 e he state heval
    · intro state hxs
      cases hh : evalCrepRuntimeExp (riscvCrepWordTarget state) head with
      | none => simp [evalCrepRuntimeExps, hh] at hxs
      | some headValue =>
        have htail : evalCrepRuntimeExps (riscvCrepWordTarget state) tail ≠ none := by
          intro ht
          simp [evalCrepRuntimeExps, hh, ht] at hxs
        have hheadSimp := ihHead state (by simp [hh])
        have htailSimp := ihTail.2 state htail
        simp [evalCrepRuntimeExps, hh, hheadSimp, htailSimp]


/-- Flapjack representation of HOL's local `mapc f` state update through
    `FMAP_MAP2`: apply `f` to each `(functionName, storedEntry)` pair and leave
    every other runtime field alone. -/
def crepArithMapCode {α : Type}
    (f : FunName × (List Nat × CrepProg α) → List Nat × CrepProg α)
    (state : CrepRuntimeState α σ) :
    CrepRuntimeState α σ :=
  { state with code := fun name =>
      (state.code name).map (fun entry => f (name, entry)) }

/-! Internal evaluator lemma: `evalCrepRuntimeExp` reads locals, globals,
    memory, and target operations but never the code map. It is generic in the
    word carrier and leaves every target field arbitrary, so it captures the
    code-map irrelevance part of HOL's local `mapc f` step for callbacks that
    inspect the function key as well as the stored entry. It is infrastructure
    rather than a HOL theorem. -/
private theorem crepEvalCodeMapIrrel {α : Type} [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    {σ : Type}
    (f : FunName × (List Nat × CrepProg α) → List Nat × CrepProg α)
    (state : CrepRuntimeState α σ) (expression : CrepExp α) :
    evalCrepRuntimeExp (crepArithMapCode f state) expression =
      evalCrepRuntimeExp state expression := by
  have evalExpsMapM (targetState : CrepRuntimeState α σ) :
      ∀ expressions,
        evalCrepRuntimeExps targetState expressions =
          expressions.mapM (evalCrepRuntimeExp targetState) := by
    intro expressions
    induction expressions with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        ∀ (state : CrepRuntimeState α σ)
          (f : FunName × (List Nat × CrepProg α) → List Nat × CrepProg α),
          (∀ e, e ∈ expressions →
            evalCrepRuntimeExp (crepArithMapCode f state) e =
              evalCrepRuntimeExp state e) ∧
          evalCrepRuntimeExps (crepArithMapCode f state) expressions =
            evalCrepRuntimeExps state expressions))
    generalizing state f <;>
    all_goals try simp_all [crepArithMapCode, evalCrepRuntimeExp,
      crepRuntimeLoad, crepRuntimeLoad32, crepRuntimeLoadByte]
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil => simp [evalCrepRuntimeExp]
    | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp]
      | cons right rest =>
        cases rest with
        | nil =>
          simp only [evalCrepRuntimeExp]
          rw [ih state f |>.1 left (by simp)]
          rw [ih state f |>.1 right (by simp)]
        | cons _ _ => simp [evalCrepRuntimeExp]

/-! The following theorem assembles the all-constructor preservation proof
    over an arbitrary explicitly enumerated finite Boolean-index word carrier.
    It retains the successful-evaluation premise, arbitrary local `mapc f`
    code update, and complete optional word-lab result: HOL's `word_lab` and
    Lean's `PanWordLab` each have only the `Word` constructor. It remains
    untagged as HOL `simp_exp_correct1` because this theorem runs the
    compiler's canonical RISC-V runtime, whose memory model is target-specific.
    The all-width source runtime below uses the same finite-index dimension
    witness with HOL-shaped memory operations. The two runtime configurations
    differ at width 24: HOL maps `byte_align 5w` to 4, while the RISC-V model
    with `bytesInWord = 3` maps address 5 to 3. See
    `PanFixedLoadParity.holByteAlignWidth24Address5` and the direct HOL row in
    `pan_fixed_load_probe.out`. This remains an untagged target specialization,
    not the polymorphic HOL theorem. -/
theorem crepSimpExpCorrect1HolFiniteDimension {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (h : (evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression).map
      PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      ((crepArithMapCode f (state.toHolFiniteWordRuntime dimension)))
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word =
    (evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression).map
      PanWordLab.word := by
  let runtime := state.toHolFiniteWordRuntime dimension
  let fromNat := fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  have hraw : evalCrepRuntimeExp runtime expression ≠ none := by
    simpa using h
  have hsimp := crepSimpExpEvalPreservesHolFiniteDimension dimension state
    expression hraw
  calc
    (evalCrepRuntimeExp (crepArithMapCode f runtime)
        (crepSimpExp fromNat expression)).map PanWordLab.word =
        (evalCrepRuntimeExp runtime (crepSimpExp fromNat expression)).map
          PanWordLab.word := by
            exact congrArg (Option.map PanWordLab.word)
              (crepEvalCodeMapIrrel f runtime (crepSimpExp fromNat expression))
    _ = (evalCrepRuntimeExp runtime expression).map PanWordLab.word :=
      congrArg (Option.map PanWordLab.word) hsimp

def crepArithHolFiniteDimensionMapCode {ι : Type} {σ : Type}
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) : CrepHolState (ι → Bool) σ :=
  { state with code := fun name =>
      (state.code name).map (fun entry => f (name, entry)) }

theorem crepArithHolFiniteDimensionMapCode_runtime {ι : Type}
    (dimension : HolFiniteDimension ι) {σ : Type}
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) :
    (crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordRuntime dimension =
      crepArithMapCode f (state.toHolFiniteWordRuntime dimension) := by
  cases state
  rfl

/-! Source-state-shaped all-width corollary. This has HOL's premise, mapc
    update, simplifier, and complete option/word_lab result, and its proof
    rewrites through the production evaluator theorem above. It is kept
    untagged because the source evaluator is represented through an explicit
    `HolFiniteDimension` enumeration and BitVec/RISC-V operations, so the
    unrestricted HOL word-carrier correspondence is still unproved. -/
theorem crepSimpExpCorrect1HolFiniteDimensionSource {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (h : evalCrepHolFiniteDimensionExpWordLab dimension state expression ≠ none) :
    evalCrepHolFiniteDimensionExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) expression) =
    evalCrepHolFiniteDimensionExpWordLab dimension state expression := by
  have hEvalSource (source : CrepHolState (ι → Bool) σ)
      (e : CrepExp (ι → Bool)) :
      evalCrepHolFiniteDimensionExpWordLab dimension source e =
        (evalCrepRuntimeExp (source.toHolFiniteWordRuntime dimension) e).map
          PanWordLab.word := by
    simp only [evalCrepHolFiniteDimensionExpWordLab]
    rw [← evalCrepRuntimeExp_finiteDimension_eq dimension source e]
  have hSourceRuntime := hEvalSource state expression
  have hRuntime :
      (evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression).map
        PanWordLab.word ≠ none := by
    simpa [hSourceRuntime] using h
  have hMapRuntime := hEvalSource (crepArithHolFiniteDimensionMapCode f state)
    (crepSimpExp (fun n => bitVecToHolWord dimension
      (BitVec.ofNat dimension.width n)) expression)
  calc
    evalCrepHolFiniteDimensionExpWordLab dimension
        (crepArithHolFiniteDimensionMapCode f state)
        (crepSimpExp (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) expression) =
        (evalCrepRuntimeExp
          ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordRuntime dimension)
          (crepSimpExp (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word :=
          hMapRuntime
    _ = (evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension)
          expression).map PanWordLab.word := by
          rw [crepArithHolFiniteDimensionMapCode_runtime]
          exact crepSimpExpCorrect1HolFiniteDimension f state expression hRuntime
    _ = evalCrepHolFiniteDimensionExpWordLab dimension state expression :=
      hSourceRuntime.symm

/-! This source-runtime corollary runs the recursive preservation induction
    over the finite-word runtime whose byte loads use the HOL-shaped source
    memory model. `evalCrepRuntimeExp_sourceWord_eq` proves that production
    evaluation over this adapter equals the recursive source equations for
    each dimension. It remains support rather than a HOL tag because the
    compiler's canonical RISC-V runtime selects a different memory model at
    some widths, and no all-width relation between those production
    configurations is proved. -/
theorem crepSimpExpEvalPreservesHolFiniteWordSource {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool))
    (h : evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression ≠ none) :
    evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression) =
    evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression := by
  apply crepSimpExpEvalPreservesHolFiniteDimensionWithRuntime dimension
    (fun sourceState => sourceState.toHolFiniteWordSourceRuntime dimension)
    (fun sourceState expression constant value hEval =>
      crepEvalMulConstHolFiniteWordSource dimension sourceState expression
        constant value hEval)
    state expression h

theorem crepArithHolFiniteDimensionSourceMapCode_runtime {ι : Type}
    (dimension : HolFiniteDimension ι) {σ : Type}
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) :
    (crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
        dimension =
      crepArithMapCode f (state.toHolFiniteWordSourceRuntime dimension) := by
  cases state
  rfl

/-- Full-result all-width support for HOL `simp_exp_correct1` over the
    production evaluator configured with the source-shaped finite-word memory
    model. This keeps the successful-evaluation premise and the entire
    `Option (PanWordLab word)` result, including its HOL `word_lab` wrapper;
    `f` changes only the code map. It remains untagged because the explicit
    finite-index carrier and its primitive operations have not yet been proved
    identical to HOL's implicit `finite_index`/`crepSem$eval` interpretation.
    The unused result binder mirrors HOL's `!s exp v` shape. -/
theorem crepSimpExpCorrect1HolFiniteWordSourceRuntime {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (_v : PanWordLab (ι → Bool))
    (h : evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression ≠ none) :
    (evalCrepRuntimeExp
      ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
        dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word := by
  let runtime := state.toHolFiniteWordSourceRuntime dimension
  have hsimp := crepSimpExpEvalPreservesHolFiniteWordSource
    dimension state expression h
  calc
    (evalCrepRuntimeExp
        ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
          dimension)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression)).map PanWordLab.word =
      (evalCrepRuntimeExp (crepArithMapCode f runtime)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression)).map PanWordLab.word := by
            rw [crepArithHolFiniteDimensionSourceMapCode_runtime]
    _ = (evalCrepRuntimeExp runtime
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression)).map PanWordLab.word := by
            exact congrArg (Option.map PanWordLab.word)
              (crepEvalCodeMapIrrel f runtime (crepSimpExp
                (fun n => bitVecToHolWord dimension
                  (BitVec.ofNat dimension.width n)) expression))
    _ = (evalCrepRuntimeExp runtime expression).map PanWordLab.word :=
      congrArg (Option.map PanWordLab.word) hsimp

/-- The `Const` case of CakeML's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). This case has the original success
    premise, arbitrary code-map update, simplifier, and complete
    `Option word_lab` equality. Both sides reduce directly to
    `SOME (Word value)`, so it requires no evaluator correspondence beyond
    the defining `Const` equations. It is one constructor case, not the full
    recursive theorem. -/
def crepArithHolMapCode {n : Nat} {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) :
    CrepHolState (RiscV.Word n) σ :=
  { state with code := fun name =>
      (state.code name).map (fun entry => f (name, entry)) }

/-- Apply the Crep arithmetic simplifier to the body stored at every function
    name, preserving the declaration's parameter list. This is the Lean
    function-map form of the `FMAP_MAP2` code transformation used by the local
    `lookup_code` lemma in `crep_arithProofScript.sml`. -/
def crepArithSimpCodeMap {α : Type} [BEq α] [OfNat α 0] [OfNat α 1]
    [Mul α] [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (fromNat : Nat → α)
    (code : FunName → Option (List Nat × CrepProg α)) :
    FunName → Option (List Nat × CrepProg α) :=
  fun name => (code name).map fun (parameters, body) =>
    (parameters, crepSimpProg fromNat body)

/-- Flapjack's generic lookup/simplification commuting lemma. This is not yet
    tagged as HOL `crep_arithProofScript.sml:162` `lookup_code`: HOL quantifies
    over word-valued Crep programs, whereas this lemma accepts arbitrary `α`.
    The exact width-indexed theorem is tracked by bead flapjack-pxn.18.5.4.4. -/
theorem crepArithLookupCodeSimpProg {α : Type}
    [BEq α] [OfNat α 0] [OfNat α 1] [Mul α] [AndOp α]
    [ShiftRight α] [PanShiftWidth α]
    (fromNat : Nat → α)
    (code : FunName → Option (List Nat × CrepProg α))
    (fname : FunName) (args : List (PanWordLab α)) (_len : Nat) :
    lookupCrepHolCode (crepArithSimpCodeMap fromNat code) fname args _len =
      (lookupCrepHolCode code fname args _len).map
        (fun (body, locals) => (crepSimpProg fromNat body, locals)) := by
  unfold lookupCrepHolCode crepArithSimpCodeMap FLOOKUP
  cases hlookup : code fname with
  | none => simp [hlookup]
  | some entry =>
      rcases entry with ⟨parameters, body⟩
      by_cases hvalid : parameters.length = args.length ∧ parameters.Nodup
      · simp [hlookup, hvalid]
      · simp [hlookup, hvalid]

/-- Width-indexed form of the local HOL `lookup_code` theorem
    (`crep_arithProofScript.sml:162-168`). The equation itself matches the
    source `FMAP_MAP2`/`OPTION_MAP (simp_prog ## I)` commute law at
    `RiscV.Word width`, but the statement is keyed by the production
    `lookupCrepHolCodeW` carrier whose function names are `FunName = String`,
    whereas HOL `crepSemScript.sml:17` defines `funname = mlstring`. It is
    therefore FLAPJACK-SPECIFIC (not an exact HOL port); the exact
    MlString-keyed replacement is tracked by `flapjack-4w9`, with dependency
    `flapjack-pxn.18.3.5.8`. The `@[hol]` tag is withheld until the carrier is
    exact. The generic helper above also remains untagged. -/
theorem crepArithLookupCodeSimpProgW {width : Nat} [NeZero width]
    (code : FunName → Option (List Nat × CrepProg (RiscV.Word width)))
    (fname : FunName) (args : List (PanWordLab (RiscV.Word width)))
    (len : Nat) :
    lookupCrepHolCodeW
        (crepArithSimpCodeMap (BitVec.ofNat width) code) fname args len =
      (lookupCrepHolCodeW code fname args len).map
        (fun (body, locals) =>
          (crepSimpProg (BitVec.ofNat width) body, locals)) := by
  simpa [lookupCrepHolCodeW] using
    (crepArithLookupCodeSimpProg
      (fromNat := BitVec.ofNat width) code fname args len)

/-- Flapjack-specific `Const` case corresponding to part of CakeML's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It specializes the
    HOL-polymorphic word carrier to `RiscV.Word n`, so it is deliberately not
    tagged as a HOL case. Within that specialization, both sides reduce by
    the defining `Const` evaluator equations. -/
theorem crepSimpExpCorrect1ConstCase {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) (value : RiscV.Word n)
    (_result : PanWordLab (RiscV.Word n))
    (_h : evalCrepHolExpWordLab state (.const value) ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) (.const value)) =
    evalCrepHolExpWordLab state (.const value) := by
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11]

/-- Flapjack-specific `Var` case corresponding to CakeML's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It specializes the
    HOL-polymorphic word carrier to `RiscV.Word n`, so it is deliberately not
    tagged as a HOL case. Within that specialization, `mapc f` changes only
    code and the local value is unchanged. -/
theorem crepSimpExpCorrect1VarCase {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) (name : Nat)
    (_result : PanWordLab (RiscV.Word n))
    (_h : evalCrepHolExpWordLab state (.var name) ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) (.var name)) =
    evalCrepHolExpWordLab state (.var name) := by
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11,
    crepArithHolMapCode]

/-- Flapjack-specific `LoadGlob` case corresponding to CakeML's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It specializes the
    HOL-polymorphic word carrier to `RiscV.Word n`, so it is deliberately not
    tagged as a HOL case. Within that specialization, the global lookup is
    unchanged by `mapc f`. -/
theorem crepSimpExpCorrect1LoadGlobCase {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) (address : BitVec 5)
    (_result : PanWordLab (RiscV.Word n))
    (_h : evalCrepHolExpWordLab state (.loadGlob address) ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) (.loadGlob address)) =
    evalCrepHolExpWordLab state (.loadGlob address) := by
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11,
    crepArithHolMapCode]

/-- Flapjack-specific `BaseAddr` case corresponding to CakeML's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It specializes the
    HOL-polymorphic word carrier to `RiscV.Word n`, so it is deliberately not
    tagged as a HOL case. Within that specialization, the address is unchanged
    by simplification. -/
theorem crepSimpExpCorrect1BaseAddrCase {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ)
    (_result : PanWordLab (RiscV.Word n))
    (_h : evalCrepHolExpWordLab state .baseAddr ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) .baseAddr) =
    evalCrepHolExpWordLab state .baseAddr := by
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11,
    crepArithHolMapCode]

/-- Flapjack-specific `TopAddr` case corresponding to CakeML's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It specializes the
    HOL-polymorphic word carrier to `RiscV.Word n`, so it is deliberately not
    tagged as a HOL case. Within that specialization, the address is unchanged
    by simplification. -/
theorem crepSimpExpCorrect1TopAddrCase {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ)
    (_result : PanWordLab (RiscV.Word n))
    (_h : evalCrepHolExpWordLab state .topAddr ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) .topAddr) =
    evalCrepHolExpWordLab state .topAddr := by
  simp [evalCrepHolExpWordLab, evalCrepHolExp, crepSimpExp.eq_11,
    crepArithHolMapCode]

/-- Successful-result form of the all-width source-runtime support, following
    HOL `simp_exp_correct`'s premise and conclusion with the full wrapped
    result. This remains untagged for the evaluator-correspondence gap recorded
    on `crepSimpExpCorrect1HolFiniteWordSourceRuntime`. -/
theorem crepSimpExpCorrectHolFiniteWordSourceRuntime {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (value : ι → Bool)
    (h : evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression = some value) :
    (evalCrepRuntimeExp
      ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
        dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word = some (.word value) := by
  have hSuccess : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression ≠ none := by
    simp [h]
  rw [crepSimpExpCorrect1HolFiniteWordSourceRuntime
    (_v := .word value) f state expression hSuccess]
  simp [h]

/-- All-dimension production-evaluator support for HOL
    `simp_exp_correct1`. The hypothesis states successful evaluation, `f`
    updates only the source state's code map, and the conclusion preserves the
    successful word projection. `HolFiniteDimension` is explicit Lean
    evidence for a finite index carrier, with `decode` serving as its
    `finite_index` map. This remains untagged because no theorem yet identifies
    that adapter and its operation instances with HOL's native implicit
    `dimindex`/`finite_index` interpretation of `crepSem$eval`. -/
theorem crepSimpExpCorrect1HolFiniteWordSource {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (h : (evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
        dimension)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
      expression).map PanWordLab.word := by
  have hraw : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression ≠ none := by
    intro hn
    simp [hn] at h
  have hsimp := crepSimpExpEvalPreservesHolFiniteWordSource dimension state
    expression hraw
  calc
    (evalCrepRuntimeExp
        ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
          dimension)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          expression)).map PanWordLab.word =
        (evalCrepRuntimeExp
          (crepArithMapCode f
            (state.toHolFiniteWordSourceRuntime dimension))
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            expression)).map PanWordLab.word := by
              rw [crepArithHolFiniteDimensionSourceMapCode_runtime]
    _ = (evalCrepRuntimeExp
          (state.toHolFiniteWordSourceRuntime dimension)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            expression)).map PanWordLab.word := by
              exact congrArg (Option.map PanWordLab.word)
                (crepEvalCodeMapIrrel f
                  (state.toHolFiniteWordSourceRuntime dimension)
                  (crepSimpExp
                    (fun n => bitVecToHolWord dimension
                      (BitVec.ofNat dimension.width n)) expression))
    _ = (evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
          expression).map PanWordLab.word :=
            congrArg (Option.map PanWordLab.word) hsimp

/-- The complete `simp_exp_correct1` result shape over the explicit finite-word
    source equations. This factors the successful-evaluation premise, arbitrary
    code-map update, and `Option (word_lab word)` conclusion through production
    evaluation, then rewrites both sides with the all-constructor source bridge.
    It stays untagged because the explicit finite-index witness is not yet
    formally identified with HOL's implicit `finite_index` dictionary. -/
theorem crepSimpExpCorrect1HolFiniteWordSourceEval {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (h : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word ≠ none) :
    (evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word := by
  letI : HolFiniteDimension ι := dimension
  have hRuntime : (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression).map
        PanWordLab.word ≠ none := by
    rw [evalCrepRuntimeExp_sourceWord_eq dimension]
    exact h
  have hPreserved := crepSimpExpCorrect1HolFiniteWordSource
    (dimension := dimension) f state expression hRuntime
  calc
    (evalCrepHolFiniteWordSourceExp dimension
        (crepArithHolFiniteDimensionMapCode f state)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word =
      (evalCrepRuntimeExp
        ((crepArithHolFiniteDimensionMapCode f state).toHolFiniteWordSourceRuntime
          dimension)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word :=
          congrArg (Option.map PanWordLab.word)
            (evalCrepRuntimeExp_sourceWord_eq dimension
              (crepArithHolFiniteDimensionMapCode f state)
              (crepSimpExp
                (fun n => bitVecToHolWord dimension
                  (BitVec.ofNat dimension.width n)) expression)).symm
    _ = (evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
          expression).map PanWordLab.word := hPreserved
    _ = (evalCrepHolFiniteWordSourceExp dimension state expression).map
          PanWordLab.word :=
            congrArg (Option.map PanWordLab.word)
              (evalCrepRuntimeExp_sourceWord_eq dimension state expression)

/-- HOL-shaped finite-index interface for the complete source-evaluator
    simplifier result. The implicit `HolFiniteDimension` instance represents
    HOL's implicit `finite_index` evidence, so this theorem quantifies over an
    arbitrary finite word index type rather than a fixed `Fin width`. Its
    unused `v` binder is retained to match HOL's `! s exp v` quantifier shape;
    its successful-evaluation premise, code-map update, `simp_exp` image, and
    full optional `word_lab` result follow `simp_exp_correct1`. It remains
    untagged: the explicit source evaluator is not yet identified theoremically
    with HOL's native `crepSem$eval` equations and word-operation instances. -/
theorem crepSimpExpCorrect1HolFiniteWordSourceEvalClass {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (_v : PanWordLab (ι → Bool))
    (h : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word ≠ none) :
    (evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word := by
  exact crepSimpExpCorrect1HolFiniteWordSourceEval dimension f state expression h

/-- Full `Option word_lab` statement shape for all explicit finite word
    dimensions. This is the Lean source-evaluator translation of HOL's local
    `simp_exp_correct1`: the finite-index dictionary is implicit, the success
    premise is on the evaluator result, `f` updates only the code map, and the
    entire wrapped result is preserved. It stays untagged because the source
    evaluator and its word-operation dictionary have not yet been identified
    with the concrete HOL `crepSem$eval` equations and the selected HOL
    `finite_index` instance. `holFiniteIndex_bijective` proves the defining
    unique-in-range property for the Lean dimension dictionary, but does not
    establish that instance identity. -/
theorem crepSimpExpCorrect1HolFiniteWordSourceWordLab {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (_v : PanWordLab (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension state expression ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state expression := by
  change (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word ≠ none at h
  change (evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word
  exact crepSimpExpCorrect1HolFiniteWordSourceEvalClass
    f state expression _v h

/-- Flapjack source-model Const case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). This is one case only, not the assembled
    theorem. The explicit `HolFiniteDimension` dictionary represents HOL's
    implicit finite-index word dimension; the state, unused result binder,
    successful-evaluation premise, code-map update, simplifier image, and full
    `Option word_lab` equality retain HOL's case statement shape. On this
    constructor the source evaluator equation is exactly `eval_def`'s Const
    clause, and no memory or target operation is involved. Other evaluator
    cases and the full simp_exp_correct1 evaluator relation remain unported.
    Untagged: `evalCrepHolFiniteWordSourceExpWordLab` has not been proved equal
    to HOL `crepSem$eval` over an exact HOL state carrier. -/
theorem crepSimpExpCorrect1ConstHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (value : ι → Bool)
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.const value) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.const value)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.const value) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepArithHolFiniteDimensionMapCode,
    crepSimpExp.eq_11]

/-- Flapjack source-model Var case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). Its source equation reduces to HOL
    `eval_def`'s `FLOOKUP s.locals v`; the explicit Lean state stores the same
    partial lookup as a function, and its word_lab projection/reconstruction
    cancels. The unused result binder, success premise, code-map update,
    simplifier image, and full `Option word_lab` equality match this case.
    This is one constructor case only; the assembled theorem and evaluator
    correspondence for the other constructors remain open. Untagged because
    the source-model evaluator has not been related to exact HOL `eval`. -/
theorem crepSimpExpCorrect1VarHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (name : Nat)
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.var name) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.var name)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.var name) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepArithHolFiniteDimensionMapCode,
    crepSimpExp]

/-- Flapjack source-model recursive Load case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). The induction hypothesis is the same
    preservation statement for the address expression at every state and
    result binder. HOL `eval_def` evaluates the address then applies
    `mem_load`; the source evaluator does the corresponding `memaddrs`/memory
    lookup, with `PanWordLab.word` preserving the complete option result. No
    target-specific operation premise is added. Other memory constructors
    and the assembled theorem remain open. Untagged until this evaluator is
    proved equivalent to HOL `crepSem$eval` on an exact state carrier. -/
theorem crepSimpExpCorrect1LoadHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.load address) ≠ none)
    (ih : ∀ (source : CrepHolState (ι → Bool) σ)
      (_value : PanWordLab (ι → Bool)),
      evalCrepHolFiniteWordSourceExpWordLab dimension source address ≠ none →
      evalCrepHolFiniteWordSourceExpWordLab dimension
        (crepArithHolFiniteDimensionMapCode f source)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          address) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source address) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.load address)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.load address) := by
  have hAddress : evalCrepHolFiniteWordSourceExp dimension state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, hNone]
  have hAddressWordLab :
      evalCrepHolFiniteWordSourceExpWordLab dimension state address ≠ none := by
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hAddress
  have hInduction := ih state _result hAddressWordLab
  have hWordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hAddressEval :
      evalCrepHolFiniteWordSourceExp dimension
          (crepArithHolFiniteDimensionMapCode f state)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension
              (BitVec.ofNat dimension.width n)) address) =
        evalCrepHolFiniteWordSourceExp dimension state address := by
    apply Option.map_injective hWordInjective
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hInduction
  simp only [crepSimpExp.eq_1,
    evalCrepHolFiniteWordSourceExpWordLab, evalCrepHolFiniteWordSourceExp]
  rw [hAddressEval]
  simp [crepArithHolFiniteDimensionMapCode]
  rfl

/-! The recursive word32-load case is proved against the source-shaped
    finite-word evaluator. Its memory primitive has a separate all-width
    equation to the tagged HOL `mem_load_32` result, including the `word_lab`
    wrapper and `w2w`; the enclosing recursive evaluator remains untagged
    until its finite-index state encoding is identified with native HOL. -/
theorem crepSimpExpCorrect1Load32HolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.load32 address) ≠ none)
    (ih : ∀ (source : CrepHolState (ι → Bool) σ)
      (_value : PanWordLab (ι → Bool)),
      evalCrepHolFiniteWordSourceExpWordLab dimension source address ≠ none →
      evalCrepHolFiniteWordSourceExpWordLab dimension
        (crepArithHolFiniteDimensionMapCode f source)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          address) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source address) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.load32 address)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.load32 address) := by
  have hAddress : evalCrepHolFiniteWordSourceExp dimension state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, hNone]
  have hAddressWordLab :
      evalCrepHolFiniteWordSourceExpWordLab dimension state address ≠ none := by
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hAddress
  have hInduction := ih state _result hAddressWordLab
  have hWordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hAddressEval :
      evalCrepHolFiniteWordSourceExp dimension
          (crepArithHolFiniteDimensionMapCode f state)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension
              (BitVec.ofNat dimension.width n)) address) =
        evalCrepHolFiniteWordSourceExp dimension state address := by
    apply Option.map_injective hWordInjective
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hInduction
  simp only [crepSimpExp.eq_2,
    evalCrepHolFiniteWordSourceExpWordLab, evalCrepHolFiniteWordSourceExp]
  rw [hAddressEval]
  simp [crepArithHolFiniteDimensionMapCode]
  rfl

/-! This source-evaluator constructor equation uses the exact Load32 primitive
    bridge in `CrepSem.Eval`: after the recursive address succeeds, the
    source-shaped Crep clause is precisely the imported HOL `mem_load_32`
    definition with its `word32` result widened to the expression carrier.
    It remains Flapjack adapter infrastructure because the enclosing explicit
    finite-index evaluator has not yet been identified with native HOL
    `crepSem$eval` as a whole. -/
theorem evalCrepHolFiniteWordSourceExp_load32_eq_panMemLoad32HOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension state
      addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExp dimension state
      (.load32 addressExpression)).map (holWordToBitVec dimension) =
    (panMemLoad32HOL
      (fun bitAddress =>
        ((CrepHolState.toHolFiniteBitVecState dimension state).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
          bitAddress = true)
      state.bigEndian (holWordToBitVec dimension address)).map
        (fun value => BitVec.ofNat dimension.width value.toNat) := by
  simp only [evalCrepHolFiniteWordSourceExp, hAddress]
  exact crepHolEvalMemLoad32_source_eq_panMemLoad32HOL dimension
    (bitVecToHolWord dimension
      (BitVec.ofNat dimension.width (dimension.width / 8)))
    state address

/-- Complete `word_lab` result form of the source `Load32` equation above.
    It transports the evaluator result through the word wrapper and matches
    the tagged HOL `mem_load_32_def` result, including the `w2w` conversion.
    This is adapter support: it does not identify the surrounding recursive
    source evaluator with HOL's implicit finite-index evaluator. -/
theorem evalCrepHolFiniteWordSourceExpWordLab_load32_eq_panMemLoad32HOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension state
      addressExpression = some address) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.load32 addressExpression)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoad32HOL
      (fun bitAddress =>
        ((CrepHolState.toHolFiniteBitVecState dimension state).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
          bitAddress = true)
      state.bigEndian (holWordToBitVec dimension address)).map
        (fun value => PanWordLab.word
          (BitVec.ofNat dimension.width value.toNat)) := by
  simpa [Option.map_map, Function.comp_def, mapCrepHolWordLab] using
    congrArg (Option.map PanWordLab.word)
      (evalCrepHolFiniteWordSourceExp_load32_eq_panMemLoad32HOL
        dimension state addressExpression address hAddress)

/-! The byte-load case follows the same recursive address argument. Its
    explicit `byteAlign`/`getByte` source model has a separate all-width
    equation to the tagged HOL `mem_load_byte` result; the enclosing recursive
    evaluator remains untagged until its finite-index state encoding is
    identified with native HOL. -/
theorem crepSimpExpCorrect1LoadByteHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.loadByte address) ≠ none)
    (ih : ∀ (source : CrepHolState (ι → Bool) σ)
      (_value : PanWordLab (ι → Bool)),
      evalCrepHolFiniteWordSourceExpWordLab dimension source address ≠ none →
      evalCrepHolFiniteWordSourceExpWordLab dimension
        (crepArithHolFiniteDimensionMapCode f source)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          address) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source address) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.loadByte address)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.loadByte address) := by
  have hAddress : evalCrepHolFiniteWordSourceExp dimension state address ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, hNone]
  have hAddressWordLab :
      evalCrepHolFiniteWordSourceExpWordLab dimension state address ≠ none := by
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hAddress
  have hInduction := ih state _result hAddressWordLab
  have hWordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hAddressEval :
      evalCrepHolFiniteWordSourceExp dimension
          (crepArithHolFiniteDimensionMapCode f state)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension
              (BitVec.ofNat dimension.width n)) address) =
        evalCrepHolFiniteWordSourceExp dimension state address := by
    apply Option.map_injective hWordInjective
    simpa [evalCrepHolFiniteWordSourceExpWordLab] using hInduction
  simp only [crepSimpExp.eq_3,
    evalCrepHolFiniteWordSourceExpWordLab, evalCrepHolFiniteWordSourceExp]
  rw [hAddressEval]
  simp [crepArithHolFiniteDimensionMapCode]
  rfl

/-- Flapjack source-model LoadGlob case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). HOL `eval_def` returns
    `FLOOKUP s.globals gadr`; the Lean source clause performs the same
    `BitVec 5` lookup, and the code-map update preserves globals. The unused
    result binder, success premise, simplifier image, and complete
    `Option word_lab` equality match this case. Other evaluator cases and the
    assembled theorem remain open. Untagged pending the exact HOL evaluator
    and state-carrier bridge. -/
theorem crepSimpExpCorrect1LoadGlobHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (address : BitVec 5)
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.loadGlob address) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.loadGlob address)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state (.loadGlob address) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepArithHolFiniteDimensionMapCode,
    crepSimpExp]

/-- Flapjack source-model BaseAddr case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). The Lean source equation reads the same
    state field as HOL `eval_def`; no recursive evaluator or target operation
    is involved. The unused result binder, success premise, code-map update,
    simplifier image, and complete `Option word_lab` equality match this case.
    The assembled theorem and other evaluator cases remain open. Untagged
    pending the exact HOL evaluator and state-carrier bridge. -/
theorem crepSimpExpCorrect1BaseAddrHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ)
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      .baseAddr ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        .baseAddr) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state .baseAddr := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepArithHolFiniteDimensionMapCode,
    crepSimpExp]

/-- Flapjack source-model TopAddr case corresponding to HOL's local `simp_exp_correct1`
    (`crep_arithProofScript.sml:111`). The Lean source equation reads the same
    state field as HOL `eval_def`; no recursive evaluator or target operation
    is involved. The unused result binder, success premise, code-map update,
    simplifier image, and complete `Option word_lab` equality match this case.
    The assembled theorem and other evaluator cases remain open. Untagged
    pending the exact HOL evaluator and state-carrier bridge. -/
theorem crepSimpExpCorrect1TopAddrHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ)
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      .topAddr ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        .topAddr) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state .topAddr := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepArithHolFiniteDimensionMapCode,
    crepSimpExp]

/-- Flapjack support for the recursive `Op` case shape of HOL's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). Its child induction
    hypotheses range over precisely the expressions in the argument list, and
    it retains the successful-evaluation premise, arbitrary code-map update,
    and complete `Option word_lab` result. This remains untagged: the premise
    and conclusion use `evalCrepHolFiniteWordSourceExpWordLab`, whose
    `HolFiniteDimension` and `CrepHolState` encoding has not been proved equal
    to HOL `crepSem$eval`/`eval_def` for arbitrary HOL word dimensions and
    states. Routing `word_op` through the HOL `word_op_def` port proves only
    the operation clause, not the evaluator correspondence needed to claim the
    theorem case. The exact HOL evaluator bridge, other recursive cases, and
    assembled theorem remain open. -/
theorem crepSimpExpCorrect1OpHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool)))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.op operator expressions) ≠ none)
    (ih : ∀ (subexpression : CrepExp (ι → Bool)),
      subexpression ∈ expressions →
      ∀ (source : CrepHolState (ι → Bool) σ)
        (_value : PanWordLab (ι → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f source)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.op operator expressions)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.op operator expressions) := by
  let fromNat := fun n =>
    bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  let updated := crepArithHolFiniteDimensionMapCode f state
  have hRaw : evalCrepHolFiniteWordSourceExp dimension state
      (.op operator expressions) ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab, hNone]
  have hArguments : expressions.mapM
      (evalCrepHolFiniteWordSourceExp dimension state) ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  obtain ⟨values, hValues⟩ := Option.ne_none_iff_exists'.mp hArguments
  have hWordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro left right hEq
    cases hEq
    rfl
  have hPointwise : ∀ child value, child ∈ expressions →
      evalCrepHolFiniteWordSourceExp dimension state child = some value →
      evalCrepHolFiniteWordSourceExp dimension updated
        (crepSimpExp fromNat child) = some value := by
    intro child value hmem heval
    have hChild := ih child hmem state (.word value) (by
      simp [evalCrepHolFiniteWordSourceExpWordLab, heval])
    have hChildRaw : evalCrepHolFiniteWordSourceExp dimension updated
        (crepSimpExp fromNat child) =
      evalCrepHolFiniteWordSourceExp dimension state child := by
      apply Option.map_injective hWordInjective
      exact hChild
    simpa [heval] using hChildRaw
  have hTransformed := optMmapEqSomeMono
      (evalCrepHolFiniteWordSourceExp dimension state)
      (fun child => evalCrepHolFiniteWordSourceExp dimension updated
        (crepSimpExp fromNat child)) expressions values hValues hPointwise
  have hMapMapM (xs : List (CrepExp (ι → Bool))) :
      (xs.map (crepSimpExp fromNat)).mapM
          (evalCrepHolFiniteWordSourceExp dimension updated) =
        xs.mapM (fun child => evalCrepHolFiniteWordSourceExp dimension updated
          (crepSimpExp fromNat child)) := by
    induction xs with
    | nil => rfl
    | cons head tail ihTail => simp [List.mapM_cons, ihTail]
  have hTransformedMapped :
      (expressions.map (crepSimpExp fromNat)).mapM
          (evalCrepHolFiniteWordSourceExp dimension updated) = some values := by
    rw [hMapMapM]
    exact hTransformed
  have hEvaluation :
      evalCrepHolFiniteWordSourceExp dimension updated
          (.op operator (expressions.map (crepSimpExp fromNat))) =
        evalCrepHolFiniteWordSourceExp dimension state
          (.op operator expressions) := by
    simp only [evalCrepHolFiniteWordSourceExp]
    rw [hTransformedMapped, hValues]
    rfl
  change (evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat (.op operator expressions))).map PanWordLab.word = _
  rw [crepSimpExp.eq_4]
  exact congrArg (Option.map PanWordLab.word) hEvaluation

/-! Flapjack support for the recursive `Cmp` case of HOL's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). The IHs range over
    exactly its two child expressions; the successful premise and full
    `Option word_lab` result are retained. Updating the code map does not
    change the source comparison operation, so the child equalities suffice.
    This remains untagged: its evaluator is the explicit
    `HolFiniteDimension`/`CrepHolState` source model, whose interpretation has
    not been proved identical to native HOL `crepSem$eval` for arbitrary word
    types and states. -/
/-! Adapter equation for the source `Cmp` evaluator primitive. Its comparison
    field transports to the tagged Boolean HOL `word_cmp` definition, then
    `wordCmpResultHOL` embeds that Boolean as the Crep word result. This helper
    has no standalone HOL declaration because the word-valued embedding is the
    surrounding `crepSem$eval` clause; the explicit source-state evaluator is
    still awaiting the complete native `eval_def` correspondence. -/
theorem evalCrepHolFiniteWordSourceExp_cmp_eq_wordCmpHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension state left =
      some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension state right =
      some rightValue) :
    evalCrepHolFiniteWordSourceExp dimension state (.cmp operator left right) =
      some (bitVecToHolWord dimension
        (Compiler.Encoders.Asm.wordCmpResultHOL operator
          (holWordToBitVec dimension leftValue)
          (holWordToBitVec dimension rightValue))) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, hLeft, hRight,
    holFiniteWordSourceMemoryModel]

/-! Adapter equation for the source `Shift` evaluator primitive. It exposes
    HOL `word_sh_def` directly after successful child evaluations and retains
    its `Option` failure behavior for out-of-range shifts. The source
    evaluator/Crep-state relation remains Flapjack-specific until the complete
    native `crepSem$eval` correspondence is proved. -/
theorem evalCrepHolFiniteWordSourceExp_shift_eq_wordShiftHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Shift)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension state left =
      some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension state right =
      some rightValue) :
    evalCrepHolFiniteWordSourceExp dimension state (.shift operator left right) =
      (wordShiftHOL operator (holWordToBitVec dimension leftValue)
        (holWordToBitVec dimension rightValue).toNat).map
          (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, hLeft, hRight,
    holFiniteWordSourceMemoryModel]

/-! Adapter equation for the list-valued source `Op` clause. Once the source
    subexpressions evaluate to `values`, the clause is exactly HOL
    `word_op_def` transported through the explicit finite word carrier. The
    complete argument list and HOL's `Option` arity failure are preserved. -/
theorem evalCrepHolFiniteWordSourceExp_op_eq_wordOpHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool))) (values : List (ι → Bool))
    (hValues : expressions.mapM (evalCrepHolFiniteWordSourceExp dimension state) =
      some values) :
    evalCrepHolFiniteWordSourceExp dimension state (.op operator expressions) =
      (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
        (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, hValues,
    holFiniteWordSourceMemoryModel]

theorem crepSimpExpCorrect1CmpHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.cmp operator left right) ≠ none)
    (ih : ∀ (subexpression : CrepExp (ι → Bool)),
      subexpression ∈ [left, right] →
      ∀ (source : CrepHolState (ι → Bool) σ)
        (_value : PanWordLab (ι → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f source)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.cmp operator left right)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.cmp operator left right) := by
  let fromNat := fun n =>
    bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  let updated := crepArithHolFiniteDimensionMapCode f state
  have hRaw : evalCrepHolFiniteWordSourceExp dimension state
      (.cmp operator left right) ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab, hNone]
  have hLeftRaw : evalCrepHolFiniteWordSourceExp dimension state left ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  have hRightRaw : evalCrepHolFiniteWordSourceExp dimension state right ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  obtain ⟨leftValue, hLeftValue⟩ :=
    Option.ne_none_iff_exists'.mp hLeftRaw
  obtain ⟨rightValue, hRightValue⟩ :=
    Option.ne_none_iff_exists'.mp hRightRaw
  have wordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro x y hxy
    cases hxy
    rfl
  have hLeftCase := ih left (by simp) state (.word leftValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue])
  have hRightCase := ih right (by simp) state (.word rightValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hRightValue])
  have hLeftSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat left) = some leftValue := by
    have hEq := Option.map_injective wordInjective hLeftCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue] using hEq
  have hRightSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat right) = some rightValue := by
    have hEq := Option.map_injective wordInjective hRightCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hRightValue] using hEq
  have hLeftSimp' : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) left) = some leftValue := by
    simpa [fromNat, updated, crepArithHolFiniteDimensionMapCode] using hLeftSimp
  have hRightSimp' : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) right) = some rightValue := by
    simpa [fromNat, updated, crepArithHolFiniteDimensionMapCode] using hRightSimp
  have hUpdatedCmp : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (.cmp operator
        (crepSimpExp (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) left)
        (crepSimpExp (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) right)) =
      some ((holFiniteWordSourceMemoryModel dimension state.bigEndian).compare
        operator leftValue rightValue) := by
    simp only [evalCrepHolFiniteWordSourceExp, hLeftSimp', hRightSimp']
    simp [crepArithHolFiniteDimensionMapCode]
  have hOriginalCmp : evalCrepHolFiniteWordSourceExp dimension state
      (.cmp operator left right) =
      some ((holFiniteWordSourceMemoryModel dimension state.bigEndian).compare
        operator leftValue rightValue) := by
    simp [evalCrepHolFiniteWordSourceExp, hLeftValue, hRightValue]
  simp only [evalCrepHolFiniteWordSourceExpWordLab]
  rw [crepSimpExp.eq_9]
  rw [hUpdatedCmp, hOriginalCmp]

/-! Flapjack support for the recursive `Shift` case of HOL's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). It preserves the
    successful-evaluation premise, arbitrary code-map update, complete
    `Option word_lab` result, and two child IHs over the original expressions.
    The source shift operation is unchanged by the map update. This case stays
    untagged until the explicit finite-dimension source evaluator and state are
    identified with native HOL `crepSem$eval` for arbitrary word types. -/
theorem crepSimpExpCorrect1ShiftHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (operator : Shift)
    (left right : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.shift operator left right) ≠ none)
    (ih : ∀ (subexpression : CrepExp (ι → Bool)),
      subexpression ∈ [left, right] →
      ∀ (source : CrepHolState (ι → Bool) σ)
        (_value : PanWordLab (ι → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f source)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.shift operator left right)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.shift operator left right) := by
  let fromNat := fun n =>
    bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  let updated := crepArithHolFiniteDimensionMapCode f state
  have hRaw : evalCrepHolFiniteWordSourceExp dimension state
      (.shift operator left right) ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab, hNone]
  have hLeftRaw : evalCrepHolFiniteWordSourceExp dimension state left ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  have hRightRaw : evalCrepHolFiniteWordSourceExp dimension state right ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  obtain ⟨leftValue, hLeftValue⟩ :=
    Option.ne_none_iff_exists'.mp hLeftRaw
  obtain ⟨rightValue, hRightValue⟩ :=
    Option.ne_none_iff_exists'.mp hRightRaw
  have wordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro x y hxy
    cases hxy
    rfl
  have hLeftCase := ih left (by simp) state (.word leftValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue])
  have hRightCase := ih right (by simp) state (.word rightValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hRightValue])
  have hLeftSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat left) = some leftValue := by
    have hEq := Option.map_injective wordInjective hLeftCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue] using hEq
  have hRightSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat right) = some rightValue := by
    have hEq := Option.map_injective wordInjective hRightCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hRightValue] using hEq
  have hLeftSimp' : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) left) = some leftValue := by
    simpa [fromNat, updated, crepArithHolFiniteDimensionMapCode] using hLeftSimp
  have hRightSimp' : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp (fun n => bitVecToHolWord dimension
        (BitVec.ofNat dimension.width n)) right) = some rightValue := by
    simpa [fromNat, updated, crepArithHolFiniteDimensionMapCode] using hRightSimp
  have hUpdatedShift : evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (.shift operator
        (crepSimpExp (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) left)
        (crepSimpExp (fun n => bitVecToHolWord dimension
          (BitVec.ofNat dimension.width n)) right)) =
    evalCrepHolFiniteWordSourceExp dimension state
      (.shift operator left right) := by
    simp only [evalCrepHolFiniteWordSourceExp, hLeftSimp', hRightSimp']
    simp [crepArithHolFiniteDimensionMapCode, hLeftValue, hRightValue]
  simp only [evalCrepHolFiniteWordSourceExpWordLab]
  rw [crepSimpExp.eq_10]
  exact congrArg (Option.map PanWordLab.word) hUpdatedShift

/-! The multiplication `Crepop` case of HOL's local
    `simp_exp_correct1` (`crep_arithProofScript.sml:111`). Its two recursive
    hypotheses range over the original argument list; successful evaluation,
    arbitrary `mapc f`, `simp_exp`, and the complete optional `word_lab`
    result are retained. This all-width source-model case stays untagged until
    the explicit finite-index/state evaluator is identified with native HOL
    `crepSem$eval`. -/
theorem crepSimpExpCorrect1CrepOpMulHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool))
    (_result : PanWordLab (ι → Bool))
    (_h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.crepOp .mul [left, right]) ≠ none)
    (ih : ∀ (subexpression : CrepExp (ι → Bool)),
      subexpression ∈ [left, right] →
      ∀ (source : CrepHolState (ι → Bool) σ)
        (_value : PanWordLab (ι → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f source)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.crepOp .mul [left, right])) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.crepOp .mul [left, right]) := by
  let fromNat := fun n =>
    bitVecToHolWord dimension (BitVec.ofNat dimension.width n)
  let updated := crepArithHolFiniteDimensionMapCode f state
  have hRaw : evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right]) ≠ none := by
    intro hNone
    apply _h
    simp [evalCrepHolFiniteWordSourceExpWordLab, hNone]
  have hLeftRaw : evalCrepHolFiniteWordSourceExp dimension state left ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  have hRightRaw : evalCrepHolFiniteWordSourceExp dimension state right ≠ none := by
    intro hNone
    apply hRaw
    simp [evalCrepHolFiniteWordSourceExp, hNone]
  obtain ⟨leftValue, hLeftValue⟩ :=
    Option.ne_none_iff_exists'.mp hLeftRaw
  obtain ⟨rightValue, hRightValue⟩ :=
    Option.ne_none_iff_exists'.mp hRightRaw
  have wordInjective : Function.Injective
      (PanWordLab.word : (ι → Bool) → PanWordLab (ι → Bool)) := by
    intro x y hxy
    cases hxy
    rfl
  have hLeftCase := ih left (by simp) state (.word leftValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue])
  have hRightCase := ih right (by simp) state (.word rightValue) (by
    simp [evalCrepHolFiniteWordSourceExpWordLab, hRightValue])
  have hLeftSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat left) = some leftValue := by
    have hEq := Option.map_injective wordInjective hLeftCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hLeftValue] using hEq
  have hRightSimp : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat right) = some rightValue := by
    have hEq := Option.map_injective wordInjective hRightCase
    simpa [evalCrepHolFiniteWordSourceExpWordLab, hRightValue] using hEq
  have hLeftRuntime : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension)
      (crepSimpExp fromNat left) = some leftValue := by
    have hUpdated := hLeftSimp
    rw [← evalCrepRuntimeExp_sourceWord_eq dimension updated
      (crepSimpExp fromNat left)] at hUpdated
    rw [crepArithHolFiniteDimensionSourceMapCode_runtime dimension f state] at hUpdated
    calc
      evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
          (crepSimpExp fromNat left) =
        evalCrepRuntimeExp
          (crepArithMapCode f (state.toHolFiniteWordSourceRuntime dimension))
          (crepSimpExp fromNat left) :=
            (crepEvalCodeMapIrrel f
              (state.toHolFiniteWordSourceRuntime dimension)
              (crepSimpExp fromNat left)).symm
      _ = some leftValue := hUpdated
  have hRightRuntime : evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension)
      (crepSimpExp fromNat right) = some rightValue := by
    have hUpdated := hRightSimp
    rw [← evalCrepRuntimeExp_sourceWord_eq dimension updated
      (crepSimpExp fromNat right)] at hUpdated
    rw [crepArithHolFiniteDimensionSourceMapCode_runtime dimension f state] at hUpdated
    calc
      evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension)
          (crepSimpExp fromNat right) =
        evalCrepRuntimeExp
          (crepArithMapCode f (state.toHolFiniteWordSourceRuntime dimension))
          (crepSimpExp fromNat right) :=
            (crepEvalCodeMapIrrel f
              (state.toHolFiniteWordSourceRuntime dimension)
              (crepSimpExp fromNat right)).symm
      _ = some rightValue := hUpdated
  have hMulRuntime := crepSimpMulEvalHolFiniteDimension dimension
    (fun source => source.toHolFiniteWordSourceRuntime dimension)
    (fun source expression constant value hEval =>
      crepEvalMulConstHolFiniteWordSource dimension source expression
        constant value hEval)
    state left right leftValue rightValue hLeftRuntime hRightRuntime
  have hMulSource : evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat (.crepOp .mul [left, right])) =
        some (leftValue * rightValue) := by
    rw [← evalCrepRuntimeExp_sourceWord_eq dimension updated
      (crepSimpExp fromNat (.crepOp .mul [left, right]))]
    rw [crepArithHolFiniteDimensionSourceMapCode_runtime dimension f state]
    rw [crepEvalCodeMapIrrel f
      (state.toHolFiniteWordSourceRuntime dimension)
      (crepSimpExp fromNat (.crepOp .mul [left, right]))]
    exact hMulRuntime
  have hOriginalSource : evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right]) = some (leftValue * rightValue) := by
    simp [evalCrepHolFiniteWordSourceExp, hLeftValue, hRightValue,
      holFiniteWordSourceCrepOp_eq_crepOpCrep, crepOpCrep]
  change (evalCrepHolFiniteWordSourceExp dimension updated
      (crepSimpExp fromNat (.crepOp .mul [left, right]))).map PanWordLab.word =
    (evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right])).map PanWordLab.word
  rw [hMulSource, hOriginalSource]

/-! HOL's induction proof handles the complete `Crepop op es` constructor before
    splitting `crep_op`'s defining equations. Since this language currently has
    only `CrepOp.mul`, the source evaluator succeeds only for a two-element
    argument list; all other shapes discharge from the same success premise.
    This all-width source-model wrapper follows that case boundary and consumes
    the recursive hypotheses over the original list, as in
    `simp_exp_correct1`. It remains untagged for the evaluator correspondence
    gap recorded above. -/
theorem crepSimpExpCorrect1CrepOpHolFiniteWordSourceCase
    {ι : Type} {σ : Type} [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ)
    (operator : CrepOp) (arguments : List (CrepExp (ι → Bool)))
    (result : PanWordLab (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.crepOp operator arguments) ≠ none)
    (ih : ∀ (subexpression : CrepExp (ι → Bool)),
      subexpression ∈ arguments →
      ∀ (source : CrepHolState (ι → Bool) σ)
        (_value : PanWordLab (ι → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f source)
          (crepSimpExp
            (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
            subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source subexpression) :
    evalCrepHolFiniteWordSourceExpWordLab dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        (.crepOp operator arguments)) =
    evalCrepHolFiniteWordSourceExpWordLab dimension state
      (.crepOp operator arguments) := by
  cases operator with
  | mul =>
    cases arguments with
    | nil => simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp] at h
    | cons left tail =>
      cases tail with
      | nil => simp [evalCrepHolFiniteWordSourceExpWordLab,
          evalCrepHolFiniteWordSourceExp] at h
      | cons right rest =>
        cases rest with
        | nil =>
          exact crepSimpExpCorrect1CrepOpMulHolFiniteWordSourceCase
            (dimension := dimension) f state left right result h
            (fun subexpression hmem source value heval =>
              ih subexpression hmem source value heval)
        | cons extra rest =>
          simp [evalCrepHolFiniteWordSourceExpWordLab,
            evalCrepHolFiniteWordSourceExp] at h

/-! The source evaluator and the canonical finite-dimension evaluator both
    read LoadGlob directly from the represented HOL globals field. This bridge
    closes this evaluator constructor without assumptions about the memory
    model; it is Flapjack adapter support, not a standalone HOL declaration. -/
theorem evalCrepHolFiniteWordSourceExp_loadGlob_eq_finiteDimension
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : BitVec 5) :
    evalCrepHolFiniteWordSourceExp dimension state (.loadGlob address) =
      evalCrepHolFiniteDimensionExp dimension state (.loadGlob address) := by
  letI : HolFiniteDimension ι := dimension
  cases hglobal : state.globals address with
  | none => simp [evalCrepHolFiniteWordSourceExp,
      evalCrepHolFiniteDimensionExp, evalCrepHolExp,
      CrepHolState.toHolFiniteBitVecState, mapCrepExpWord, hglobal]
  | some wordLab =>
    cases wordLab with
    | word value =>
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolFiniteDimensionExp,
        evalCrepHolExp, CrepHolState.toHolFiniteBitVecState, mapCrepExpWord,
        mapCrepHolWordLab, panTheWord, hglobal,
        bitVecToHolWord_holWordToBitVec]

/-- Successful-result form of the all-finite-index source-evaluator theorem.
    This follows HOL `simp_exp_correct`'s premise and conclusion, with the
    same arbitrary code-map update and full `word_lab` value. It remains
    untagged for the same explicit source-evaluator/native HOL correspondence
    gap recorded on `crepSimpExpCorrect1HolFiniteWordSourceEvalClass`. -/
theorem crepSimpExpCorrectHolFiniteWordSourceEvalClass {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (value : PanWordLab (ι → Bool))
    (h : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word = some value) :
    (evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word = some value := by
  have hSuccess : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word ≠ none := by simp [h]
  calc
    (evalCrepHolFiniteWordSourceExp dimension
        (crepArithHolFiniteDimensionMapCode f state)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension
            (BitVec.ofNat dimension.width n)) expression)).map PanWordLab.word =
            (evalCrepHolFiniteWordSourceExp dimension state expression).map
              PanWordLab.word :=
            crepSimpExpCorrect1HolFiniteWordSourceEvalClass
              f state expression value hSuccess
    _ = some value := h

/-- Full `word_lab` result form of the source-evaluator preservation theorem.
    The raw source evaluator returns `Option word`; mapping the `word`
    constructor gives HOL's complete `Option word_lab` result. This form keeps
    the successful-evaluation premise on the raw evaluator. It remains untagged
    because production evaluation is configured with the HOL-shaped source
    memory model rather than the compiler's canonical RISC-V memory model;
    their arbitrary-carrier relation is not proved. -/
theorem crepSimpExpCorrect1HolFiniteWordSourceFull {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool))
    (state : CrepHolState (ι → Bool) σ) (expression : CrepExp (ι → Bool))
    (h : evalCrepHolFiniteWordSourceExp dimension state expression ≠ none) :
    (evalCrepHolFiniteWordSourceExp dimension
      (crepArithHolFiniteDimensionMapCode f state)
      (crepSimpExp
        (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
        expression)).map PanWordLab.word =
    (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word := by
  have hmap : (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word ≠ none := by
    cases heval : evalCrepHolFiniteWordSourceExp dimension state expression <;>
      simp_all
  exact crepSimpExpCorrect1HolFiniteWordSourceEval
    dimension f state expression hmap

/-! Canonical `Fin width` all-width instance of the source-runtime result.
    Unlike the arbitrary `HolFiniteDimension` theorem above, this fixes the
    index-to-bit map to Lean's standard `Fin` ordering for every positive
    width. It remains untagged: this canonical Lean representation still does
    not prove that production `evalCrepRuntimeExp`'s transported word
    operations and memory loads are HOL `crepSem$eval` for every word type. -/
theorem crepSimpExpCorrect1HolWordBitsSourceRuntime {width : Nat} [NeZero width]
    {σ : Type}
    (f : FunName × (List Nat × CrepProg (Fin width → Bool)) →
      List Nat × CrepProg (Fin width → Bool))
    (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (h : (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := width))) expression).map
        PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      (CrepHolState.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := width))
        (crepArithHolFiniteDimensionMapCode f state))
      (crepSimpExp
        (fun n => bitVecToHolWordBits (BitVec.ofNat width n)) expression)).map
        PanWordLab.word =
    (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := width))) expression).map
        PanWordLab.word := by
  let dimension : HolFiniteDimension (Fin width) :=
    instFinHolFiniteDimension (width := width)
  letI : HolFiniteDimension (Fin width) := dimension
  have hFromNat :
      (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n)) =
        (fun n => bitVecToHolWordBits (BitVec.ofNat dimension.width n)) := by
    funext value
    rfl
  have hresult := crepSimpExpCorrect1HolFiniteWordSource (f := f)
    (state := state) (expression := expression) h
  rw [hFromNat] at hresult
  exact hresult



/-- Flapjack's RISC-V specialization of HOL simp_exp_correct1.
    It keeps the HOL theorem's successful-evaluation premise, arbitrary local
    mapc f code-map update, and complete Option (PanWordLab.word ...)
    result. The value type is a positive-width RISC-V word and evaluation fixes
    riscvCrepWordTarget; HOL instead quantifies over its polymorphic word
    type and arbitrary crepSem state. The evaluator correspondence is proved
    for every positive RISC-V width and for the concrete `Fin width → Bool`
    carrier, but not for an arbitrary HOL finite dimension type. This faithful-
    shape specialization is deliberately untagged. -/
theorem crepSimpExpCorrect1 {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n))
    (h : (evalCrepRuntimeExp (riscvCrepWordTarget state) expression).map
      PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp (riscvCrepWordTarget (crepArithMapCode f state))
      (crepSimpExp (BitVec.ofNat n) expression)).map PanWordLab.word =
    (evalCrepRuntimeExp (riscvCrepWordTarget state) expression).map
      PanWordLab.word := by
  have hraw : evalCrepRuntimeExp (riscvCrepWordTarget state) expression ≠ none := by
    simpa using h
  have hsimp := crepSimpExpEvalPreserves state expression hraw
  have htarget :
      riscvCrepWordTarget (crepArithMapCode f state) =
        crepArithMapCode f (riscvCrepWordTarget state) := by
    cases state
    rfl
  rw [htarget]
  rw [crepEvalCodeMapIrrel f (riscvCrepWordTarget state)
    (crepSimpExp (BitVec.ofNat n) expression)]
  rw [hsimp]

/-! Flapjack-only all-width support for the source-shaped state update. This
    is intentionally not tagged as HOL `simp_exp_correct1`: it represents
    HOL words only as `RiscV.Word n`/`BitVec n` and the direct evaluator's
    width operations through the RISC-V model. The exact arbitrary HOL word
    carrier theorem remains open. The all-constructor production evaluator
    correspondence is proved in `CrepSem.Eval`. -/
theorem crepArithHolMapCode_target [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ) :
    riscvCrepWordTarget (crepArithHolMapCode f state).toRuntime =
      crepArithMapCode f (riscvCrepWordTarget state.toRuntime) := by
  cases state
  rfl

theorem crepSimpExpCorrect1BitVec {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n))
    (h : evalCrepHolExpWordLab state expression ≠ none) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) expression) =
    evalCrepHolExpWordLab state expression := by
  have hraw :
      evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime) expression ≠ none := by
    rw [evalCrepRuntimeExp_toRuntime_eq]
    simpa [evalCrepHolExpWordLab] using h
  have hsimp := crepSimpExpEvalPreserves state.toRuntime expression hraw
  calc
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
        (crepSimpExp (BitVec.ofNat n) expression) =
        (evalCrepRuntimeExp
          (riscvCrepWordTarget (crepArithHolMapCode f state).toRuntime)
          (crepSimpExp (BitVec.ofNat n) expression)).map PanWordLab.word := by
          simp only [evalCrepHolExpWordLab]
          rw [← evalCrepRuntimeExp_toRuntime_eq]
    _ = (evalCrepRuntimeExp
          (crepArithMapCode f (riscvCrepWordTarget state.toRuntime))
          (crepSimpExp (BitVec.ofNat n) expression)).map PanWordLab.word := by
          rw [crepArithHolMapCode_target]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime)
          (crepSimpExp (BitVec.ofNat n) expression)).map PanWordLab.word := by
          rw [crepEvalCodeMapIrrel f (riscvCrepWordTarget state.toRuntime)
            (crepSimpExp (BitVec.ofNat n) expression)]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime)
          expression).map PanWordLab.word := by
          exact congrArg (Option.map PanWordLab.word) hsimp
    _ = evalCrepHolExpWordLab state expression := by
          rw [evalCrepHolExpWordLab]
          rw [← evalCrepRuntimeExp_toRuntime_eq]

/-! Flapjack-only all-width instance of the public HOL `simp_exp_correct`
    conclusion. It inherits the arbitrary-carrier mismatch documented above
    and is not tagged as a HOL port. -/
theorem crepSimpExpCorrectBitVec {n : Nat} [NeZero n] {σ : Type}
    (f : FunName × (List Nat × CrepProg (RiscV.Word n)) →
      List Nat × CrepProg (RiscV.Word n))
    (state : CrepHolState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n)) (value : RiscV.Word n)
    (h : evalCrepHolExpWordLab state expression = some (.word value)) :
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
      (crepSimpExp (BitVec.ofNat n) expression) = some (.word value) := by
  have hsuccess : evalCrepHolExpWordLab state expression ≠ none := by
    rw [h]
    simp
  calc
    evalCrepHolExpWordLab (crepArithHolMapCode f state)
        (crepSimpExp (BitVec.ofNat n) expression) =
        evalCrepHolExpWordLab state expression :=
          crepSimpExpCorrect1BitVec f state expression hsuccess
    _ = some (.word value) := h

/-! Fin-index source states can use the all-width simplifier naturality theorem
    above to transfer evaluator preservation through BitVec. -/
def crepArithHolWordBitsMapCode {width : Nat} {σ : Type}
    (f : FunName × (List Nat × CrepProg (Fin width → Bool)) →
      List Nat × CrepProg (Fin width → Bool))
    (state : CrepHolState (Fin width → Bool) σ) :
    CrepHolState (Fin width → Bool) σ :=
  { state with code := fun name =>
      (state.code name).map (fun entry => f (name, entry)) }

theorem crepArithHolWordBitsMapCode_toBitVecState {width : Nat} [NeZero width] {σ : Type}
    (f : FunName × (List Nat × CrepProg (Fin width → Bool)) →
      List Nat × CrepProg (Fin width → Bool))
    (state : CrepHolState (Fin width → Bool) σ) :
    (crepArithHolWordBitsMapCode f state).toBitVecState = state.toBitVecState := by
  cases state
  rfl

/-! All-width `eval_mul_const` support in the canonical `Fin width` word
    representation. This factors the arbitrary finite-enumeration adapter out
    of the arithmetic step used by the simp proof. It remains untagged because
    its source evaluator and word operations are transported through the
    BitVec/RISC-V model; the HOL `eval_def`/`crep_op_def` correspondence is
    still open. -/
theorem crepEvalMulConstHolWordBits {width : Nat} [NeZero width]
    {σ : Type} (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (constant value : Fin width → Bool)
    (h : evalCrepHolWordBitsExp state expression = some value) :
    evalCrepHolWordBitsExp state
      (crepMulConst (fun n => bitVecToHolWordBits (BitVec.ofNat width n))
        expression constant) = some (value * constant) := by
  have hSource : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec expression) =
        some (holWordBitsToBitVec value) := by
    change (evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec expression)).map
        bitVecToHolWordBits = some value at h
    cases hEval : evalCrepHolExp state.toBitVecState
        (mapCrepExpWord holWordBitsToBitVec expression) with
    | none => simp [hEval] at h
    | some bitVecValue =>
        have hValue : bitVecToHolWordBits bitVecValue = value := by
          simpa [hEval] using h
        have hBitVecValue : bitVecValue = holWordBitsToBitVec value := by
          calc
            bitVecValue = holWordBitsToBitVec
                (bitVecToHolWordBits bitVecValue) := by
                  rw [holWordBitsToBitVec_bitVecToHolWordBits]
            _ = holWordBitsToBitVec value := congrArg holWordBitsToBitVec hValue
        simp [hBitVecValue]
  have hProduction :
      evalCrepRuntimeExp
          (riscvCrepWordTarget state.toBitVecState.toRuntime)
          (mapCrepExpWord holWordBitsToBitVec expression) =
        some (holWordBitsToBitVec value) := by
    rw [evalCrepRuntimeExp_toRuntime_eq]
    exact hSource
  have hMul := crepEvalMulConstRaw state.toBitVecState.toRuntime
    (mapCrepExpWord holWordBitsToBitVec expression)
    (holWordBitsToBitVec constant) (holWordBitsToBitVec value) hProduction
  have hSourceMul :
      evalCrepHolExp state.toBitVecState
          (crepMulConst (BitVec.ofNat width)
            (mapCrepExpWord holWordBitsToBitVec expression)
            (holWordBitsToBitVec constant)) =
        some (holWordBitsToBitVec value * holWordBitsToBitVec constant) := by
    rw [← evalCrepRuntimeExp_toRuntime_eq]
    exact hMul
  have hNatural := crepMulConst_holWordBits expression constant
  unfold evalCrepHolWordBitsExp
  rw [hNatural, hSourceMul]
  apply congrArg some
  calc
    bitVecToHolWordBits
        (holWordBitsToBitVec value * holWordBitsToBitVec constant) =
        bitVecToHolWordBits (holWordBitsToBitVec (value * constant)) := by
          rw [holWordBitsToBitVec_mul]
    _ = value * constant := bitVecToHolWordBits_holWordBitsToBitVec _

private theorem crepSimpExpEvalPreservesHolWordBits {width : Nat} [NeZero width]
    {σ : Type} (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (h : evalCrepHolWordBitsExp state expression ≠ none) :
    evalCrepHolWordBitsExp state
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
          expression) = evalCrepHolWordBitsExp state expression := by
  have hBitVecSource : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec expression) ≠ none := by
    intro hnone
    simp [evalCrepHolWordBitsExp, hnone] at h
  have hBitVecRuntime :
      evalCrepRuntimeExp (riscvCrepWordTarget state.toBitVecState.toRuntime)
        (mapCrepExpWord holWordBitsToBitVec expression) ≠ none := by
    rw [evalCrepRuntimeExp_toRuntime_eq]
    exact hBitVecSource
  have hpres := crepSimpExpEvalPreserves state.toBitVecState.toRuntime
    (mapCrepExpWord holWordBitsToBitVec expression) hBitVecRuntime
  have hpresSource :
      evalCrepHolExp state.toBitVecState
          (crepSimpExp (BitVec.ofNat width)
            (mapCrepExpWord holWordBitsToBitVec expression)) =
        evalCrepHolExp state.toBitVecState
          (mapCrepExpWord holWordBitsToBitVec expression) := by
    rw [← evalCrepRuntimeExp_toRuntime_eq, ← evalCrepRuntimeExp_toRuntime_eq]
    exact hpres
  unfold evalCrepHolWordBitsExp
  rw [crepSimpExp_holWordBits]
  exact congrArg (Option.map bitVecToHolWordBits) hpresSource

private theorem crepSimpExpEvalPreservesHolWordBitsWordLab
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (h : evalCrepHolWordBitsExpWordLab state expression ≠ none) :
    evalCrepHolWordBitsExpWordLab state
        (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
          expression) = evalCrepHolWordBitsExpWordLab state expression := by
  have hraw : evalCrepHolWordBitsExp state expression ≠ none := by
    intro hnone
    simp [evalCrepHolWordBitsExpWordLab, hnone] at h
  exact congrArg (Option.map PanWordLab.word)
    (crepSimpExpEvalPreservesHolWordBits state expression hraw)

/-- All-width production evaluator support over the canonical finite-index
    HOL word representation. It retains mapc's arbitrary code-map update and
    Option/word_lab result shape. It is untagged because it fixes the dimension
    carrier to Fin width; reindexing from every HOL finite dimension type is
    tracked separately. -/
theorem crepSimpExpCorrect1HolWordBits {width : Nat} [NeZero width]
    {σ : Type}
    (f : FunName × (List Nat × CrepProg (Fin width → Bool)) →
      List Nat × CrepProg (Fin width → Bool))
    (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (h : (evalCrepRuntimeExp state.toHolWordBitsRuntime expression).map
      PanWordLab.word ≠ none) :
    (evalCrepRuntimeExp
      (crepArithHolWordBitsMapCode f state).toHolWordBitsRuntime
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        expression)).map PanWordLab.word =
    (evalCrepRuntimeExp state.toHolWordBitsRuntime expression).map PanWordLab.word := by
  have hSource : evalCrepHolWordBitsExpWordLab state expression ≠ none := by
    have h' := h
    rw [evalCrepRuntimeExp_toHolWordBits_eq] at h'
    exact h'
  have hpresSource := crepSimpExpEvalPreservesHolWordBitsWordLab state expression hSource
  have hstate := crepArithHolWordBitsMapCode_toBitVecState f state
  rw [evalCrepRuntimeExp_toHolWordBits_eq
    (crepArithHolWordBitsMapCode f state)
    (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) expression)]
  rw [evalCrepRuntimeExp_toHolWordBits_eq state expression]
  change evalCrepHolWordBitsExpWordLab (crepArithHolWordBitsMapCode f state)
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value)) expression) =
    evalCrepHolWordBitsExpWordLab state expression
  simpa only [evalCrepHolWordBitsExpWordLab, evalCrepHolWordBitsExp, hstate]
    using hpresSource

/-! This source-evaluator-shaped corollary uses the canonical numeric bit
    positions `Fin width`, rather than an arbitrary enumeration of an index
    type. It is still untagged: the evaluator's word operations and byte-load
    behavior are transported through BitVec/RISC-V, and we have not proved
    that this model is HOL's FCP word operations for every HOL type's
    `dimindex`. The remaining faithful port is that representation/evaluator
    correspondence, tracked by bead `flapjack-pxn.18.5.4.3.1`. -/
theorem crepSimpExpCorrect1HolWordBitsSource {width : Nat} [NeZero width]
    {σ : Type}
    (f : FunName × (List Nat × CrepProg (Fin width → Bool)) →
      List Nat × CrepProg (Fin width → Bool))
    (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool))
    (h : evalCrepHolWordBitsExpWordLab state expression ≠ none) :
    evalCrepHolWordBitsExpWordLab (crepArithHolWordBitsMapCode f state)
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat width value))
        expression) =
    evalCrepHolWordBitsExpWordLab state expression := by
  have hpres := crepSimpExpEvalPreservesHolWordBitsWordLab state expression h
  have hstate := crepArithHolWordBitsMapCode_toBitVecState f state
  unfold evalCrepHolWordBitsExpWordLab at hpres ⊢
  unfold evalCrepHolWordBitsExp at hpres ⊢
  rw [hstate]
  exact hpres


end Flapjack
