import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.Semantics.CrepSem.WordAlignment

/-!
# Pancake Crepe expression evaluation

This file encodes the HOL `crepSem$state` fields without the target-only
operation and FFI-context fields carried by Flapjack's executable runtime.
The adapter below supplies the operations derived from a positive-width word
type, and the source-shaped evaluator follows `crepSem$eval_def`.
-/

namespace Flapjack

open Compiler.Encoders.Asm

/-! HOL's polymorphic `'a word` carrier is a Boolean function indexed by the
    finite dimension type `'a`. This canonical `Fin width` representation
    exposes that carrier in Lean's core library. The conversions below use
    little-endian bit order, matching BitVec's low-bit indexing. They are
    Flapjack representation infrastructure, not a claim about the Crep
    evaluator or any HOL theorem. -/
def holWordBitsToBitVec {width : Nat} (word : Fin width → Bool) :
    BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn word)).cast (by simp)

theorem holWordBitsToBitVec_getLsbD {width : Nat}
    (word : Fin width → Bool) (index : Fin width) :
    (holWordBitsToBitVec word).getLsbD index.val = word index := by
  change (BitVec.ofBoolListLE (List.ofFn word)).getLsbD index.val = word index
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

def bitVecToHolWordBits {width : Nat} (word : BitVec width) :
    Fin width → Bool :=
  fun index => word.getLsb index

theorem bitVecToHolWordBits_holWordBitsToBitVec {width : Nat}
    (word : Fin width → Bool) :
    bitVecToHolWordBits (holWordBitsToBitVec word) = word := by
  funext index
  change (BitVec.ofBoolListLE (List.ofFn word)).getLsbD index.val = word index
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

theorem holWordBitsToBitVec_injective {width : Nat} :
    Function.Injective (@holWordBitsToBitVec width) := by
  intro left right h
  calc
    left = bitVecToHolWordBits (holWordBitsToBitVec left) :=
      (bitVecToHolWordBits_holWordBitsToBitVec left).symm
    _ = bitVecToHolWordBits (holWordBitsToBitVec right) := congrArg bitVecToHolWordBits h
    _ = right := bitVecToHolWordBits_holWordBitsToBitVec right

theorem bitVecToHolWordBits_ofNat {width : Nat} (value : Nat) :
    bitVecToHolWordBits (BitVec.ofNat width value) =
      fun index => Nat.testBit value index.val := by
  funext index
  change (BitVec.ofNat width value).toNat.testBit index.val =
    Nat.testBit value index.val
  rw [BitVec.toNat_ofNat]
  simp [Nat.testBit_mod_two_pow, index.isLt]

theorem holWordBitsToBitVec_bitVecToHolWordBits {width : Nat}
    (word : BitVec width) :
    holWordBitsToBitVec (bitVecToHolWordBits word) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  change (BitVec.ofBoolListLE
      (List.ofFn (fun i => word.getLsb i))).getLsbD index =
    word.getLsbD index
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, hindex]

/-! HOL4 defines `n2w n` by `FCP i. BIT i n` in
    `$HOL/src/n-bit/wordsScript.sml`; `word_index_n2w` identifies a valid FCP
    index with that numeric bit position. This is the canonical `Fin width`
    encoding fact, independent of the RISC-V evaluator. It is left untagged
    because HOL4's core words theory is external to the checked CakeML source
    tree, so this declaration cannot carry a repository-local `@[hol]` path. -/
theorem holWordBitsToBitVec_n2w {width : Nat} (value : Nat) :
    holWordBitsToBitVec (fun index : Fin width => Nat.testBit value index.val) =
      BitVec.ofNat width value := by
  rw [← bitVecToHolWordBits_ofNat]
  exact holWordBitsToBitVec_bitVecToHolWordBits _

/-! A dimension-indexed HOL word is isomorphic to the canonical Fin-index
    representation once its finite dimension is enumerated. Here `decode` is
    the numeric-index-to-carrier map (the role of HOL `finite_index`) and
    `encode` is its inverse. Lean core/Std in this project does not provide
    Fintype/equivFin, so the enumeration data is represented explicitly here.
    `holFiniteIndex_bijective` below proves that `decode` satisfies the exact
    unique-in-range property from HOL's `fcp$finite_index` definition. The
    arbitrary-index `n2w` adapter below is pointwise `BIT` at `encode i`; the
    remaining word-operation and evaluator comparisons are proved separately. -/
class HolFiniteDimension (ι : Type u) where
  width : Nat
  width_pos : 0 < width
  encode : ι → Fin width
  decode : Fin width → ι
  encode_decode : ∀ index, encode (decode index) = index
  decode_encode : ∀ index, decode (encode index) = index

instance instFinHolFiniteDimension {width : Nat} [NeZero width] :
    HolFiniteDimension (Fin width) where
  width := width
  width_pos := Nat.pos_of_ne_zero (NeZero.ne width)
  encode := id
  decode := id
  encode_decode := by intro index; rfl
  decode_encode := by intro index; rfl

/-- HOL's `fcp$finite_index` (`HOL/src/n-bit/fcpScript.sml:118`)
    restricted to its valid range. The dimension's `decode` is the chosen
    finite-index map `Fin width → ι`; values outside the HOL bound are
    immaterial to the defining bijection property, so this total Lean function
    extends them with the first valid index. -/
def holFiniteIndex {ι : Type u} (dimension : HolFiniteDimension ι)
    (index : Nat) : ι :=
  if h : index < dimension.width then dimension.decode ⟨index, h⟩
  else dimension.decode ⟨0, dimension.width_pos⟩

/-- The explicit `HolFiniteDimension` dictionary satisfies HOL's defining
    finite-index property: every carrier index has a unique natural number
    below the dimension that maps to it. This connects `decode` to HOL's
    `finite_index`; it does not identify the separate source word-operation
    adapters or evaluator equations with the corresponding HOL definitions. -/
theorem holFiniteIndex_bijective {ι : Type u}
    (dimension : HolFiniteDimension ι) (value : ι) :
    ∃ index, index < dimension.width ∧ holFiniteIndex dimension index = value ∧
      ∀ other, other < dimension.width →
        holFiniteIndex dimension other = value → other = index := by
  refine ⟨(dimension.encode value).val, (dimension.encode value).isLt, ?_, ?_⟩
  · simp [holFiniteIndex, (dimension.encode value).isLt, dimension.decode_encode]
  · intro index hindex hindexValue
    have hdecoded : dimension.decode ⟨index, hindex⟩ = value := by
      simpa [holFiniteIndex, hindex] using hindexValue
    have hencoded : (⟨index, hindex⟩ : Fin dimension.width) =
        dimension.encode value := by
      calc
        ⟨index, hindex⟩ = dimension.encode (dimension.decode ⟨index, hindex⟩) :=
          (dimension.encode_decode _).symm
        _ = dimension.encode value := congrArg dimension.encode hdecoded
    exact congrArg Fin.val hencoded

def holWordToFinBits {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : ι → Bool) : Fin dimension.width → Bool :=
  fun index => word (dimension.decode index)

def finBitsToHolWord {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : Fin dimension.width → Bool) : ι → Bool :=
  fun index => word (dimension.encode index)

theorem finBitsToHolWord_holWordToFinBits {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : ι → Bool) :
    finBitsToHolWord dimension (holWordToFinBits dimension word) = word := by
  funext index
  simp [finBitsToHolWord, holWordToFinBits, dimension.decode_encode]

theorem holWordToFinBits_finBitsToHolWord {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : Fin dimension.width → Bool) :
    holWordToFinBits dimension (finBitsToHolWord dimension word) = word := by
  funext index
  simp [holWordToFinBits, finBitsToHolWord, dimension.encode_decode]

def holWordToBitVec {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : ι → Bool) : BitVec dimension.width :=
  holWordBitsToBitVec (holWordToFinBits dimension word)

def bitVecToHolWord {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : BitVec dimension.width) : ι → Bool :=
  finBitsToHolWord dimension (bitVecToHolWordBits word)

theorem bitVecToHolWord_holWordToBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : ι → Bool) :
    bitVecToHolWord dimension (holWordToBitVec dimension word) = word := by
  change finBitsToHolWord dimension
      (bitVecToHolWordBits (holWordBitsToBitVec (holWordToFinBits dimension word))) = word
  rw [bitVecToHolWordBits_holWordBitsToBitVec]
  exact finBitsToHolWord_holWordToFinBits dimension word

theorem holWordToBitVec_injective {ι : Type u}
    (dimension : HolFiniteDimension ι) :
    Function.Injective (holWordToBitVec dimension) := by
  intro left right h
  calc
    left = bitVecToHolWord dimension (holWordToBitVec dimension left) :=
      (bitVecToHolWord_holWordToBitVec dimension left).symm
    _ = bitVecToHolWord dimension (holWordToBitVec dimension right) :=
      congrArg (bitVecToHolWord dimension) h
    _ = right := bitVecToHolWord_holWordToBitVec dimension right

theorem holWordToBitVec_bitVecToHolWord {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : BitVec dimension.width) :
    holWordToBitVec dimension (bitVecToHolWord dimension word) = word := by
  change holWordBitsToBitVec
      (holWordToFinBits dimension
        (finBitsToHolWord dimension (bitVecToHolWordBits word))) = word
  rw [holWordToFinBits_finBitsToHolWord]
  exact holWordBitsToBitVec_bitVecToHolWordBits word

theorem holWordToBitVec_getLsbD {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : ι → Bool)
    (index : Fin dimension.width) :
    (holWordToBitVec dimension word).getLsbD index.val =
      word (dimension.decode index) := by
  change (holWordBitsToBitVec (holWordToFinBits dimension word)).getLsbD
      index.val = _
  rw [holWordBitsToBitVec_getLsbD]
  rfl

/-! Signed word ordering for the source finite-index carrier. HOL's `word <`
    compares the two's-complement values: different sign bits decide the
    result, and equal sign bits use unsigned order. Keep this definition in
    the HOL word adapter instead of selecting RISC-V's comparison instance. -/
def holWordSignedLess {width : Nat} (left right : BitVec width) : Bool :=
  let sign := 2 ^ (width - 1)
  if left.toNat < sign then
    if right.toNat < sign then decide (left.toNat < right.toNat) else false
  else if right.toNat < sign then
    true
  else
    decide (left.toNat < right.toNat)

theorem holWordSignedLess_eq_riscvSignedLess {width : Nat}
    (left right : BitVec width) :
    holWordSignedLess left right = RiscV.signedLess left right := rfl

/-! Generic finite-index word operations are transported by the explicit
    dimension enumeration. They are kept in their own namespace so existing
    Fin-specific instances remain the canonical production adapters. -/
namespace HolFiniteWord

variable {ι : Type u} [dimension : HolFiniteDimension ι]

instance : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩

instance : BEq (ι → Bool) :=
  ⟨fun left right => holWordToBitVec dimension left == holWordToBitVec dimension right⟩

instance (value : Nat) : OfNat (ι → Bool) value :=
  ⟨bitVecToHolWord dimension (BitVec.ofNat dimension.width value)⟩

instance : Add (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (holWordToBitVec dimension left + holWordToBitVec dimension right)⟩

instance : Mul (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (holWordToBitVec dimension left * holWordToBitVec dimension right)⟩

instance : Sub (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (holWordToBitVec dimension left - holWordToBitVec dimension right)⟩

instance : AndOp (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (AndOp.and (holWordToBitVec dimension left) (holWordToBitVec dimension right))⟩

instance : OrOp (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (OrOp.or (holWordToBitVec dimension left) (holWordToBitVec dimension right))⟩

instance : HXor (ι → Bool) (ι → Bool) (ι → Bool) :=
  ⟨fun left right => bitVecToHolWord dimension
    (HXor.hXor (holWordToBitVec dimension left) (holWordToBitVec dimension right))⟩

instance : Complement (ι → Bool) :=
  ⟨fun value => bitVecToHolWord dimension
    (Complement.complement (holWordToBitVec dimension value))⟩

instance : ShiftLeft (ι → Bool) :=
  ⟨fun value amount => bitVecToHolWord dimension
    (ShiftLeft.shiftLeft (holWordToBitVec dimension value)
      (holWordToBitVec dimension amount))⟩

instance : ShiftRight (ι → Bool) :=
  ⟨fun value amount => bitVecToHolWord dimension
    (ShiftRight.shiftRight (holWordToBitVec dimension value)
      (holWordToBitVec dimension amount))⟩

instance : LT (ι → Bool) :=
  ⟨fun left right => holWordToBitVec dimension left < holWordToBitVec dimension right⟩

instance : DecidableRel (fun left right : ι → Bool => left < right) := by
  intro left right
  change Decidable (holWordToBitVec dimension left < holWordToBitVec dimension right)
  infer_instance

instance : PanCmp (ι → Bool) :=
  ⟨fun left right => decide (holWordToBitVec dimension left <
      holWordToBitVec dimension right),
    fun left right => holWordSignedLess (holWordToBitVec dimension left)
      (holWordToBitVec dimension right)⟩

instance : PanShiftWidth (ι → Bool) :=
  ⟨dimension.width, fun value => (holWordToBitVec dimension value).toNat⟩

instance : ArithmeticShiftRight (ι → Bool) :=
  ⟨fun value amount => bitVecToHolWord dimension
    (BitVec.sshiftRight (holWordToBitVec dimension value)
      (holWordToBitVec dimension amount).toNat)⟩

instance : RotateRightOp (ι → Bool) :=
  ⟨fun value amount => bitVecToHolWord dimension
    (BitVec.rotateRight (holWordToBitVec dimension value)
      (holWordToBitVec dimension amount).toNat)⟩

end HolFiniteWord

theorem holFiniteWordToBitVec_zero {ι : Type u}
    [dimension : HolFiniteDimension ι] :
    holWordToBitVec dimension (0 : ι → Bool) = 0 := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0)) = _
  rw [holWordToBitVec_bitVecToHolWord]
  simp [BitVec.ofNat]

theorem holFiniteWordToBitVec_one {ι : Type u}
    [dimension : HolFiniteDimension ι] :
    holWordToBitVec dimension (1 : ι → Bool) = 1 := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension (BitVec.ofNat dimension.width 1)) = _
  rw [holWordToBitVec_bitVecToHolWord]
  simp [BitVec.ofNat]

theorem holFiniteWordToBitVec_add {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (left + right) =
      holWordToBitVec dimension left + holWordToBitVec dimension right := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (holWordToBitVec dimension left + holWordToBitVec dimension right)) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_mul {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (left * right) =
      holWordToBitVec dimension left * holWordToBitVec dimension right := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (holWordToBitVec dimension left * holWordToBitVec dimension right)) = _
  rw [holWordToBitVec_bitVecToHolWord]

/-! Source-shaped arithmetic for HOL4's `word_add_def` and `word_mul_def` in
    `$HOL/src/n-bit/wordsScript.sml`. HOL defines each operation by converting
    its operands with `w2n`, doing natural arithmetic, and converting back
    with `n2w`. These adapters use BitVec `toNat`/`ofNat` for those conversions.
    The pointwise `n2w`/FCP `BIT` equation and the HOL `w2n` weighted `SBIT`
    sum are stated through the explicit finite_index decoder and proved below;
    source-shaped add/mul/sub equations expose those conversions. They remain
    untagged because the chosen dictionary has not been identified as the
    concrete HOL instance for each index type, and the evaluator operations
    still need exact source correspondence. -/
def holFiniteWordN2W {ι : Type u} (dimension : HolFiniteDimension ι)
    (value : Nat) : ι → Bool :=
  bitVecToHolWord dimension (BitVec.ofNat dimension.width value)

theorem holFiniteWordN2W_at_index {ι : Type u}
    (dimension : HolFiniteDimension ι) (value : Nat) (index : ι) :
    holFiniteWordN2W dimension value index =
      Nat.testBit value (dimension.encode index).val := by
  simp [holFiniteWordN2W, bitVecToHolWord, finBitsToHolWord,
    bitVecToHolWordBits_ofNat]

/-- HOL `words$n2w_def` is `FCP i. BIT i n`. This equation states it at the
    `holFiniteIndex` decoder: for every valid natural index, the explicit word
    adapter reads precisely that bit. -/
theorem holFiniteWordN2W_at_finiteIndex {ι : Type u}
    (dimension : HolFiniteDimension ι) (value index : Nat)
    (hindex : index < dimension.width) :
    holFiniteWordN2W dimension value (holFiniteIndex dimension index) =
      Nat.testBit value index := by
  rw [holFiniteWordN2W_at_index]
  simp [holFiniteIndex, hindex, dimension.encode_decode]

def holFiniteWordW2N {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : ι → Bool) : Nat :=
  (holWordToBitVec dimension word).toNat

/-! Recursive finite spelling of HOL `SUM width (λi. SBIT (word i) i)`: the
    zero index contributes bit 0, while every later index's weight is twice
    its weight in the tail dimension. -/
def finWordSBitSum : (width : Nat) → (Fin width → Bool) → Nat
  | 0, _ => 0
  | width + 1, word =>
      (if word 0 then 1 else 0) +
        2 * finWordSBitSum width (fun index => word index.succ)

theorem finWordSBitSum_eq_holWordBitsToBitVec_toNat
    (width : Nat) (word : Fin width → Bool) :
    finWordSBitSum width word = (BitVec.ofBoolListLE (List.ofFn word)).toNat := by
  induction width with
  | zero =>
      have hlist : List.ofFn word = [] := by simp [List.ofFn]
      rw [hlist]
      simp [finWordSBitSum, BitVec.ofBoolListLE]
  | succ width ih =>
      change (if word 0 then 1 else 0) +
          2 * finWordSBitSum width (fun index => word index.succ) =
        (BitVec.ofBoolListLE (List.ofFn word)).toNat
      rw [List.ofFn_succ]
      rw [BitVec.ofBoolListLE, BitVec.toNat_concat, ih]
      cases word 0 <;> simp [Bool.toNat, Nat.mul_comm, Nat.add_comm]

theorem holWordBitsToBitVec_toNat_eq_ofBoolListLE {width : Nat}
    (word : Fin width → Bool) :
    (holWordBitsToBitVec word).toNat =
      (BitVec.ofBoolListLE (List.ofFn word)).toNat := by
  simp [holWordBitsToBitVec, BitVec.toNat_cast]

def holFiniteWordSBitSum {ι : Type u} (dimension : HolFiniteDimension ι)
    (word : ι → Bool) : Nat :=
  finWordSBitSum dimension.width (holWordToFinBits dimension word)

theorem holFiniteWordW2N_eq_SBitSum {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : ι → Bool) :
    holFiniteWordW2N dimension word = holFiniteWordSBitSum dimension word := by
  change (holWordBitsToBitVec (holWordToFinBits dimension word)).toNat =
    finWordSBitSum dimension.width (holWordToFinBits dimension word)
  rw [holWordBitsToBitVec_toNat_eq_ofBoolListLE]
  exact (finWordSBitSum_eq_holWordBitsToBitVec_toNat _ _).symm

/-- HOL `words$w2n_def` is `SUM dimindex (\i. SBIT (w ' i) i)`. This
    companion equation writes the same sum using the supplied `finite_index`
    decoder, so `holFiniteWordW2N`'s bit positions are explicit. -/
theorem holFiniteWordW2N_eq_finiteIndexSBitSum {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : ι → Bool) :
    holFiniteWordW2N dimension word =
      finWordSBitSum dimension.width
        (fun index => word (holFiniteIndex dimension index.val)) := by
  rw [holFiniteWordW2N_eq_SBitSum]
  change finWordSBitSum dimension.width (holWordToFinBits dimension word) = _
  congr 1
  funext index
  simp [holWordToFinBits, holFiniteIndex, index.isLt]

def holFiniteWordSourceAdd {ι : Type u} (dimension : HolFiniteDimension ι)
    (left right : ι → Bool) : ι → Bool :=
  holFiniteWordN2W dimension
    (holFiniteWordW2N dimension left + holFiniteWordW2N dimension right)

def holFiniteWordSourceMul {ι : Type u} (dimension : HolFiniteDimension ι)
    (left right : ι → Bool) : ι → Bool :=
  holFiniteWordN2W dimension
    (holFiniteWordW2N dimension left * holFiniteWordW2N dimension right)

def holFiniteWordSourceSub {ι : Type u} (dimension : HolFiniteDimension ι)
    (left right : ι → Bool) : ι → Bool :=
  holFiniteWordN2W dimension
    (holFiniteWordW2N dimension left +
      (2 ^ dimension.width - holFiniteWordW2N dimension right %
        2 ^ dimension.width))

theorem holFiniteWordSourceAdd_eq_n2w_SBitSum {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holFiniteWordSourceAdd dimension left right =
      holFiniteWordN2W dimension
        (holFiniteWordSBitSum dimension left + holFiniteWordSBitSum dimension right) := by
  simp [holFiniteWordSourceAdd, holFiniteWordW2N_eq_SBitSum]

theorem holFiniteWordSourceMul_eq_n2w_SBitSum {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holFiniteWordSourceMul dimension left right =
      holFiniteWordN2W dimension
        (holFiniteWordSBitSum dimension left * holFiniteWordSBitSum dimension right) := by
  simp [holFiniteWordSourceMul, holFiniteWordW2N_eq_SBitSum]

theorem holFiniteWordSourceSub_eq_n2w_SBitSum {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holFiniteWordSourceSub dimension left right =
      holFiniteWordN2W dimension
        (holFiniteWordSBitSum dimension left +
          (2 ^ dimension.width - holFiniteWordSBitSum dimension right %
            2 ^ dimension.width)) := by
  simp [holFiniteWordSourceSub, holFiniteWordW2N_eq_SBitSum]

theorem holFiniteWordSourceAdd_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holWordToBitVec dimension (holFiniteWordSourceAdd dimension left right) =
      holWordToBitVec dimension left + holWordToBitVec dimension right := by
  rw [holFiniteWordSourceAdd, holFiniteWordN2W, holFiniteWordW2N,
    holWordToBitVec_bitVecToHolWord]
  simp [holFiniteWordW2N, BitVec.ofNat_add]

theorem holFiniteWordSourceMul_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holWordToBitVec dimension (holFiniteWordSourceMul dimension left right) =
      holWordToBitVec dimension left * holWordToBitVec dimension right := by
  rw [holFiniteWordSourceMul, holFiniteWordN2W, holFiniteWordW2N,
    holWordToBitVec_bitVecToHolWord]
  simp [holFiniteWordW2N, BitVec.ofNat_mul]

/-- Source-shaped finite-word implementation of HOL `crep_op_def` for the
    explicitly enumerated word carrier. The `.mul` clause uses the HOL
    `word_mul_def` rendering above; every other argument shape fails exactly
    as the tagged word-typed `crepOpCrepWord` definition does. This helper has
    no standalone HOL declaration: it is an adapter from the source
    `n2w`/`w2n` representation to that tagged definition. -/
def holFiniteWordSourceCrepOp {ι : Type u}
    (dimension : HolFiniteDimension ι) :
    CrepOp → List (ι → Bool) → Option (ι → Bool)
  | .mul, [left, right] =>
      some (holFiniteWordSourceMul dimension left right)
  | _, _ => none

/-- The finite-word source implementation of CrepOp agrees with the tagged
    HOL `crep_op_def` after transporting each word to its canonical BitVec
    carrier, for every positive word width and every operand-list shape. -/
theorem holFiniteWordSourceCrepOp_to_crepOpCrepWord {ι : Type u}
    (dimension : HolFiniteDimension ι) (operator : CrepOp)
    (values : List (ι → Bool)) :
    (holFiniteWordSourceCrepOp dimension operator values).map
        (holWordToBitVec dimension) =
      crepOpCrepWord (width := dimension.width) operator
        (values.map (holWordToBitVec dimension)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases operator
  cases values with
  | nil => rfl
  | cons left rest =>
    cases rest with
    | nil => rfl
    | cons right tail =>
      cases tail with
      | nil =>
        simp [holFiniteWordSourceCrepOp, crepOpCrepWord,
          holFiniteWordSourceMul_toBitVec]
      | cons extra tail => rfl

/-- HOL `word_mul_def` and the production `Mul` instance on an explicitly
    finite Boolean-index carrier compute the same word.  HOL's source-shaped
    side is `n2w (w2n left * w2n right)`; production transports `BitVec` mul
    through the finite-index equivalence.  This all-dimension operation bridge
    is Flapjack support: the `HolFiniteDimension` witness has not been shown to
    be HOL's implicit `finite_index` dictionary, and this fact alone does not
    establish the `crepSem$eval` state/evaluator correspondence. -/
theorem holFiniteWordSourceMul_eq_mul {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holFiniteWordSourceMul dimension left right = left * right := by
  letI : HolFiniteDimension ι := dimension
  have hInjective : Function.Injective (holWordToBitVec dimension) := by
    intro x y h
    calc
      x = bitVecToHolWord dimension (holWordToBitVec dimension x) := by
        rw [bitVecToHolWord_holWordToBitVec]
      _ = bitVecToHolWord dimension (holWordToBitVec dimension y) :=
        congrArg (bitVecToHolWord dimension) h
      _ = y := bitVecToHolWord_holWordToBitVec dimension y
  apply hInjective
  rw [holFiniteWordSourceMul_toBitVec, holFiniteWordToBitVec_mul]

/-- The source finite-word CrepOp adapter also agrees with the production
    generic helper on its actual carrier. Combined with
    `holFiniteWordSourceCrepOp_to_crepOpCrepWord`, this relates both the
    production evaluator clause and the tagged HOL word-typed `crep_op_def`
    through the same source operation. -/
theorem holFiniteWordSourceCrepOp_eq_crepOpCrep {ι : Type u}
    (dimension : HolFiniteDimension ι) (operator : CrepOp)
    (values : List (ι → Bool)) :
    holFiniteWordSourceCrepOp dimension operator values =
      crepOpCrep operator values := by
  cases operator
  cases values with
  | nil => rfl
  | cons left rest =>
    cases rest with
    | nil => rfl
    | cons right tail =>
      cases tail with
      | nil =>
        simp [holFiniteWordSourceCrepOp, crepOpCrep,
          holFiniteWordSourceMul_eq_mul]
      | cons extra tail => rfl

theorem holFiniteWordSourceSub_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (left right : ι → Bool) :
    holWordToBitVec dimension (holFiniteWordSourceSub dimension left right) =
      holWordToBitVec dimension left - holWordToBitVec dimension right := by
  rw [holFiniteWordSourceSub, holFiniteWordN2W, holFiniteWordW2N,
    holWordToBitVec_bitVecToHolWord]
  change BitVec.ofNat dimension.width
      ((holWordToBitVec dimension left).toNat +
        (2 ^ dimension.width -
          (holWordToBitVec dimension right).toNat % 2 ^ dimension.width)) = _
  rw [Nat.add_comm _ (2 ^ dimension.width - _)]
  rw [← BitVec.ofNat_sub_ofNat]
  simp

theorem holFiniteWordToBitVec_and {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (AndOp.and left right) =
      AndOp.and (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (AndOp.and (holWordToBitVec dimension left) (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_or {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (OrOp.or left right) =
      OrOp.or (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (OrOp.or (holWordToBitVec dimension left) (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_xor {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (HXor.hXor left right) =
      HXor.hXor (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (HXor.hXor (holWordToBitVec dimension left) (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_sub {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (left - right) =
      holWordToBitVec dimension left - holWordToBitVec dimension right := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (holWordToBitVec dimension left - holWordToBitVec dimension right)) = _
  rw [holWordToBitVec_bitVecToHolWord]

private theorem mapFoldr {α : Type u} {β : Type v} (convert : α → β)
    (combine : α → α → α) (combineTarget : β → β → β)
    (hCombine : ∀ left right, convert (combine left right) =
      combineTarget (convert left) (convert right))
    (initial : α) (initialTarget : β) (hInitial : convert initial = initialTarget)
    (values : List α) :
    convert (values.foldr combine initial) =
      (values.map convert).foldr combineTarget initialTarget := by
  induction values with
  | nil => simp [hInitial]
  | cons head tail ih =>
      simp only [List.foldr_cons, List.map_cons]
      rw [hCombine, ih]

theorem holFiniteWord_wordOp_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (operator : BinOp)
    (values : List (ι → Bool)) :
    wordOp operator values =
      (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
        (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  cases operator with
  | and =>
      simp only [wordOpHOL, wordOp, Option.map_some]
      apply congrArg some
      let combine : (ι → Bool) → (ι → Bool) → (ι → Bool) := AndOp.and
      let combineTarget : BitVec dimension.width → BitVec dimension.width →
          BitVec dimension.width := AndOp.and
      have hseed : holWordToBitVec dimension
          (Complement.complement (0 : ι → Bool)) =
            Complement.complement (0 : BitVec dimension.width) := by
        change holWordToBitVec dimension
          (bitVecToHolWord dimension
            (Complement.complement (holWordToBitVec dimension (0 : ι → Bool)))) = _
        rw [holWordToBitVec_bitVecToHolWord, holFiniteWordToBitVec_zero]
      have hfold := mapFoldr (holWordToBitVec dimension) combine combineTarget
        (by intro left right; exact holFiniteWordToBitVec_and left right)
        (Complement.complement (0 : ι → Bool))
        (Complement.complement (0 : BitVec dimension.width)) hseed values
      exact (bitVecToHolWord_holWordToBitVec dimension _).symm.trans
        (congrArg (bitVecToHolWord dimension) hfold)
  | add =>
      simp only [wordOpHOL, wordOp, Option.map_some]
      apply congrArg some
      let combine : (ι → Bool) → (ι → Bool) → (ι → Bool) := fun left right => left + right
      let combineTarget : BitVec dimension.width → BitVec dimension.width →
          BitVec dimension.width := fun left right => left + right
      have hfold := mapFoldr (holWordToBitVec dimension) combine combineTarget
        (by intro left right; exact holFiniteWordToBitVec_add left right)
        (0 : ι → Bool) (0 : BitVec dimension.width) holFiniteWordToBitVec_zero values
      exact (bitVecToHolWord_holWordToBitVec dimension _).symm.trans
        (congrArg (bitVecToHolWord dimension) hfold)
  | or =>
      simp only [wordOpHOL, wordOp, Option.map_some]
      apply congrArg some
      let combine : (ι → Bool) → (ι → Bool) → (ι → Bool) := OrOp.or
      let combineTarget : BitVec dimension.width → BitVec dimension.width →
          BitVec dimension.width := OrOp.or
      have hfold := mapFoldr (holWordToBitVec dimension) combine combineTarget
        (by intro left right; exact holFiniteWordToBitVec_or left right)
        (0 : ι → Bool) (0 : BitVec dimension.width) holFiniteWordToBitVec_zero values
      exact (bitVecToHolWord_holWordToBitVec dimension _).symm.trans
        (congrArg (bitVecToHolWord dimension) hfold)
  | xor =>
      simp only [wordOpHOL, wordOp, Option.map_some]
      apply congrArg some
      let combine : (ι → Bool) → (ι → Bool) → (ι → Bool) := HXor.hXor
      let combineTarget : BitVec dimension.width → BitVec dimension.width →
          BitVec dimension.width := HXor.hXor
      have hfold := mapFoldr (holWordToBitVec dimension) combine combineTarget
        (by intro left right; exact holFiniteWordToBitVec_xor left right)
        (0 : ι → Bool) (0 : BitVec dimension.width) holFiniteWordToBitVec_zero values
      exact (bitVecToHolWord_holWordToBitVec dimension _).symm.trans
        (congrArg (bitVecToHolWord dimension) hfold)
  | sub =>
      cases values with
      | nil => rfl
      | cons left tail =>
          cases tail with
          | nil => rfl
          | cons right rest =>
              cases rest with
              | nil =>
                  simp only [wordOpHOL, wordOp]
                  apply congrArg some
                  exact (bitVecToHolWord_holWordToBitVec dimension (left - right)).symm.trans
                    (congrArg (bitVecToHolWord dimension)
                      (holFiniteWordToBitVec_sub left right))
              | cons extra rest => rfl

theorem holFiniteWordToBitVec_shiftRight {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (ShiftRight.shiftRight left right) =
      ShiftRight.shiftRight (holWordToBitVec dimension left)
        (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (ShiftRight.shiftRight (holWordToBitVec dimension left)
        (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_shiftLeft {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (ShiftLeft.shiftLeft left right) =
      ShiftLeft.shiftLeft (holWordToBitVec dimension left)
        (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (ShiftLeft.shiftLeft (holWordToBitVec dimension left)
        (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_asr {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (ArithmeticShiftRight.arithmeticShiftRight left right) =
      ArithmeticShiftRight.arithmeticShiftRight
        (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (BitVec.sshiftRight (holWordToBitVec dimension left)
        (holWordToBitVec dimension right).toNat)) =
    BitVec.sshiftRight (holWordToBitVec dimension left)
      (holWordToBitVec dimension right).toNat
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWordToBitVec_ror {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (RotateRightOp.rotateRight left right) =
      RotateRightOp.rotateRight
        (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (BitVec.rotateRight (holWordToBitVec dimension left)
        (holWordToBitVec dimension right).toNat)) =
    BitVec.rotateRight (holWordToBitVec dimension left)
      (holWordToBitVec dimension right).toNat
  rw [holWordToBitVec_bitVecToHolWord]

theorem holFiniteWord_evalPanShift_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (operator : Shift)
    (left right : ι → Bool) :
    evalPanShiftFull operator left right =
      (evalPanShiftFull operator (holWordToBitVec dimension left)
        (holWordToBitVec dimension right)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hWidthSource : PanShiftWidth.width (α := ι → Bool) = dimension.width := rfl
  have hAmountSource (value : ι → Bool) :
      PanShiftWidth.amount (α := ι → Bool) value =
        (holWordToBitVec dimension value).toNat := rfl
  have hWidthBits : PanShiftWidth.width (α := BitVec dimension.width) =
      dimension.width := rfl
  have hAmountBits (value : BitVec dimension.width) :
      PanShiftWidth.amount (α := BitVec dimension.width) value = value.toNat := rfl
  cases operator with
  | lsl =>
      simp only [evalPanShiftFull, hWidthSource, hAmountSource, hWidthBits, hAmountBits]
      by_cases h : (holWordToBitVec dimension right).toNat ≠ 0 ∧
          dimension.width ≤ (holWordToBitVec dimension right).toNat
      · simp [h]
      · simp [h]
        rw [← bitVecToHolWord_holWordToBitVec dimension
          (ShiftLeft.shiftLeft left right), holFiniteWordToBitVec_shiftLeft]
  | lsr =>
      simp only [evalPanShiftFull, hWidthSource, hAmountSource, hWidthBits, hAmountBits]
      by_cases h : (holWordToBitVec dimension right).toNat ≠ 0 ∧
          dimension.width ≤ (holWordToBitVec dimension right).toNat
      · simp [h]
      · simp [h]
        rw [← bitVecToHolWord_holWordToBitVec dimension
          (ShiftRight.shiftRight left right), holFiniteWordToBitVec_shiftRight]
  | asr =>
      simp only [evalPanShiftFull, hWidthSource, hAmountSource, hWidthBits, hAmountBits]
      by_cases h : (holWordToBitVec dimension right).toNat ≠ 0 ∧
          dimension.width ≤ (holWordToBitVec dimension right).toNat
      · simp [h]
      · simp [h]
        rw [← bitVecToHolWord_holWordToBitVec dimension
          (ArithmeticShiftRight.arithmeticShiftRight left right),
          holFiniteWordToBitVec_asr]
  | ror =>
      simp only [evalPanShiftFull, hWidthSource, hAmountSource, hWidthBits, hAmountBits]
      by_cases h : (holWordToBitVec dimension right).toNat ≠ 0 ∧
          dimension.width ≤ (holWordToBitVec dimension right).toNat
      · simp [h]
      · simp [h]
        rw [← bitVecToHolWord_holWordToBitVec dimension
          (RotateRightOp.rotateRight left right), holFiniteWordToBitVec_ror]

/-! The generic `Cmp` operation used by the source-shaped finite-word
    evaluator is transported through the same finite-index/BitVec equivalence
    as its operands. -/
theorem holFiniteWord_evalPanCmp_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (operator : Cmp)
    (left right : ι → Bool) :
    holWordToBitVec dimension (evalPanCmp operator left right) =
      evalPanCmp operator (holWordToBitVec dimension left)
        (holWordToBitVec dimension right) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  have hOneZero (condition : Bool) :
      holWordToBitVec dimension (if condition then (1 : ι → Bool) else 0) =
        (if condition then (1 : BitVec dimension.width) else 0) := by
    cases condition <;> simp [holFiniteWordToBitVec_zero,
      holFiniteWordToBitVec_one]
  have hZeroOne (condition : Bool) :
      holWordToBitVec dimension (if condition then (0 : ι → Bool) else 1) =
        (if condition then (0 : BitVec dimension.width) else 1) := by
    cases condition <;> simp [holFiniteWordToBitVec_zero,
      holFiniteWordToBitVec_one]
  cases operator with
  | equal =>
      have hcondition : (left == right) =
          (holWordToBitVec dimension left == holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hOneZero _
  | notEqual =>
      have hcondition : (left == right) =
          (holWordToBitVec dimension left == holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hZeroOne _
  | lower =>
      have hcondition : PanCmp.lower left right =
          PanCmp.lower (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hOneZero _
  | notLower =>
      have hcondition : PanCmp.lower left right =
          PanCmp.lower (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hZeroOne _
  | less =>
      have hcondition : PanCmp.less left right =
          PanCmp.less (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hOneZero _
  | notLess =>
      have hcondition : PanCmp.less left right =
          PanCmp.less (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) := rfl
      simp only [evalPanCmp]
      rw [hcondition]
      exact hZeroOne _
  | test =>
      have hcondition : (AndOp.and left right == (0 : ι → Bool)) =
          (AndOp.and (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) == (0 : BitVec dimension.width)) := by
        change (holWordToBitVec dimension (AndOp.and left right) ==
          holWordToBitVec dimension (0 : ι → Bool)) = _
        rw [holFiniteWordToBitVec_and, holFiniteWordToBitVec_zero]
      simp only [evalPanCmp]
      rw [hcondition]
      exact hOneZero _
  | notTest =>
      have hcondition : (AndOp.and left right == (0 : ι → Bool)) =
          (AndOp.and (holWordToBitVec dimension left)
            (holWordToBitVec dimension right) == (0 : BitVec dimension.width)) := by
        change (holWordToBitVec dimension (AndOp.and left right) ==
          holWordToBitVec dimension (0 : ι → Bool)) = _
        rw [holFiniteWordToBitVec_and, holFiniteWordToBitVec_zero]
      simp only [evalPanCmp]
      rw [hcondition]
      exact hZeroOne _

/-! Operations on finite-index HOL word bits are transported through the
    equivalence above. This gives the production Crep evaluator and arithmetic
    simplifier their standard word interfaces on the function-valued carrier,
    with bitvector arithmetic as the implementation. -/
namespace HolWordBits

variable {width : Nat}

instance : BEq (Fin width → Bool) :=
  ⟨fun left right => holWordBitsToBitVec left == holWordBitsToBitVec right⟩

instance (value : Nat) : OfNat (Fin width → Bool) value :=
  ⟨bitVecToHolWordBits (BitVec.ofNat width value)⟩

instance : Add (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (holWordBitsToBitVec left + holWordBitsToBitVec right)⟩

instance : Mul (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (holWordBitsToBitVec left * holWordBitsToBitVec right)⟩

instance : Sub (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (holWordBitsToBitVec left - holWordBitsToBitVec right)⟩

instance : AndOp (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (AndOp.and (holWordBitsToBitVec left) (holWordBitsToBitVec right))⟩

instance : OrOp (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (OrOp.or (holWordBitsToBitVec left) (holWordBitsToBitVec right))⟩

instance : HXor (Fin width → Bool) (Fin width → Bool) (Fin width → Bool) :=
  ⟨fun left right => bitVecToHolWordBits
    (HXor.hXor (holWordBitsToBitVec left) (holWordBitsToBitVec right))⟩

instance : Complement (Fin width → Bool) :=
  ⟨fun value => bitVecToHolWordBits (Complement.complement
    (holWordBitsToBitVec value))⟩

instance : ShiftLeft (Fin width → Bool) :=
  ⟨fun value amount => bitVecToHolWordBits (ShiftLeft.shiftLeft
    (holWordBitsToBitVec value) (holWordBitsToBitVec amount))⟩

instance : ShiftRight (Fin width → Bool) :=
  ⟨fun value amount => bitVecToHolWordBits (ShiftRight.shiftRight
    (holWordBitsToBitVec value) (holWordBitsToBitVec amount))⟩

instance : LT (Fin width → Bool) :=
  ⟨fun left right => holWordBitsToBitVec left < holWordBitsToBitVec right⟩

instance : DecidableRel (fun left right : Fin width → Bool => left < right) := by
  intro left right
  change Decidable (holWordBitsToBitVec left < holWordBitsToBitVec right)
  infer_instance

instance : PanCmp (Fin width → Bool) :=
  ⟨fun left right => decide (holWordBitsToBitVec left < holWordBitsToBitVec right),
    fun left right => holWordSignedLess
      (holWordBitsToBitVec left) (holWordBitsToBitVec right)⟩

instance : PanShiftWidth (Fin width → Bool) :=
  ⟨width, fun value => (holWordBitsToBitVec value).toNat⟩

instance : ArithmeticShiftRight (Fin width → Bool) :=
  ⟨fun value amount => bitVecToHolWordBits
    (BitVec.sshiftRight (holWordBitsToBitVec value)
      (holWordBitsToBitVec amount).toNat)⟩

instance : RotateRightOp (Fin width → Bool) :=
  ⟨fun value amount => bitVecToHolWordBits
    (BitVec.rotateRight (holWordBitsToBitVec value)
      (holWordBitsToBitVec amount).toNat)⟩

end HolWordBits

/-- Flapjack-only numeral conversion for the finite-index word adapter; HOL
    uses its native polymorphic word numeral definitions. -/
@[simp] theorem holWordBitsToBitVec_zero {width : Nat} :
    holWordBitsToBitVec (0 : Fin width → Bool) = (0 : BitVec width) := by
  change holWordBitsToBitVec (bitVecToHolWordBits (BitVec.ofNat width 0)) = _
  rw [holWordBitsToBitVec_bitVecToHolWordBits]
  simp

/-- Flapjack-only equality conversion for the finite-index word adapter. -/
@[simp] theorem holWordBitsToBitVec_beq {width : Nat}
    (left right : Fin width → Bool) :
    (left == right) = (holWordBitsToBitVec left == holWordBitsToBitVec right) := rfl

/-- Flapjack-only low-bit operation conversion used by the recognizer bridge. -/
@[simp] theorem holWordBitsToBitVec_andOp {width : Nat}
    (left right : Fin width → Bool) :
    holWordBitsToBitVec (AndOp.and left right) =
      AndOp.and (holWordBitsToBitVec left) (holWordBitsToBitVec right) := by
  change holWordBitsToBitVec (bitVecToHolWordBits
    (AndOp.and (holWordBitsToBitVec left) (holWordBitsToBitVec right))) = _
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

/-- Flapjack-only logical-right-shift conversion used by the recognizer bridge. -/
@[simp] theorem holWordBitsToBitVec_shiftRight {width : Nat}
    (left right : Fin width → Bool) :
    holWordBitsToBitVec (ShiftRight.shiftRight left right) =
      ShiftRight.shiftRight (holWordBitsToBitVec left) (holWordBitsToBitVec right) := by
  change holWordBitsToBitVec (bitVecToHolWordBits
    (ShiftRight.shiftRight (holWordBitsToBitVec left) (holWordBitsToBitVec right))) = _
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

@[simp] theorem holWordBitsToBitVec_add {width : Nat}
    (left right : Fin width → Bool) :
    holWordBitsToBitVec (left + right) =
      holWordBitsToBitVec left + holWordBitsToBitVec right := by
  change holWordBitsToBitVec (bitVecToHolWordBits
    (holWordBitsToBitVec left + holWordBitsToBitVec right)) = _
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

@[simp] theorem holWordBitsToBitVec_mul {width : Nat}
    (left right : Fin width → Bool) :
    holWordBitsToBitVec (left * right) =
      holWordBitsToBitVec left * holWordBitsToBitVec right := by
  change holWordBitsToBitVec (bitVecToHolWordBits
    (holWordBitsToBitVec left * holWordBitsToBitVec right)) = _
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

@[simp] theorem holWordBitsToBitVec_one {width : Nat} :
    holWordBitsToBitVec (1 : Fin width → Bool) = BitVec.ofNat width 1 := by
  change holWordBitsToBitVec (bitVecToHolWordBits (BitVec.ofNat width 1)) =
    BitVec.ofNat width 1
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

def holWordBitsRiscVMemoryModel [NeZero width] (bigEndian : Bool) :
    PanMemoryModel (Fin width → Bool) :=
  let model := RiscV.panRiscVMemoryModelForEndian bigEndian
  { byteAlign := fun bytes address => bitVecToHolWordBits
      (model.byteAlign (holWordBitsToBitVec bytes) (holWordBitsToBitVec address))
    getByte := fun bytes address value be => bitVecToHolWordBits
      (model.getByte (holWordBitsToBitVec bytes) (holWordBitsToBitVec address)
        (holWordBitsToBitVec value) be)
    setByte := fun bytes address byte value be => bitVecToHolWordBits
      (model.setByte (holWordBitsToBitVec bytes) (holWordBitsToBitVec address)
        (holWordBitsToBitVec byte) (holWordBitsToBitVec value) be)
    aligned := fun alignment address => model.aligned alignment
      (holWordBitsToBitVec address)
    wordOfBytes := fun be bytes => bitVecToHolWordBits
      (model.wordOfBytes be (bytes.map holWordBitsToBitVec))
    wordOfBytes32 := fun be bytes => bitVecToHolWordBits
      (model.wordOfBytes32 be (bytes.map holWordBitsToBitVec))
    wordOp := fun operator values =>
      (model.wordOp operator (values.map holWordBitsToBitVec)).map
        bitVecToHolWordBits
    compare := fun operator left right => bitVecToHolWordBits
      (model.compare operator (holWordBitsToBitVec left) (holWordBitsToBitVec right))
    shift := fun operator left right =>
      (model.shift operator (holWordBitsToBitVec left) (holWordBitsToBitVec right)).map
        bitVecToHolWordBits }

private def crepHolEvalFfiContext [OfNat α 0] : PanValueFfiContext α where
  sharedDomain := fun _ => false
  byteAlign := id
  bigEndian := false
  wordToBytes := fun _ _ => []
  wordOfBytes := fun _ _ => 0
  wordToByte := fun _ => 0
  byteToWord := fun _ => 0
  valueToNat := fun _ => 0

/-- Add the executable-only fields needed by the production evaluator. Its
    word operations and byte accessors are fixed from the word width and HOL's
    `be`; the placeholder FFI codec is unused by expression evaluation. -/
def CrepHolState.toRuntime [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepRuntimeState (RiscV.Word width) σ :=
  { locals := state.locals
    globals := state.globals
    code := state.code
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    memoryModel := RiscV.panRiscVMemoryModelForEndian state.bigEndian
    bytesInWord := BitVec.ofNat width (width / 8)
    ffiContext := crepHolEvalFfiContext
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

/-- `toHolState` is a left inverse of `toRuntime` on the 11 encoded fields. -/
theorem CrepHolState.toHolState_toRuntime [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    state.toRuntime.toHolState = state := rfl

/-- Production adapter: the exact HOL-shaped `setCrepHolGlobals` on the
    field-only state commutes with `CrepHolState.toRuntime`, so the executable
    `setCrepRuntimeGlobals` performs the same global update. -/
theorem setCrepHolGlobals_toRuntime [NeZero width]
    (key : BitVec 5) (value : PanWordLab (RiscV.Word width))
    (state : CrepHolState (RiscV.Word width) σ) :
    (setCrepHolGlobals key value state).toRuntime =
      setCrepRuntimeGlobals key value state.toRuntime := rfl

/-! Production `CrepRuntimeState` adapter for a finite-index HOL word state.
    The target's word operations and byte accessors are lifted through the
    finite-index/BitVec equivalence. FFI fields are expression-irrelevant, as
    in `CrepHolState.toRuntime`. -/
def CrepHolState.toHolWordBitsRuntime [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) :
    CrepRuntimeState (Fin width → Bool) σ :=
  { locals := state.locals
    globals := state.globals
    code := state.code
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    memoryModel := holWordBitsRiscVMemoryModel state.bigEndian
    bytesInWord := bitVecToHolWordBits (BitVec.ofNat width (width / 8))
    ffiContext := crepHolEvalFfiContext
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

/-! Structural change of word carrier for expression-evaluator comparison.
    The HOL state code map is omitted because `crepSem$eval` never reads code;
    expression-only correspondence therefore does not need to translate
    stored programs. -/
def mapCrepExpWord {α β : Type} (convert : α → β) :
    CrepExp α → CrepExp β
  | .const value => .const (convert value)
  | .var name => .var name
  | .load address => .load (mapCrepExpWord convert address)
  | .load32 address => .load32 (mapCrepExpWord convert address)
  | .loadByte address => .loadByte (mapCrepExpWord convert address)
  | .loadGlob address => .loadGlob address
  | .op operator expressions =>
      .op operator (expressions.map (mapCrepExpWord convert))
  | .crepOp operator expressions =>
      .crepOp operator (expressions.map (mapCrepExpWord convert))
  | .cmp operator left right =>
      .cmp operator (mapCrepExpWord convert left) (mapCrepExpWord convert right)
  | .shift operator left right =>
      .shift operator (mapCrepExpWord convert left) (mapCrepExpWord convert right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

def mapCrepHolWordLab (convert : α → β) : PanWordLab α → PanWordLab β
  | .word value => .word (convert value)

def CrepHolState.toBitVecState [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) :
    CrepHolState (RiscV.Word width) σ :=
  { locals := fun name => (state.locals name).map
      (mapCrepHolWordLab holWordBitsToBitVec)
    globals := fun name => (state.globals name).map
      (mapCrepHolWordLab holWordBitsToBitVec)
    code := fun _ => none
    memory := fun address => mapCrepHolWordLab holWordBitsToBitVec
      (state.memory (bitVecToHolWordBits address))
    memaddrs := fun address => state.memaddrs (bitVecToHolWordBits address)
    shMemaddrs := fun address => state.shMemaddrs (bitVecToHolWordBits address)
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := holWordBitsToBitVec state.baseAddress
    topAddress := holWordBitsToBitVec state.topAddress }

def transportPanMemoryModel {α : Type u} {β : Type v} (convert : α → β)
    (retract : β → α) (model : PanMemoryModel α) : PanMemoryModel β where
  byteAlign := fun bytes address => convert
    (model.byteAlign (retract bytes) (retract address))
  getByte := fun bytes address value bigEndian => convert
    (model.getByte (retract bytes) (retract address) (retract value) bigEndian)
  setByte := fun bytes address byte value bigEndian => convert
    (model.setByte (retract bytes) (retract address) (retract byte)
      (retract value) bigEndian)
  aligned := fun alignment address => model.aligned alignment (retract address)
  wordOfBytes := fun bigEndian bytes => convert
    (model.wordOfBytes bigEndian (bytes.map retract))
  wordOfBytes32 := fun bigEndian bytes => convert
    (model.wordOfBytes32 bigEndian (bytes.map retract))
  wordOp := fun operator values =>
    (model.wordOp operator (values.map retract)).map convert
  compare := fun operator left right => convert
    (model.compare operator (retract left) (retract right))
  shift := fun operator left right =>
    (model.shift operator (retract left) (retract right)).map convert

def holFiniteWordRiscVMemoryModel {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool) :
    PanMemoryModel (ι → Bool) :=
  transportPanMemoryModel (bitVecToHolWord dimension)
    (holWordToBitVec dimension)
    (RiscV.panRiscVMemoryModelForEndian bigEndian)

/-! HOL `byte_align_def` clears the low bits selected by
    `LOG2 (dimindex DIV 8)`. This differs from target rounding when a word has
    a non-power-of-two number of bytes. -/
def holByteAlignBitVec [NeZero width] (address : BitVec width) : BitVec width :=
  let alignment := 2 ^ Nat.log2 (width / 8)
  BitVec.ofNat width ((address.toNat / alignment) * alignment)

/-! Source-shaped finite-word memory adapter. Its byteAlign, getByte, and
    aligned fields encode the imported HOL formulas through the finite-word /
    BitVec equivalence. `setByte` implements the pointwise bit-slice cases in
    HOL's `set_byte_def`, and `wordOfBytes` follows the recursive
    `word_of_bytes_def`. Generic finite-word/BitVec transport is now proved for
    byte alignment, `setByte`, recursive `wordOfBytes`, and the byte/word load
    helpers. This does not identify the transported model with the production
    RISC-V memory model at every width (the 24-bit alignment counterexample is
    documented above), or identify the explicit enumeration with HOL's
    implicit `finite_index` dictionary. Word operators, comparisons, and shifts
    use generic source-level definitions. This runtime supports the untagged
    recursive preservation theorem; production evaluator correspondence and
    unrestricted HOL carrier identification remain open. -/
def holFiniteWordSourceByteAlign {ι : Type u}
    (dimension : HolFiniteDimension ι) (address : ι → Bool) : ι → Bool := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  exact bitVecToHolWord dimension
    (holByteAlignBitVec (holWordToBitVec dimension address))

/-- The source memory model's `byteAlign` field is exactly HOL's
    dimension-derived alignment after transporting the explicit finite word
    through its BitVec encoding. In particular, it uses
    `2 ^ log2 (width / 8)`, so this equation remains valid for dimensions
    whose byte count is not a power of two. -/
theorem holFiniteWordSourceByteAlign_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (address : ι → Bool) :
    holWordToBitVec dimension
        (holFiniteWordSourceByteAlign dimension address) =
      holByteAlignBitVec (holWordToBitVec dimension address) := by
  simp [holFiniteWordSourceByteAlign, holWordToBitVec_bitVecToHolWord]

/-- Byte-slot component of HOL `byte_index_def`, preserving HOL natural
    `MOD_0` when the dimension has fewer than eight bits. -/
def holFiniteWordSourceByteIndex {ι : Type u}
    (dimension : HolFiniteDimension ι) (address : ι → Bool)
    (bigEndian : Bool) : Nat :=
  let bytesPerWord := dimension.width / 8
  let addressIndex := (holWordToBitVec dimension address).toNat
  -- HOL natural MOD uses x MOD 0 = x. This matters for word dimensions below
  -- eight bits, where dimindex DIV 8 is zero.
  let byteIndex := if bytesPerWord = 0 then addressIndex
    else addressIndex % bytesPerWord
  if bigEndian then bytesPerWord - 1 - byteIndex else byteIndex

/-- HOL `byte_index_def` uses `8 * (w2n address MOD bytesPerWord)` in
    little-endian mode, and counts that slot backward in big-endian mode.
    This equation exposes the source `w2n` through its already-proved
    weighted-SBIT representation; the `bytesPerWord = 0` branch preserves
    HOL's `MOD_0` behavior. -/
theorem holFiniteWordSourceByteIndex_eq_holW2N {ι : Type u}
    (dimension : HolFiniteDimension ι) (address : ι → Bool)
    (bigEndian : Bool) :
    8 * holFiniteWordSourceByteIndex dimension address bigEndian =
      if bigEndian then
        8 * (dimension.width / 8 - 1 -
          (holFiniteWordW2N dimension address % (dimension.width / 8)))
      else
        8 * (holFiniteWordW2N dimension address % (dimension.width / 8)) := by
  have haddress : (holWordToBitVec dimension address).toNat =
      holFiniteWordSBitSum dimension address := by
    change holFiniteWordW2N dimension address = _
    exact holFiniteWordW2N_eq_SBitSum dimension address
  rw [holFiniteWordW2N_eq_SBitSum]
  unfold holFiniteWordSourceByteIndex
  rw [haddress]
  by_cases hbytes : dimension.width / 8 = 0
  · cases bigEndian <;> simp [hbytes]
  · cases bigEndian <;> simp [hbytes]

/-- Pointwise form of HOL `get_byte_def`: output bit `j` is source bit
    `j + 8 * byteIndex`, provided `j` belongs to the result `word8`. -/
def holFiniteWordSourceGetByte {ι : Type u}
    (dimension : HolFiniteDimension ι) (address value : ι → Bool)
    (bigEndian : Bool) : ι → Bool :=
  let byteIndex := holFiniteWordSourceByteIndex dimension address bigEndian
  let bitOffset := 8 * byteIndex
  let valueBits := holWordToBitVec dimension value
  fun index =>
    let bit := (dimension.encode index).val
    decide (bit < 8) && valueBits.getLsbD (bit + bitOffset)

/-- HOL `get_byte_def` is `w2w (w ⋙ byte_index)`. Pointwise, its
    source-shaped finite-word implementation is the low eight bits of a
    logical BitVec shift, for every explicit dimension and byte order. This
    equation is the operation bridge consumed by generic byte-load proofs. -/
theorem holFiniteWordSourceGetByte_atIndex {ι : Type u}
    (dimension : HolFiniteDimension ι) (address value : ι → Bool)
    (bigEndian : Bool) (index : Fin dimension.width) :
    holFiniteWordSourceGetByte dimension address value bigEndian
        (dimension.decode index) =
      (decide (index.val < 8) &&
        BitVec.getLsbD (holWordToBitVec dimension value >>>
          (8 * holFiniteWordSourceByteIndex dimension address bigEndian))
          index.val) := by
  simp [holFiniteWordSourceGetByte, holFiniteWordSourceByteIndex,
    dimension.encode_decode, Nat.add_comm]

/-- After transporting the source `get_byte` result to BitVec, each output
    bit is exactly the corresponding bit of the logically shifted source word,
    restricted to the low eight positions. This exposes HOL's `w2w`/logical
    shift behavior at the memory-model field boundary for every dimension. -/
theorem holFiniteWordSourceGetByte_toBitVec_getLsbD {ι : Type u}
    (dimension : HolFiniteDimension ι) (address value : ι → Bool)
    (bigEndian : Bool) (index : Fin dimension.width) :
    BitVec.getLsbD
        (holWordToBitVec dimension
          (holFiniteWordSourceGetByte dimension address value bigEndian))
        index.val =
      (decide (index.val < 8) &&
        BitVec.getLsbD
          (holWordToBitVec dimension value >>>
            (8 * holFiniteWordSourceByteIndex dimension address bigEndian))
          index.val) := by
  rw [holWordToBitVec_getLsbD dimension _ index]
  exact holFiniteWordSourceGetByte_atIndex dimension address value bigEndian index

/-- Whole-word form of the HOL `get_byte_def` transport. The result is a
    carrier-width `w2w` of the low eight bits of the logically shifted source
    word, including truncation when the carrier is narrower than one byte. -/
theorem holFiniteWordSourceGetByte_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (address value : ι → Bool)
    (bigEndian : Bool) :
    holWordToBitVec dimension
        (holFiniteWordSourceGetByte dimension address value bigEndian) =
      BitVec.ofNat dimension.width
        ((holWordToBitVec dimension value >>>
          (8 * holFiniteWordSourceByteIndex dimension address bigEndian)).toNat % 2^8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  rw [holFiniteWordSourceGetByte_toBitVec_getLsbD
    dimension address value bigEndian ⟨index, hindex⟩]
  rw [BitVec.getLsbD_ofNat]
  by_cases hbyte : index < 8
  · rw [Nat.testBit_mod_two_pow]
    simp [hbyte, BitVec.getLsbD_eq_getElem, hindex,
      BitVec.getElem_eq_testBit_toNat, Nat.testBit_shiftRight]
  · rw [Nat.testBit_mod_two_pow]
    simp [hbyte, BitVec.getLsbD_eq_getElem, hindex,
      BitVec.getElem_eq_testBit_toNat, Nat.testBit_shiftRight]

/-- Pointwise `word_slice_alt`/shift/or expansion of HOL `set_byte_def`. -/
def holFiniteWordSourceSetByte {ι : Type u}
    (dimension : HolFiniteDimension ι) (address byte value : ι → Bool)
    (bigEndian : Bool) : ι → Bool :=
  let byteIndex := holFiniteWordSourceByteIndex dimension address bigEndian
  let bitOffset := 8 * byteIndex
  let byteBits := holWordToBitVec dimension byte
  fun index =>
    let bit := (dimension.encode index).val
    let keepHigh := decide (bitOffset + 8 ≤ bit ∧ bit < dimension.width) && value index
    let insertByte := decide (bitOffset ≤ bit ∧ bit < bitOffset + 8) &&
      byteBits.getLsbD (bit - bitOffset)
    let keepLow := decide (bit < bitOffset) && value index
    keepHigh || insertByte || keepLow

/-- BitVec form of HOL `set_byte_def`: retain the high slice, insert the
    low eight bits of the byte at its byte offset, and retain the low slice. -/
def holFiniteWordSetByteBitVec (width offset : Nat)
    (byte value : BitVec width) : BitVec width :=
  (((value >>> (offset + 8)) <<< (offset + 8)) |||
      ((BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)) <<< offset)) |||
    BitVec.setWidth width (BitVec.extractLsb' 0 offset value)

/-- Flapjack BitVec encoding lemma, with no separate HOL declaration: it gives
    the Nat value of a zero-based low slice after widening it back to the
    carrier width. Keeping this normalization separate makes the later
    four-byte `word_of_bytes` proof reason about bounded Nat lanes. -/
private theorem setWidth_extractLsb_zero_toNat (width length : Nat)
    (value : BitVec width) (hlen : length ≤ width) :
    (BitVec.setWidth width (BitVec.extractLsb' 0 length value)).toNat =
      value.toNat % 2 ^ length := by
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have hsmall : value.toNat % 2 ^ length < 2 ^ length :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpow : 2 ^ length ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by omega) hlen
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hsmall hpow)]

/-- Flapjack proof infrastructure for the BitVec encoding of HOL `set_byte`;
    HOL has no separate Nat equation for this helper. The lower slice, inserted
    byte, and preserved upper slice occupy disjoint bit ranges. -/
private theorem holFiniteWordSetByteBitVec_toNat (width offset : Nat)
    (byte value : BitVec width) (hoffset : offset + 8 ≤ width) :
    (holFiniteWordSetByteBitVec width offset byte value).toNat =
      (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset := by
  have hlow : value.toNat % 2 ^ offset < 2 ^ offset :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbyte : byte.toNat % 2 ^ 8 < 2 ^ 8 :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmid : (byte.toNat % 2 ^ 8) * 2 ^ offset +
      value.toNat % 2 ^ offset < 2 ^ (offset + 8) := by
    have hpow : 2 ^ (offset + 8) = 256 * 2 ^ offset := by
      rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]
    have hbyteLe : byte.toNat % 2 ^ 8 ≤ 255 := by omega
    have hscaled := Nat.mul_le_mul_right (2 ^ offset) hbyteLe
    rw [hpow]
    omega
  have hhigh : (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) <
      2 ^ width := by
    have hdiv := Nat.div_mul_le_self value.toNat (2 ^ (offset + 8))
    have hpow : 2 ^ (offset + 8) ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by omega) hoffset
    omega
  have hlane : (byte.toNat % 2 ^ 8) * 2 ^ offset < 2 ^ width := by
    have hbyteTimes : (byte.toNat % 2 ^ 8) * 2 ^ offset <
        2 ^ (offset + 8) := by
      have hscaled := Nat.mul_lt_mul_of_pos_right hbyte (Nat.two_pow_pos offset)
      have hpow : 2 ^ (offset + 8) = 256 * 2 ^ offset := by
        rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]
      rw [hpow]
      rw [show (2 : Nat) ^ 8 = 256 by decide] at hscaled
      omega
    exact Nat.lt_of_lt_of_le hbyteTimes
      (Nat.pow_le_pow_right (by omega) hoffset)
  have hLowNat :
      (BitVec.setWidth width (BitVec.extractLsb' 0 offset value)).toNat =
        value.toNat % 2 ^ offset :=
    setWidth_extractLsb_zero_toNat width offset value (by omega)
  have hByteNat :
      (BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)).toNat =
        byte.toNat % 2 ^ 8 :=
    setWidth_extractLsb_zero_toNat width 8 byte (by omega)
  have hHighNat :
      ((value >>> (offset + 8)) <<< (offset + 8)).toNat =
        (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hhigh]
  have hLaneNat :
      ((BitVec.setWidth width (BitVec.extractLsb' 0 8 byte)) <<< offset).toNat =
        (byte.toNat % 2 ^ 8) * 2 ^ offset := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [hByteNat, Nat.mod_eq_of_lt hlane]
  have hOrLow :
      (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset =
        ((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset) := by
    calc
      _ = 2 ^ offset * (byte.toNat % 2 ^ 8) + value.toNat % 2 ^ offset := by
        rw [Nat.mul_comm]
      _ = (2 ^ offset * (byte.toNat % 2 ^ 8)) ||| (value.toNat % 2 ^ offset) :=
        Nat.two_pow_add_eq_or_of_lt hlow _
      _ = _ := by rw [Nat.mul_comm]
  have hOrAll :
      (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) =
      ((value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8)) |||
        (((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset)) := by
    calc
      _ = 2 ^ (offset + 8) * (value.toNat / 2 ^ (offset + 8)) +
          ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) := by
        rw [Nat.mul_comm]
      _ = (2 ^ (offset + 8) * (value.toNat / 2 ^ (offset + 8))) |||
          ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) :=
        Nat.two_pow_add_eq_or_of_lt hmid _
      _ = _ := by rw [Nat.mul_comm, hOrLow]
  unfold holFiniteWordSetByteBitVec
  rw [BitVec.toNat_or, BitVec.toNat_or, hHighNat, hLaneNat, hLowNat]
  calc
    _ = ((value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8)) |||
        (((byte.toNat % 2 ^ 8) * 2 ^ offset) ||| (value.toNat % 2 ^ offset)) := by
          rw [Nat.or_assoc]
    _ = (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        ((byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset) := hOrAll.symm
    _ = (value.toNat / 2 ^ (offset + 8)) * 2 ^ (offset + 8) +
        (byte.toNat % 2 ^ 8) * 2 ^ offset + value.toNat % 2 ^ offset := by omega

/-- The generic source `set_byte` model agrees with its BitVec slice form for
    every finite dimension, byte address, and endian mode. -/
theorem holFiniteWordSourceSetByte_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (address byte value : ι → Bool)
    (bigEndian : Bool) :
    holWordToBitVec dimension
        (holFiniteWordSourceSetByte dimension address byte value bigEndian) =
      holFiniteWordSetByteBitVec dimension.width
        (8 * holFiniteWordSourceByteIndex dimension address bigEndian)
        (holWordToBitVec dimension byte) (holWordToBitVec dimension value) := by
  let offset := 8 * holFiniteWordSourceByteIndex dimension address bigEndian
  have hoffset : offset =
      8 * holFiniteWordSourceByteIndex dimension address bigEndian := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  rw [holWordToBitVec_getLsbD dimension _ ⟨index, hindex⟩]
  have hvalue := holWordToBitVec_getLsbD dimension value ⟨index, hindex⟩
  simp only [holFiniteWordSourceSetByte, dimension.encode_decode]
  rw [← hoffset, ← hvalue]
  by_cases hlow : index < offset
  · have hlow8 : index < offset + 8 := by omega
    have hnotge : ¬ offset ≤ index := by omega
    simp [holFiniteWordSetByteBitVec, hlow, hlow8, hnotge, hindex]
  · by_cases hmid : index < offset + 8
    · have hge : offset ≤ index := by omega
      have hnohigh : ¬ offset + 8 ≤ index := by omega
      have hspan : index - offset < 8 := by omega
      simp [holFiniteWordSetByteBitVec, hlow, hmid, hge, hnohigh,
        hspan, hindex]
    · have hge : offset + 8 ≤ index := by omega
      have hnoByte : ¬ index - offset < 8 := by omega
      have hrestore : offset + 8 + (index - (offset + 8)) = index := by omega
      simp [holFiniteWordSetByteBitVec, hlow, hmid, hge, hnoByte,
        hindex, hrestore]

private def holFiniteWordSourceWordOfBytesAt {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (address : ι → Bool) : List (ι → Bool) → ι → Bool
  | [] => bitVecToHolWord dimension (BitVec.ofNat dimension.width 0)
  | byte :: rest =>
      holFiniteWordSourceSetByte dimension address byte
        (holFiniteWordSourceWordOfBytesAt dimension bigEndian
          (bitVecToHolWord dimension
            (holWordToBitVec dimension address + 1)) rest)
        bigEndian

def holFiniteWordSourceAligned {ι : Type u}
    (dimension : HolFiniteDimension ι) (alignment : Nat) (address : ι → Bool) :
    Bool :=
  let exponent := Nat.log2 alignment
  decide ((holWordToBitVec dimension address).toNat % (2 ^ exponent) = 0)

/-- Source-model alignment is HOL `aligned` expressed through HOL `w2n`:
    clearing `LOG2 alignment` low bits is divisibility by that power of two.
    The address conversion is the weighted-SBIT sum proved for `w2n_def`. -/
theorem holFiniteWordSourceAligned_eq_holW2N {ι : Type u}
    (dimension : HolFiniteDimension ι) (alignment : Nat)
    (address : ι → Bool) :
    holFiniteWordSourceAligned dimension alignment address =
      decide (holFiniteWordSBitSum dimension address %
        (2 ^ Nat.log2 alignment) = 0) := by
  change decide (holFiniteWordW2N dimension address %
    (2 ^ Nat.log2 alignment) = 0) = _
  rw [holFiniteWordW2N_eq_SBitSum]

/-! HOL `aligned 2` is clearing two low bits, equivalent to a natural-number
    shift round trip. This theorem records the source/HOL guard equivalence;
    `panMemLoad32HOL` uses the equivalent modulo-four form directly so its
    width-one instance does not depend on overloaded shift amounts. -/
theorem holFiniteWordSourceAligned4_eq_natShiftGuard {ι : Type u}
    (dimension : HolFiniteDimension ι) (address : ι → Bool) :
    holFiniteWordSourceAligned dimension 4 address =
      decide ((((holWordToBitVec dimension address) >>> (2 : Nat)) <<< (2 : Nat)) =
        holWordToBitVec dimension address) := by
  change decide ((holWordToBitVec dimension address).toNat %
      (2 ^ Nat.log2 4) = 0) = _
  rw [show Nat.log2 4 = 2 by decide]
  exact bitVecAligned4_decide_eq_shiftGuard (holWordToBitVec dimension address)

def holFiniteWordSourceWordOfBytes {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) : ι → Bool :=
  holFiniteWordSourceWordOfBytesAt dimension bigEndian
    (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0)) bytes

/-- The result of HOL `word_of_bytes` at its fixed `word32` width. Each source
    byte is first widened to a 32-bit word, independently of the carrier width. -/
private def holFiniteWordSourceWordOfBytesBitVecAt {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (address : ι → Bool) :
    List (BitVec dimension.width) → BitVec dimension.width
  | [] => BitVec.ofNat dimension.width 0
  | byte :: rest =>
      holFiniteWordSetByteBitVec dimension.width
        (8 * holFiniteWordSourceByteIndex dimension address bigEndian) byte
        (holFiniteWordSourceWordOfBytesBitVecAt dimension bigEndian
          (bitVecToHolWord dimension
            (holWordToBitVec dimension address + 1)) rest)

/-- Nat fold for the exact four-byte `word_of_bytes` case used by HOL
    `mem_load_32_def`. Every input is a 32-bit carrier word; the equations
    expose the four low-byte bounds before the result is lifted back to
    BitVec32. -/
private theorem holFiniteWordSourceWordOfBytesBitVecAt_four_toNat
    (bigEndian : Bool) (byte0 byte1 byte2 byte3 : BitVec 32) :
    (holFiniteWordSourceWordOfBytesBitVecAt
      (instFinHolFiniteDimension (width := 32)) bigEndian
      (bitVecToHolWord (instFinHolFiniteDimension (width := 32))
        (BitVec.ofNat 32 0)) [byte0, byte1, byte2, byte3]).toNat =
      if bigEndian then
        (byte0.toNat % 2 ^ 8) * 2 ^ 24 +
          (byte1.toNat % 2 ^ 8) * 2 ^ 16 +
          (byte2.toNat % 2 ^ 8) * 2 ^ 8 + byte3.toNat % 2 ^ 8
      else
        byte0.toNat % 2 ^ 8 +
          (byte1.toNat % 2 ^ 8) * 2 ^ 8 +
          (byte2.toNat % 2 ^ 8) * 2 ^ 16 +
          (byte3.toNat % 2 ^ 8) * 2 ^ 24 := by
  let dimension32 : HolFiniteDimension (Fin 32) :=
    instFinHolFiniteDimension (width := 32)
  have hWidth : dimension32.width = 32 := rfl
  change (holFiniteWordSourceWordOfBytesBitVecAt dimension32 bigEndian
      (bitVecToHolWord dimension32 (BitVec.ofNat 32 0))
      [byte0, byte1, byte2, byte3]).toNat = _
  have hbyte0 : byte0.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbyte1 : byte1.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbyte2 : byte2.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbyte3 : byte3.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  cases bigEndian <;>
    simp [holFiniteWordSourceWordOfBytesBitVecAt,
      holFiniteWordSourceByteIndex, dimension32,
      hWidth, holWordToBitVec_bitVecToHolWord,
      holFiniteWordSetByteBitVec_toNat, Nat.mod_eq_of_lt] <;> omega

def holFiniteWordSourceWordOfBytes32BitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) : BitVec 32 := by
  let dimension32 : HolFiniteDimension (Fin 32) :=
    instFinHolFiniteDimension (width := 32)
  let bytes32 := bytes.map fun byte =>
    BitVec.ofNat 32 ((holWordToBitVec dimension byte).toNat % 256)
  exact holFiniteWordSourceWordOfBytesBitVecAt dimension32 bigEndian
    (bitVecToHolWord dimension32 (BitVec.ofNat 32 0)) bytes32

/-- The source four-byte `word_of_bytes` fold agrees with the executable
    RISC-V fold once each input has been narrowed to its low byte. This is
    Flapjack bridge infrastructure for HOL `mem_load_32_def`, not a separate
    HOL declaration. -/
private theorem holFiniteWordSourceWordOfBytes32BitVec_four_eq_riscv
    {ι : Type u} (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (byte0 byte1 byte2 byte3 : ι → Bool) :
    holFiniteWordSourceWordOfBytes32BitVec dimension bigEndian
      [byte0, byte1, byte2, byte3] =
    RiscV.panRiscVWordOfBytes (width := 32) bigEndian
      [BitVec.ofNat 32 ((holWordToBitVec dimension byte0).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte1).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte2).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte3).toNat % 256)] := by
  let dimension32 : HolFiniteDimension (Fin 32) :=
    instFinHolFiniteDimension (width := 32)
  change holFiniteWordSourceWordOfBytesBitVecAt dimension32 bigEndian
      (bitVecToHolWord dimension32 (BitVec.ofNat 32 0))
      [BitVec.ofNat 32 ((holWordToBitVec dimension byte0).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte1).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte2).toNat % 256),
       BitVec.ofNat 32 ((holWordToBitVec dimension byte3).toNat % 256)] = _
  have hbyte0 : (holWordToBitVec dimension byte0).toNat % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have hbyte1 : (holWordToBitVec dimension byte1).toNat % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have hbyte2 : (holWordToBitVec dimension byte2).toNat % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have hbyte3 : (holWordToBitVec dimension byte3).toNat % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [holFiniteWordSourceWordOfBytesBitVecAt_four_toNat]
  cases bigEndian
  · simp [RiscV.panRiscVWordOfBytes, Option.getD_some,
      BitVec.toNat_ofNat]
    change _ = (((holWordToBitVec dimension byte0).toNat % 256 % 2 ^ 32) +
      256 * ((holWordToBitVec dimension byte1).toNat % 256 % 2 ^ 32) +
      65536 * ((holWordToBitVec dimension byte2).toNat % 256 % 2 ^ 32) +
      16777216 * ((holWordToBitVec dimension byte3).toNat % 256 % 2 ^ 32)) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte0).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte1).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte2).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte3).toNat % 256 < 2 ^ 32)]
    have hsum : (holWordToBitVec dimension byte0).toNat % 256 +
        256 * ((holWordToBitVec dimension byte1).toNat % 256) +
        65536 * ((holWordToBitVec dimension byte2).toNat % 256) +
        16777216 * ((holWordToBitVec dimension byte3).toNat % 256) < 2 ^ 32 := by
      omega
    rw [Nat.mod_eq_of_lt hsum]
    omega
  · simp [RiscV.panRiscVWordOfBytes, Option.getD_some,
      BitVec.toNat_ofNat]
    change _ = (((holWordToBitVec dimension byte3).toNat % 256 % 2 ^ 32) +
      256 * ((holWordToBitVec dimension byte2).toNat % 256 % 2 ^ 32) +
      65536 * ((holWordToBitVec dimension byte1).toNat % 256 % 2 ^ 32) +
      16777216 * ((holWordToBitVec dimension byte0).toNat % 256 % 2 ^ 32)) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte0).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte1).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte2).toNat % 256 < 2 ^ 32)]
    rw [Nat.mod_eq_of_lt (by omega :
      (holWordToBitVec dimension byte3).toNat % 256 < 2 ^ 32)]
    have hsum : (holWordToBitVec dimension byte3).toNat % 256 +
        256 * ((holWordToBitVec dimension byte2).toNat % 256) +
        65536 * ((holWordToBitVec dimension byte1).toNat % 256) +
        16777216 * ((holWordToBitVec dimension byte0).toNat % 256) < 2 ^ 32 := by
      omega
    rw [Nat.mod_eq_of_lt hsum]
    omega

/-- HOL `mem_load_32` builds `word_of_bytes` at fixed width 32 and only then
    applies `w2w` to the carrier word. -/
def holFiniteWordSourceWordOfBytes32 {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) : ι → Bool :=
  bitVecToHolWord dimension
    (BitVec.ofNat dimension.width
      (holFiniteWordSourceWordOfBytes32BitVec dimension bigEndian bytes).toNat)

/-- The generic finite-word adapter for HOL `mem_load_32` is exactly
    `word_of_bytes` at width 32 followed by `w2w` to the carrier width. This
    records the arbitrary-width projection as an operation equation, not only
    as a concrete width fixture. -/
theorem holFiniteWordSourceWordOfBytes32_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) :
    holWordToBitVec dimension
        (holFiniteWordSourceWordOfBytes32 dimension bigEndian bytes) =
      BitVec.ofNat dimension.width
        (holFiniteWordSourceWordOfBytes32BitVec dimension bigEndian bytes).toNat := by
  simp [holFiniteWordSourceWordOfBytes32,
    holWordToBitVec_bitVecToHolWord]

/-- The recursive HOL `word_of_bytes_def` model commutes with the explicit
    finite-word-to-BitVec encoding, for every byte list, address, and endian
    mode. The cons case uses the all-dimension `set_byte` slice equation. -/
theorem holFiniteWordSourceWordOfBytesAt_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (address : ι → Bool) (bytes : List (ι → Bool)) :
    holWordToBitVec dimension
        (holFiniteWordSourceWordOfBytesAt dimension bigEndian address bytes) =
      holFiniteWordSourceWordOfBytesBitVecAt dimension bigEndian address
        (bytes.map (holWordToBitVec dimension)) := by
  induction bytes generalizing address with
  | nil => simp [holFiniteWordSourceWordOfBytesAt,
      holFiniteWordSourceWordOfBytesBitVecAt,
      holWordToBitVec_bitVecToHolWord]
  | cons byte rest ih =>
      simp only [holFiniteWordSourceWordOfBytesAt,
        holFiniteWordSourceWordOfBytesBitVecAt, List.map_cons]
      rw [holFiniteWordSourceSetByte_toBitVec]
      rw [ih (address := bitVecToHolWord dimension
        (holWordToBitVec dimension address + 1))]

/-- The public source-shaped `word_of_bytes` operation has the corresponding
    BitVec recursion from address zero. -/
theorem holFiniteWordSourceWordOfBytes_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) :
    holWordToBitVec dimension
        (holFiniteWordSourceWordOfBytes dimension bigEndian bytes) =
        holFiniteWordSourceWordOfBytesBitVecAt dimension bigEndian
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0))
        (bytes.map (holWordToBitVec dimension)) := by
  change holWordToBitVec dimension
      (holFiniteWordSourceWordOfBytesAt dimension bigEndian
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0)) bytes) = _
  simpa [holWordToBitVec_bitVecToHolWord] using
    holFiniteWordSourceWordOfBytesAt_toBitVec dimension bigEndian
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0)) bytes

/-- The direct BitVec implementation used by fixed-width HOL `word_of_bytes`
    is exactly the transport of the recursive source-word definition. Keeping
    this equation explicit lets tests and production callers reduce at BitVec
    width 32 instead of repeatedly converting finite Boolean functions. -/
theorem holFiniteWordSourceWordOfBytes32BitVec_eq_source {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytes : List (ι → Bool)) :
    holFiniteWordSourceWordOfBytes32BitVec dimension bigEndian bytes =
      holWordToBitVec (instFinHolFiniteDimension (width := 32))
        (holFiniteWordSourceWordOfBytes
          (instFinHolFiniteDimension (width := 32)) bigEndian
          (bytes.map fun byte =>
            bitVecToHolWord (instFinHolFiniteDimension (width := 32))
              (BitVec.ofNat 32 ((holWordToBitVec dimension byte).toNat % 256)))) := by
  let dimension32 : HolFiniteDimension (Fin 32) :=
    instFinHolFiniteDimension (width := 32)
  change holFiniteWordSourceWordOfBytesBitVecAt dimension32 bigEndian
      (bitVecToHolWord dimension32 (BitVec.ofNat 32 0))
      (bytes.map fun byte =>
        BitVec.ofNat 32 ((holWordToBitVec dimension byte).toNat % 256)) = _
  rw [holFiniteWordSourceWordOfBytes_toBitVec]
  simp only [List.map_map]
  apply congrArg (holFiniteWordSourceWordOfBytesBitVecAt dimension32 bigEndian
    (bitVecToHolWord dimension32 (BitVec.ofNat 32 0)))
  apply List.map_congr_left
  intro byte _
  change BitVec.ofNat 32 ((holWordToBitVec dimension byte).toNat % 256) =
    holWordToBitVec dimension32
      (bitVecToHolWord dimension32
        (BitVec.ofNat 32 ((holWordToBitVec dimension byte).toNat % 256)))
  exact (holWordToBitVec_bitVecToHolWord dimension32 _).symm

def holFiniteWordSourceMemoryModel {ι : Type u}
    (dimension : HolFiniteDimension ι) (_bigEndian : Bool) :
    PanMemoryModel (ι → Bool) := by
  letI : HolFiniteDimension ι := dimension
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  exact {
    byteAlign := fun _ address => holFiniteWordSourceByteAlign dimension address
    getByte := fun _ address value be =>
      holFiniteWordSourceGetByte dimension address value be
    setByte := fun _ address byte value be =>
      holFiniteWordSourceSetByte dimension address byte value be
    aligned := fun alignment address =>
      holFiniteWordSourceAligned dimension alignment address
    wordOfBytes := fun be bytes =>
      holFiniteWordSourceWordOfBytes dimension be bytes
    wordOfBytes32 := fun be bytes =>
      holFiniteWordSourceWordOfBytes32 dimension be bytes
    /- Route the finite-word source evaluator through the reviewed HOL
       `word_op_def` port. `holFiniteWord_wordOp_toBitVec` proves this is the
       same operation as the generic carrier helper under the dimension
       representation. -/
    wordOp := fun operator values =>
      (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
        (bitVecToHolWord dimension)
    compare := fun operator left right =>
      bitVecToHolWord dimension
        (wordCmpResultHOL operator (holWordToBitVec dimension left)
          (holWordToBitVec dimension right))
    shift := fun operator left right =>
      (wordShiftHOL operator (holWordToBitVec dimension left)
        (holWordToBitVec dimension right).toNat).map
          (bitVecToHolWord dimension) }

/-- The source model routes list-valued word operations through the tagged
    HOL `word_op_def` port. This transport equation proves that changing the
    route preserves the arbitrary finite-word helper result. -/
theorem holFiniteWordSourceMemoryModel_wordOp_eq_wordOp {ι : Type u}
    [dimension : HolFiniteDimension ι] (bigEndian : Bool)
    (operator : BinOp) (values : List (ι → Bool)) :
    (holFiniteWordSourceMemoryModel dimension bigEndian).wordOp operator values =
      wordOp operator values := by
  change (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
      (bitVecToHolWord dimension) = wordOp operator values
  exact (holFiniteWord_wordOp_toBitVec dimension operator values).symm

/-- The finite-word source model's shift field is the tagged HOL `word_sh`
    definition transported through the selected finite-index/BitVec
    representation. The existing evaluator shift transport proves it agrees
    with the prior generic full-width adapter. -/
theorem holFiniteWordSourceMemoryModel_shift_eq_evalPanShiftFull {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool) (operator : Shift)
    (left right : ι → Bool) :
    (holFiniteWordSourceMemoryModel dimension bigEndian).shift operator left right =
      evalPanShiftFull operator left right := by
  change (wordShiftHOL operator (holWordToBitVec dimension left)
      (holWordToBitVec dimension right).toNat).map (bitVecToHolWord dimension) = _
  rw [holFiniteWord_evalPanShift_toBitVec dimension operator left right]
  exact congrArg (Option.map (bitVecToHolWord dimension))
    (wordShiftHOL_eq_evalPanShiftFull operator
      (holWordToBitVec dimension left) (holWordToBitVec dimension right))

/-! The source-shaped operation fields used by the recursive finite-word
    evaluator agree with the fields of the all-width RISC-V Crep runtime
    target after the explicit finite-index/BitVec conversion. This pins the
    production target binding for `Op`, `Cmp`, and `Shift`; it does not identify
    the explicit `HolFiniteDimension` with HOL's implicit `finite_index`
    dictionary or establish the surrounding whole-state correspondence. -/
theorem holFiniteWordSourceModel_ops_eq_riscvWordTarget {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (operator : BinOp) (values : List (ι → Bool))
    (crepOperator : CrepOp) (crepValues : List (ι → Bool))
    (cmp : Cmp) (shift : Shift) (left right : ι → Bool) :
    ((holFiniteWordSourceMemoryModel dimension bigEndian).wordOp operator values).map
        (holWordToBitVec dimension) =
      (RiscV.panRiscVMemoryModelForEndian bigEndian).wordOp operator
        (values.map (holWordToBitVec dimension)) ∧
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension bigEndian).compare cmp left right) =
      (RiscV.panRiscVMemoryModelForEndian bigEndian).compare cmp
        (holWordToBitVec dimension left) (holWordToBitVec dimension right) ∧
    ((holFiniteWordSourceMemoryModel dimension bigEndian).shift shift left right).map
        (holWordToBitVec dimension) =
      (RiscV.panRiscVMemoryModelForEndian bigEndian).shift shift
        (holWordToBitVec dimension left) (holWordToBitVec dimension right) ∧
    (holFiniteWordSourceCrepOp dimension crepOperator crepValues).map
        (holWordToBitVec dimension) =
      crepOpCrepWord (width := dimension.width) crepOperator
        (crepValues.map (holWordToBitVec dimension)) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  constructor
  · change ((wordOpHOL operator (values.map (holWordToBitVec dimension))).map
        (bitVecToHolWord dimension)).map (holWordToBitVec dimension) = _
    simp only [Option.map_map, Function.comp_def,
      holWordToBitVec_bitVecToHolWord]
    change Option.map id (wordOpHOL operator
      (values.map (holWordToBitVec dimension))) = _
    rw [← panRiscVWordOp_eq_wordOpHOL (width := dimension.width) operator _]
    simp only [RiscV.panRiscVMemoryModelForEndian]
    cases h : RiscV.panRiscVWordOp operator
        (values.map (holWordToBitVec dimension)) <;> simp
  constructor
  · change holWordToBitVec dimension
        (bitVecToHolWord dimension
          (wordCmpResultHOL cmp (holWordToBitVec dimension left)
            (holWordToBitVec dimension right))) = _
    simp only [holWordToBitVec_bitVecToHolWord]
    exact (panRiscVCmp_eq_wordCmpResultHOL (width := dimension.width) cmp _ _).symm
  constructor
  · change ((wordShiftHOL shift (holWordToBitVec dimension left)
        (holWordToBitVec dimension right).toNat).map
          (bitVecToHolWord dimension)).map (holWordToBitVec dimension) = _
    simp only [Option.map_map, Function.comp_def,
      holWordToBitVec_bitVecToHolWord]
    change Option.map id (wordShiftHOL shift (holWordToBitVec dimension left)
      (holWordToBitVec dimension right).toNat) = _
    rw [← panRiscVShift_eq_wordShiftHOL (width := dimension.width) shift
      (holWordToBitVec dimension left) (holWordToBitVec dimension right)]
    simp only [RiscV.panRiscVMemoryModelForEndian]
    cases h : RiscV.panRiscVShift shift (holWordToBitVec dimension left)
        (holWordToBitVec dimension right) <;> simp
  · exact holFiniteWordSourceCrepOp_to_crepOpCrepWord dimension
      crepOperator crepValues

/-- BitVec-carrier view of the HOL source memory model. Every field is
    transported from the arbitrary finite-word source operations; this does
    not replace them with RISC-V's target memory model. -/
def holFiniteWordSourceMemoryModelToBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool) :
    PanMemoryModel (BitVec dimension.width) :=
  transportPanMemoryModel (holWordToBitVec dimension)
    (bitVecToHolWord dimension)
    (holFiniteWordSourceMemoryModel dimension bigEndian)

theorem wordCmpResultHOL_eq_evalPanCmp [NeZero width]
    (operator : Cmp) (left right : BitVec width) :
    wordCmpResultHOL operator left right = evalPanCmp operator left right := by
  cases operator with
  | equal => simp [wordCmpResultHOL, wordCmpHOL, evalPanCmp]
  | less =>
      simp [wordCmpResultHOL, wordCmpHOL, evalPanCmp, PanCmp.less,
        holAsmSignedLess, RiscV.signedLess]
  | lower =>
      simp only [wordCmpResultHOL, wordCmpHOL, evalPanCmp, PanCmp.lower]
      rfl
  | test => simp [wordCmpResultHOL, wordCmpHOL, evalPanCmp]
  | notEqual => simp [wordCmpResultHOL, wordCmpHOL, evalPanCmp]
  | notLess =>
      have hless : holAsmSignedLess left right = RiscV.signedLess left right := rfl
      simp only [wordCmpResultHOL, wordCmpHOL, evalPanCmp, PanCmp.less, hless]
      by_cases h : RiscV.signedLess left right = true <;> simp [h]
  | notLower =>
      simp only [wordCmpResultHOL, wordCmpHOL, evalPanCmp, PanCmp.lower]
      by_cases h : decide (left < right) = true <;> simp [h]
  | notTest => simp [wordCmpResultHOL, wordCmpHOL, evalPanCmp]

/-- The `setByte` field of the generic source memory model transports to its
    explicit BitVec slice operation. -/
theorem holFiniteWordSourceMemoryModel_setByte_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (address byte value : ι → Bool) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension modelEndian).setByte
          (bitVecToHolWord dimension (BitVec.ofNat dimension.width
            (dimension.width / 8))) address byte value bigEndian) =
      holFiniteWordSetByteBitVec dimension.width
        (8 * holFiniteWordSourceByteIndex dimension address bigEndian)
        (holWordToBitVec dimension byte) (holWordToBitVec dimension value) := by
  change holWordToBitVec dimension
      (holFiniteWordSourceSetByte dimension address byte value bigEndian) = _
  exact holFiniteWordSourceSetByte_toBitVec dimension address byte value bigEndian

/-- The `wordOfBytes` field transports to the explicit recursive BitVec
    implementation matching HOL `word_of_bytes_def`. -/
theorem holFiniteWordSourceMemoryModel_wordOfBytes_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (bytes : List (ι → Bool)) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension modelEndian).wordOfBytes
          bigEndian bytes) =
      holFiniteWordSourceWordOfBytesBitVecAt dimension bigEndian
        (bitVecToHolWord dimension (BitVec.ofNat dimension.width 0))
        (bytes.map (holWordToBitVec dimension)) := by
  change holWordToBitVec dimension
      (holFiniteWordSourceWordOfBytes dimension bigEndian bytes) = _
  exact holFiniteWordSourceWordOfBytes_toBitVec dimension bigEndian bytes

/-- The source memory model's fixed-width load decoder transports to the
    explicit 32-bit `word_of_bytes` result followed by carrier-width `w2w`. -/
theorem holFiniteWordSourceMemoryModel_wordOfBytes32_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (bytes : List (ι → Bool)) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension modelEndian).wordOfBytes32
          bigEndian bytes) =
      BitVec.ofNat dimension.width
        (holFiniteWordSourceWordOfBytes32BitVec dimension bigEndian bytes).toNat := by
  change holWordToBitVec dimension
      (holFiniteWordSourceWordOfBytes32 dimension bigEndian bytes) = _
  exact holFiniteWordSourceWordOfBytes32_toBitVec dimension bigEndian bytes

/-- Four-byte source-model `wordOfBytes32` agrees with the exact RISC-V
    `word_of_bytes` fold after narrowing each source word to its low byte.
    This is the packing step needed to compare the source `mem_load_32`
    equation with the production `panMemLoad32HOL` result. -/
theorem holFiniteWordSourceMemoryModel_wordOfBytes32_four_eq_riscv
    {ι : Type u} (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (byte0 byte1 byte2 byte3 : ι → Bool) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension modelEndian).wordOfBytes32
          bigEndian [byte0, byte1, byte2, byte3]) =
      BitVec.ofNat dimension.width
        (RiscV.panRiscVWordOfBytes (width := 32) bigEndian
          [BitVec.ofNat 32 ((holWordToBitVec dimension byte0).toNat % 256),
           BitVec.ofNat 32 ((holWordToBitVec dimension byte1).toNat % 256),
           BitVec.ofNat 32 ((holWordToBitVec dimension byte2).toNat % 256),
           BitVec.ofNat 32 ((holWordToBitVec dimension byte3).toNat % 256)]).toNat := by
  rw [holFiniteWordSourceMemoryModel_wordOfBytes32_toBitVec]
  rw [holFiniteWordSourceWordOfBytes32BitVec_four_eq_riscv]

/-- The model-level form of `byte_align_def` for the source-shaped load
    adapter. The unused byte-count argument reflects that HOL's
    `byte_align` derives alignment from the word dimension itself. -/
theorem holFiniteWordSourceMemoryModel_byteAlign_toBitVec {ι : Type u}
    [dimension : HolFiniteDimension ι] (bigEndian : Bool)
    (bytes address : ι → Bool) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension bigEndian).byteAlign
          bytes address) =
      holByteAlignBitVec (holWordToBitVec dimension address) := by
  change holWordToBitVec dimension
      (holFiniteWordSourceByteAlign dimension address) = _
  exact holFiniteWordSourceByteAlign_toBitVec dimension address

/-- The generic source memory model's `getByte` field has the same BitVec
    pointwise extraction equation as the HOL `get_byte` formula. -/
theorem holFiniteWordSourceMemoryModel_getByte_toBitVec_getLsbD {ι : Type u}
    (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (bytes address value : ι → Bool) (index : Fin dimension.width) :
    BitVec.getLsbD
        (holWordToBitVec dimension
          ((holFiniteWordSourceMemoryModel dimension modelEndian).getByte
            bytes address value bigEndian)) index.val =
      (decide (index.val < 8) &&
        BitVec.getLsbD
          (holWordToBitVec dimension value >>>
            (8 * holFiniteWordSourceByteIndex dimension address bigEndian))
          index.val) := by
  change BitVec.getLsbD
      (holWordToBitVec dimension
        (holFiniteWordSourceGetByte dimension address value bigEndian)) index.val = _
  exact holFiniteWordSourceGetByte_toBitVec_getLsbD
    dimension address value bigEndian index

/-- The generic source memory model's `getByte` field transports as the
    carrier-width `w2w` of the low byte of the shifted source word. -/
theorem holFiniteWordSourceMemoryModel_getByte_toBitVec {ι : Type u}
    (dimension : HolFiniteDimension ι) (modelEndian bigEndian : Bool)
    (bytes address value : ι → Bool) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension modelEndian).getByte
          bytes address value bigEndian) =
      BitVec.ofNat dimension.width
        ((holWordToBitVec dimension value >>>
          (8 * holFiniteWordSourceByteIndex dimension address bigEndian)).toNat %
            2^8) := by
  change holWordToBitVec dimension
      (holFiniteWordSourceGetByte dimension address value bigEndian) = _
  exact holFiniteWordSourceGetByte_toBitVec dimension address value bigEndian

/-- The explicit finite-word source-model byte extraction transports to the
    exact width-indexed `panGetByteHOL` formula, including HOL's MOD-zero
    indexing below one byte. -/
theorem holFiniteWordSourceMemoryModel_getByte_eq_panGetByteHOL {ι : Type u}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (address value : BitVec dimension.width) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension bigEndian).getByte
          (bitVecToHolWord dimension
            (BitVec.ofNat dimension.width (dimension.width / 8)))
          (bitVecToHolWord dimension address)
          (bitVecToHolWord dimension value) bigEndian) =
      BitVec.ofNat dimension.width
        (panGetByteHOL address value bigEndian).toNat := by
  rw [holFiniteWordSourceMemoryModel_getByte_toBitVec]
  have hidx :
      (if dimension.width < 8 then address.toNat
       else address.toNat % (dimension.width / 8)) =
        address.toNat % (dimension.width / 8) := by
    by_cases hwidth : dimension.width < 8
    · have hbytes : dimension.width / 8 = 0 := by omega
      simp [hwidth, hbytes]
    · simp [hwidth]
  simp [panGetByteHOL, holFiniteWordSourceByteIndex,
    holWordToBitVec_bitVecToHolWord, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul, hidx]

/-- The source-shaped finite-word model comparison agrees with the generic
    BitVec/HOL comparison after transporting the operands. -/
theorem holFiniteWordSourceMemoryModel_compare_toBitVec {ι : Type u}
    [dimension : HolFiniteDimension ι] (bigEndian : Bool)
    (operator : Cmp) (left right : ι → Bool) :
    holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension bigEndian).compare
          operator left right) =
      RiscV.panRiscVCmp operator (holWordToBitVec dimension left)
        (holWordToBitVec dimension right) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (wordCmpResultHOL operator (holWordToBitVec dimension left)
        (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord, wordCmpResultHOL_eq_evalPanCmp]
  exact (panRiscVCmp_eq_evalPanCmp operator _ _).symm

/-- A load model with HOL's dimension-derived byte alignment and the existing
    RISC-V byte extraction, alignment, and word-of-bytes operations. This is
    only the first operation-level bridge: the remaining imported word
    primitives still require a generic correspondence proof. -/
def holByteAlignedRiscVMemoryModel [NeZero width] (bigEndian : Bool) :
    PanMemoryModel (RiscV.Word width) :=
  let model := RiscV.panRiscVMemoryModelForEndian bigEndian
  { model with byteAlign := fun _ address => holByteAlignBitVec address }

def CrepHolState.toHolFiniteBitVecState {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepHolState (RiscV.Word dimension.width) σ :=
  { locals := fun name => (state.locals name).map
      (mapCrepHolWordLab (holWordToBitVec dimension))
    globals := fun name => (state.globals name).map
      (mapCrepHolWordLab (holWordToBitVec dimension))
    code := fun _ => none
    memory := fun address => mapCrepHolWordLab (holWordToBitVec dimension)
      (state.memory (bitVecToHolWord dimension address))
    memaddrs := fun address => state.memaddrs (bitVecToHolWord dimension address)
    shMemaddrs := fun address => state.shMemaddrs (bitVecToHolWord dimension address)
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := holWordToBitVec dimension state.baseAddress
    topAddress := holWordToBitVec dimension state.topAddress }

def CrepHolState.toHolFiniteWordRuntime {ι : Type u}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepRuntimeState (ι → Bool) σ :=
  { locals := state.locals
    globals := state.globals
    code := state.code
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    memoryModel := holFiniteWordRiscVMemoryModel dimension state.bigEndian
    bytesInWord := bitVecToHolWord dimension
      (BitVec.ofNat dimension.width (dimension.width / 8))
    ffiContext := crepHolEvalFfiContext
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

/-- Runtime adapter for proofs that need HOL's generic finite-word byte-load
    primitives. It retains the state fields and word-size value of
    `toHolFiniteWordRuntime` while selecting the source-shaped memory model.
    The all-width untagged recursive simp-preservation theorem uses this
    runtime, and the load branches are connected to the model-parametric HOL
    source helpers below. Other target primitives remain transported through
    BitVec/RISC-V; their HOL correspondence is still open. -/
def CrepHolState.toHolFiniteWordSourceRuntime {ι : Type u}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepRuntimeState (ι → Bool) σ :=
  let runtime := state.toHolFiniteWordRuntime dimension
  { runtime with
    memoryModel := holFiniteWordSourceMemoryModel dimension state.bigEndian }

/-- The generic finite-word production adapter projects back to exactly the
    eleven fields of HOL `crepSem$state`. The explicit `HolFiniteDimension`
    witness chooses word operations and byte semantics, but does not alter the
    represented HOL state. This closes the state-record part of the evaluator
    correspondence; the source word-operation correspondence remains open. -/
theorem CrepHolState.toHolState_toHolFiniteWordSourceRuntime {ι : Type u}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ) :
    (state.toHolFiniteWordSourceRuntime dimension).toHolState = state := by
  rfl

/-! The production byte/word load branches over the source-shaped runtime
    reduce to the model-parametric state helpers that spell out HOL's
    `mem_load_byte_def` and `mem_load_32_def`. These equations connect the
    production evaluator path to those source formulas; they do not assert
    that the finite-dimension BitVec encoding is HOL's implicit `finite_index`
    representation. -/
theorem crepHolFiniteWordSourceRuntime_loadByte {ι : Type u} {σ : Type u}
    [dimension : HolFiniteDimension ι]
    (state : CrepHolState (ι → Bool) σ) (address : ι → Bool) :
    crepRuntimeLoadByte (state.toHolFiniteWordSourceRuntime dimension) address =
      crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel dimension state.bigEndian)
        (bitVecToHolWord dimension
          (BitVec.ofNat dimension.width (dimension.width / 8)))
        state address := by
  cases hcell : state.memory
      ((holFiniteWordSourceMemoryModel dimension state.bigEndian).byteAlign
        (bitVecToHolWord dimension
          (BitVec.ofNat dimension.width (dimension.width / 8))) address) with
  | word value =>
      simp [CrepHolState.toHolFiniteWordSourceRuntime,
        CrepHolState.toHolFiniteWordRuntime, crepRuntimeLoadByte,
        crepHolEvalMemLoadByte, hcell, panTheWord]

theorem crepHolFiniteWordSourceRuntime_load32 {ι : Type u} {σ : Type u}
    [dimension : HolFiniteDimension ι]
    (state : CrepHolState (ι → Bool) σ) (address : ι → Bool) :
    crepRuntimeLoad32 (state.toHolFiniteWordSourceRuntime dimension) address =
      crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel dimension state.bigEndian)
        (bitVecToHolWord dimension
          (BitVec.ofNat dimension.width (dimension.width / 8)))
        state address := by
  have hWordToBitVecInjective : Function.Injective (holWordToBitVec dimension) := by
    intro left right h
    calc
      left = bitVecToHolWord dimension (holWordToBitVec dimension left) := by
        rw [bitVecToHolWord_holWordToBitVec]
      _ = bitVecToHolWord dimension (holWordToBitVec dimension right) :=
        congrArg (bitVecToHolWord dimension) h
      _ = right := bitVecToHolWord_holWordToBitVec dimension right
  have hTwo : holWordToBitVec dimension (2 : ι → Bool) =
      BitVec.ofNat dimension.width 2 := by
    change holWordToBitVec dimension
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width 2)) = _
    rw [holWordToBitVec_bitVecToHolWord]
  have hThree : holWordToBitVec dimension (3 : ι → Bool) =
      BitVec.ofNat dimension.width 3 := by
    change holWordToBitVec dimension
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width 3)) = _
    rw [holWordToBitVec_bitVecToHolWord]
  have hBits12 : BitVec.ofNat dimension.width 1 +
      BitVec.ofNat dimension.width 1 = BitVec.ofNat dimension.width 2 := by
    change BitVec.ofNat dimension.width 1 + BitVec.ofNat dimension.width 1 =
      BitVec.ofNat dimension.width (1 + 1)
    rw [BitVec.ofNat_add_ofNat]
  have hBits23 : BitVec.ofNat dimension.width 2 +
      BitVec.ofNat dimension.width 1 = BitVec.ofNat dimension.width 3 := by
    change BitVec.ofNat dimension.width 2 + BitVec.ofNat dimension.width 1 =
      BitVec.ofNat dimension.width (2 + 1)
    rw [BitVec.ofNat_add_ofNat]
  have hAddress2 : address + 1 + 1 = address + 2 := by
    apply hWordToBitVecInjective
    simp only [holFiniteWordToBitVec_add]
    rw [holFiniteWordToBitVec_one, hTwo]
    calc
      (holWordToBitVec dimension address + BitVec.ofNat dimension.width 1) +
          BitVec.ofNat dimension.width 1 =
          holWordToBitVec dimension address +
            (BitVec.ofNat dimension.width 1 + BitVec.ofNat dimension.width 1) :=
        BitVec.add_assoc _ _ _
      _ = holWordToBitVec dimension address + BitVec.ofNat dimension.width 2 :=
        congrArg (fun word => holWordToBitVec dimension address + word) hBits12
  have hAddress3 : address + 1 + 1 + 1 = address + 2 + 1 := by
    exact congrArg (fun value => value + 1) hAddress2
  have hAddress23 : address + 2 + 1 = address + 3 := by
    apply hWordToBitVecInjective
    simp only [holFiniteWordToBitVec_add]
    rw [hTwo, holFiniteWordToBitVec_one, hThree]
    calc
      (holWordToBitVec dimension address + BitVec.ofNat dimension.width 2) +
          BitVec.ofNat dimension.width 1 =
          holWordToBitVec dimension address +
            (BitVec.ofNat dimension.width 2 + BitVec.ofNat dimension.width 1) :=
        BitVec.add_assoc _ _ _
      _ = holWordToBitVec dimension address + BitVec.ofNat dimension.width 3 :=
        congrArg (fun word => holWordToBitVec dimension address + word) hBits23
  by_cases haligned :
      (holFiniteWordSourceMemoryModel dimension state.bigEndian).aligned 4 address = true
  · let alignedAddress :=
      (holFiniteWordSourceMemoryModel dimension state.bigEndian).byteAlign
        (bitVecToHolWord dimension
          (BitVec.ofNat dimension.width (dimension.width / 8))) address
    cases hcell : state.memory alignedAddress with
    | word value =>
        simp [CrepHolState.toHolFiniteWordSourceRuntime,
          CrepHolState.toHolFiniteWordRuntime, crepRuntimeLoad32,
          crepHolEvalMemLoad32, alignedAddress, haligned, hcell, panTheWord,
          hAddress2, hAddress23]
  · simp [CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime, crepRuntimeLoad32,
      crepHolEvalMemLoad32, haligned]

/-- The model-parametric HOL byte-load helper commutes with the explicit
    finite-word/BitVec state conversion when the BitVec memory model is the
    transported source model. -/
theorem crepHolEvalMemLoadByte_source_toBitVec {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytesInWord : ι → Bool) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel dimension bigEndian) bytesInWord
        state address =
      (crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian)
        (holWordToBitVec dimension bytesInWord)
        (CrepHolState.toHolFiniteBitVecState dimension state)
        (holWordToBitVec dimension address)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  cases hcell : state.memory
      ((holFiniteWordSourceMemoryModel dimension bigEndian).byteAlign
        bytesInWord address) with
  | word value =>
      simp [crepHolEvalMemLoadByte, holFiniteWordSourceMemoryModelToBitVec,
        transportPanMemoryModel, CrepHolState.toHolFiniteBitVecState,
        mapCrepHolWordLab, hcell, bitVecToHolWord_holWordToBitVec]

/-- The production finite-word source byte-load equation is the tagged HOL
    `mem_load_byte_def` port after the explicit finite-index/BitVec state
    transport. This is an all-width operation bridge; it does not by itself
    establish the whole `crepSem$eval_def` state correspondence. -/
theorem crepHolEvalMemLoadByte_source_eq_panMemLoadByteHOL {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytesInWord : ι → Bool) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    (crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel dimension bigEndian) bytesInWord
        state address).map (holWordToBitVec dimension) =
      (panMemLoadByteHOL
        (fun bitAddress =>
          ((CrepHolState.toHolFiniteBitVecState dimension state).memory
            bitAddress).toHolWordLab)
        (fun bitAddress =>
          (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
            bitAddress = true)
        state.bigEndian (holWordToBitVec dimension address)).map
          (fun byte => BitVec.ofNat dimension.width byte.toNat) := by
  let bitState := CrepHolState.toHolFiniteBitVecState dimension state
  let bitAddress := holWordToBitVec dimension address
  let bitBytes := holWordToBitVec dimension bytesInWord
  have htransport := crepHolEvalMemLoadByte_source_toBitVec dimension
    bigEndian bytesInWord state address
  have hbyteAlign :
      (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian).byteAlign
          bitBytes bitAddress = holByteAlignBitVec bitAddress := by
    letI : HolFiniteDimension ι := dimension
    have h := @holFiniteWordSourceMemoryModel_byteAlign_toBitVec ι dimension
      bigEndian (bitVecToHolWord dimension bitBytes)
      (bitVecToHolWord dimension bitAddress)
    simpa [holFiniteWordSourceMemoryModelToBitVec, transportPanMemoryModel,
      bitBytes, bitAddress, holWordToBitVec_bitVecToHolWord] using h
  have hgetByte (value : BitVec dimension.width) :
      (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian).getByte
          bitBytes bitAddress value state.bigEndian =
          BitVec.ofNat dimension.width
            (panGetByteHOL bitAddress value state.bigEndian).toNat := by
    letI : HolFiniteDimension ι := dimension
    have h := holFiniteWordSourceMemoryModel_getByte_eq_panGetByteHOL
      dimension state.bigEndian bitAddress value
    change holWordToBitVec dimension
      ((holFiniteWordSourceMemoryModel dimension bigEndian).getByte
        (bitVecToHolWord dimension
          (BitVec.ofNat dimension.width (dimension.width / 8)))
        (bitVecToHolWord dimension bitAddress)
        (bitVecToHolWord dimension value) state.bigEndian) = _
    exact h
  have hmapTransport := congrArg
    (Option.map (holWordToBitVec dimension)) htransport
  calc
    (crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel dimension bigEndian) bytesInWord
        state address).map (holWordToBitVec dimension) =
      ((crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian) bitBytes
        bitState bitAddress).map (bitVecToHolWord dimension)).map
          (holWordToBitVec dimension) := hmapTransport
    _ = crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian) bitBytes
        bitState bitAddress := by
          simp only [Option.map_map, Function.comp_def,
            holWordToBitVec_bitVecToHolWord]
          cases hresult : crepHolEvalMemLoadByte
              (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian)
              bitBytes bitState bitAddress <;> rfl
    _ = (panMemLoadByteHOL
        (fun current => (bitState.memory current).toHolWordLab)
        (fun current => bitState.memaddrs current = true)
        state.bigEndian bitAddress).map
          (fun byte => BitVec.ofNat dimension.width byte.toNat) := by
          unfold crepHolEvalMemLoadByte panMemLoadByteHOL
          rw [hbyteAlign]
          have halign : holByteAlignBitVec bitAddress =
              panByteAlignHOL bitAddress := by
            simp [holByteAlignBitVec, panByteAlignHOL]
          rw [← halign]
          cases hcell : bitState.memory (holByteAlignBitVec bitAddress) with
          | word value =>
              by_cases hdomain : bitState.memaddrs (holByteAlignBitVec bitAddress) = true
              · have hendian : bitState.bigEndian = state.bigEndian := rfl
                simp [hcell, hdomain, hgetByte, hendian, PanWordLab.toHolWordLab]
              · simp [hdomain]

/-- The model-parametric HOL word-load helper commutes with the explicit
    finite-word/BitVec state conversion, including alignment, all four byte
    addresses, and recursive `word_of_bytes`. -/
theorem crepHolEvalMemLoad32_source_toBitVec {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι) (bigEndian : Bool)
    (bytesInWord : ι → Bool) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel dimension bigEndian) bytesInWord
        state address =
      (crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModelToBitVec dimension bigEndian)
        (holWordToBitVec dimension bytesInWord)
        (CrepHolState.toHolFiniteBitVecState dimension state)
        (holWordToBitVec dimension address)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  have hTwo : holWordToBitVec dimension (2 : ι → Bool) =
      BitVec.ofNat dimension.width 2 := by
    change holWordToBitVec dimension
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width 2)) = _
    rw [holWordToBitVec_bitVecToHolWord]
  have hThree : holWordToBitVec dimension (3 : ι → Bool) =
      BitVec.ofNat dimension.width 3 := by
    change holWordToBitVec dimension
      (bitVecToHolWord dimension (BitVec.ofNat dimension.width 3)) = _
    rw [holWordToBitVec_bitVecToHolWord]
  have hBits12 : BitVec.ofNat dimension.width 1 +
      BitVec.ofNat dimension.width 1 = BitVec.ofNat dimension.width 2 := by
    change BitVec.ofNat dimension.width 1 + BitVec.ofNat dimension.width 1 =
      BitVec.ofNat dimension.width (1 + 1)
    rw [BitVec.ofNat_add_ofNat]
  have hBits23 : BitVec.ofNat dimension.width 2 +
      BitVec.ofNat dimension.width 1 = BitVec.ofNat dimension.width 3 := by
    change BitVec.ofNat dimension.width 2 + BitVec.ofNat dimension.width 1 =
      BitVec.ofNat dimension.width (2 + 1)
    rw [BitVec.ofNat_add_ofNat]
  have hWordToBitVecInjective : Function.Injective (holWordToBitVec dimension) := by
    intro left right h
    calc
      left = bitVecToHolWord dimension (holWordToBitVec dimension left) := by
        rw [bitVecToHolWord_holWordToBitVec]
      _ = bitVecToHolWord dimension (holWordToBitVec dimension right) :=
        congrArg (bitVecToHolWord dimension) h
      _ = right := bitVecToHolWord_holWordToBitVec dimension right
  have hAddress1 : bitVecToHolWord dimension
      (holWordToBitVec dimension address + BitVec.ofNat dimension.width 1) =
        address + 1 := by
    apply hWordToBitVecInjective
    rw [holWordToBitVec_bitVecToHolWord, holFiniteWordToBitVec_add,
      holFiniteWordToBitVec_one]
    change holWordToBitVec dimension address + 1 =
      holWordToBitVec dimension address + 1
    rfl
  have hAddress2 : bitVecToHolWord dimension
      (holWordToBitVec dimension address + BitVec.ofNat dimension.width 2) =
        address + 2 := by
    apply hWordToBitVecInjective
    rw [holWordToBitVec_bitVecToHolWord, holFiniteWordToBitVec_add, hTwo]
  have hAddress3 : bitVecToHolWord dimension
      (holWordToBitVec dimension address + BitVec.ofNat dimension.width 3) =
        address + 3 := by
    apply hWordToBitVecInjective
    rw [holWordToBitVec_bitVecToHolWord, holFiniteWordToBitVec_add, hThree]
  by_cases haligned :
      (holFiniteWordSourceMemoryModel dimension bigEndian).aligned 4 address = true
  · let alignedAddress :=
      (holFiniteWordSourceMemoryModel dimension bigEndian).byteAlign
        bytesInWord address
    cases hcell : state.memory alignedAddress with
    | word value =>
        simp [crepHolEvalMemLoad32, holFiniteWordSourceMemoryModelToBitVec,
          transportPanMemoryModel, CrepHolState.toHolFiniteBitVecState,
          mapCrepHolWordLab, alignedAddress, haligned, hcell,
          hAddress1, hAddress2, hAddress3,
          bitVecToHolWord_holWordToBitVec]
  · simp [crepHolEvalMemLoad32, holFiniteWordSourceMemoryModelToBitVec,
      transportPanMemoryModel, haligned,
      bitVecToHolWord_holWordToBitVec]

/-! The arbitrary finite-word source `mem_load_32` helper is the tagged HOL
    `panMemLoad32HOL` definition after transporting the explicit finite-index
    carrier to `BitVec`, including the final `w2w` from `word32` back to the
    expression word width. This closes the Load32 primitive relation; it does
    not by itself identify the whole source evaluator with native HOL `eval`.
    It is Flapjack adapter infrastructure, not an independent HOL declaration,
    and therefore carries no `@[hol]` tag. -/
theorem crepHolEvalMemLoad32_source_eq_panMemLoad32HOL {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (bytesInWord : ι → Bool) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    (crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel dimension state.bigEndian) bytesInWord
        state address).map (holWordToBitVec dimension) =
      (panMemLoad32HOL
        (fun bitAddress =>
          ((CrepHolState.toHolFiniteBitVecState dimension state).memory
            bitAddress).toHolWordLab)
        (fun bitAddress =>
          (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
            bitAddress = true)
        state.bigEndian (holWordToBitVec dimension address)).map
          (fun value => BitVec.ofNat dimension.width value.toNat) := by
  let bitState := CrepHolState.toHolFiniteBitVecState dimension state
  let bitAddress := holWordToBitVec dimension address
  let bitBytes := holWordToBitVec dimension bytesInWord
  let bitModel := holFiniteWordSourceMemoryModelToBitVec dimension state.bigEndian
  have htransport := crepHolEvalMemLoad32_source_toBitVec dimension
    state.bigEndian bytesInWord state address
  have hbyteAlign : bitModel.byteAlign bitBytes bitAddress =
      panByteAlignHOL bitAddress := by
    letI : HolFiniteDimension ι := dimension
    have h := @holFiniteWordSourceMemoryModel_byteAlign_toBitVec ι dimension
      state.bigEndian (bitVecToHolWord dimension bitBytes)
      (bitVecToHolWord dimension bitAddress)
    simpa [bitModel, holFiniteWordSourceMemoryModelToBitVec,
      transportPanMemoryModel, bitBytes, bitAddress,
      holWordToBitVec_bitVecToHolWord, holByteAlignBitVec, panByteAlignHOL]
      using h
  have hgetByte (current value : BitVec dimension.width) :
      bitModel.getByte bitBytes current value state.bigEndian =
        BitVec.ofNat dimension.width (panGetByteHOL current value state.bigEndian).toNat := by
    letI : HolFiniteDimension ι := dimension
    change holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension state.bigEndian).getByte
          (bitVecToHolWord dimension bitBytes)
          (bitVecToHolWord dimension current)
          (bitVecToHolWord dimension value) state.bigEndian) = _
    exact holFiniteWordSourceMemoryModel_getByte_eq_panGetByteHOL
      dimension state.bigEndian current value
  have hwordOfBytes32 (byte0 byte1 byte2 byte3 : BitVec dimension.width) :
      bitModel.wordOfBytes32 state.bigEndian [byte0, byte1, byte2, byte3] =
        BitVec.ofNat dimension.width
          (RiscV.panRiscVWordOfBytes (width := 32) state.bigEndian
            [BitVec.ofNat 32 (byte0.toNat % 256),
             BitVec.ofNat 32 (byte1.toNat % 256),
             BitVec.ofNat 32 (byte2.toNat % 256),
             BitVec.ofNat 32 (byte3.toNat % 256)]).toNat := by
    letI : HolFiniteDimension ι := dimension
    change holWordToBitVec dimension
        ((holFiniteWordSourceMemoryModel dimension state.bigEndian).wordOfBytes32
          state.bigEndian
            [bitVecToHolWord dimension byte0, bitVecToHolWord dimension byte1,
             bitVecToHolWord dimension byte2, bitVecToHolWord dimension byte3]) = _
    simpa only [holWordToBitVec_bitVecToHolWord] using
      (holFiniteWordSourceMemoryModel_wordOfBytes32_four_eq_riscv
      dimension state.bigEndian state.bigEndian
      (bitVecToHolWord dimension byte0) (bitVecToHolWord dimension byte1)
      (bitVecToHolWord dimension byte2) (bitVecToHolWord dimension byte3)
      )
  have hAligned : bitModel.aligned 4 bitAddress =
      decide (bitAddress.toNat % 4 = 0) := by
    change holFiniteWordSourceAligned dimension 4
        (bitVecToHolWord dimension bitAddress) = _
    unfold holFiniteWordSourceAligned
    rw [holWordToBitVec_bitVecToHolWord]
    rw [show Nat.log2 4 = 2 by decide]
  have hByteLane (byte : UInt8) :
      BitVec.ofNat 32 ((BitVec.ofNat dimension.width byte.toNat).toNat % 256) =
        BitVec.setWidth 32 (BitVec.ofNat dimension.width byte.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have hbyte : byte.toNat < 256 := byte.toNat_lt
    by_cases hwidth : dimension.width < 8
    · have hpow : 2 ^ dimension.width ≤ 256 := by
        calc
          2 ^ dimension.width ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 256 := by decide
      have hsmall : byte.toNat % 2 ^ dimension.width < 256 :=
        Nat.lt_of_lt_of_le
          (Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))) hpow
      rw [Nat.mod_eq_of_lt hsmall]
    · have hpow : 256 ≤ 2 ^ dimension.width := by
        calc
          256 = 2 ^ 8 := by decide
          _ ≤ 2 ^ dimension.width := Nat.pow_le_pow_right (by decide) (by omega)
      have hkeep : byte.toNat % 2 ^ dimension.width = byte.toNat :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hbyte hpow)
      rw [hkeep, Nat.mod_eq_of_lt hbyte]
  have hBitLoad :
      crepHolEvalMemLoad32 bitModel bitBytes bitState bitAddress =
        (panMemLoad32HOL
          (fun current => (bitState.memory current).toHolWordLab)
          (fun current => bitState.memaddrs current = true)
          state.bigEndian bitAddress).map
            (fun value => BitVec.ofNat dimension.width value.toNat) := by
    unfold crepHolEvalMemLoad32 panMemLoad32HOL
    by_cases haligned : bitAddress.toNat % 4 = 0
    · simp only [hAligned, haligned, decide_true, ↓reduceIte]
      rw [hbyteAlign]
      cases hcell : bitState.memory (panByteAlignHOL bitAddress) with
      | word value =>
          by_cases hdomain : bitState.memaddrs (panByteAlignHOL bitAddress) = true
          · simp [hcell, hdomain, PanWordLab.toHolWordLab]
            rw [show bitState.bigEndian = state.bigEndian by rfl]
            rw [hwordOfBytes32]
            simp only [hgetByte]
            rw [hByteLane, hByteLane, hByteLane, hByteLane]
            rw [BitVec.ofNat_toNat]
          · simp [hdomain]
    · simp [hAligned, haligned]
  calc
    (crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel dimension state.bigEndian) bytesInWord
        state address).map (holWordToBitVec dimension) =
      ((crepHolEvalMemLoad32 bitModel bitBytes bitState bitAddress).map
        (bitVecToHolWord dimension)).map (holWordToBitVec dimension) := by
          rw [htransport]
    _ = crepHolEvalMemLoad32 bitModel bitBytes bitState bitAddress := by
      simp [Option.map_map, Function.comp_def,
        holWordToBitVec_bitVecToHolWord]
    _ = (panMemLoad32HOL
        (fun current => (bitState.memory current).toHolWordLab)
        (fun current => bitState.memaddrs current = true)
        state.bigEndian bitAddress).map
          (fun value => BitVec.ofNat dimension.width value.toNat) := hBitLoad

/-! At the shipped RV64 configuration, the executed target byte-load helper
    also reduces to the same tagged HOL operation. This equation is stated on
    the explicit `CrepHolState` carrier and preserves both success and domain
    failure without assuming a successful target result. -/

theorem crepHolEvalMemLoadByte_riscv64_eq_panMemLoadByteHOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat 64 byte.toNat) := by
  simp only [crepHolEvalMemLoadByte, panMemLoadByteHOL,
    RiscV.panRiscVMemoryModelForEndian]
  have haligned : RiscV.panRiscVByteAlign (8 : BitVec 64) address =
      panByteAlignHOL address := by
    have hprod := RiscV.panRiscVByteAlign_eight_eq_bitMask address
    have hhol : panByteAlignHOL address =
        BitVec.ofNat 64 ((address.toNat >>> 3) <<< 3) := by
      simp [panByteAlignHOL, show Nat.log2 (64 / 8) = 3 by decide,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact hprod.trans hhol.symm
  simp only [haligned]
  cases hcell : state.memory (panByteAlignHOL address) with
  | word value =>
      by_cases hdomain : state.memaddrs (panByteAlignHOL address) = true
      · simp only [hcell, PanWordLab.toHolWordLab, hdomain,
          ↓reduceIte, Option.map_some]
        have hbyte := panGetByteHOL_eq_panRiscVGetByteEndian
          address value state.bigEndian
        have hlt := panRiscVGetByteEndian_toNat_lt_256
          address value state.bigEndian
        rw [hbyte]
        apply congrArg some
        let byte := RiscV.panRiscVGetByteEndian (8 : BitVec 64)
          address value state.bigEndian
        have hbyteVal : (UInt8.ofNat byte.toNat).toNat = byte.toNat :=
          UInt8.toNat_ofNat_of_lt hlt
        change byte = BitVec.ofNat 64 (UInt8.ofNat byte.toNat).toNat
        rw [hbyteVal]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (by omega : byte.toNat < 2 ^ 64)).symm
      · simp [hdomain]

theorem crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun byte => BitVec.ofNat 64 byte.toNat) := by
  calc
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : BitVec 64) address state.bigEndian :=
          crepRuntimeLoadByte_wordTarget_eq_riscv state.toRuntime address
    _ = panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian := rfl
    _ = crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address := by
          symm
          exact crepHolEvalMemLoadByte_eq_panModelReadByte _ _ _ _
    _ = (panMemLoadByteHOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun byte => BitVec.ofNat 64 byte.toNat) :=
            crepHolEvalMemLoadByte_riscv64_eq_panMemLoadByteHOL state address

theorem crepHolEvalMemLoadByte_source_eq_riscv64 {σ : Type}
    (state : CrepHolState (Fin 64 → Bool) σ) (address : Fin 64 → Bool) :
    (crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) state.bigEndian)
        (bitVecToHolWord (instFinHolFiniteDimension (width := 64))
          (8 : BitVec 64)) state address).map
          (holWordToBitVec (instFinHolFiniteDimension (width := 64))) =
      crepRuntimeLoadByte
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).toRuntime)
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address) := by
  calc
    _ = (panMemLoadByteHOL
        (fun current =>
          ((state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).memory current).toHolWordLab)
        (fun current =>
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).memaddrs current = true)
        state.bigEndian
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address)).map
          (fun byte => BitVec.ofNat 64 byte.toNat) := by
            exact crepHolEvalMemLoadByte_source_eq_panMemLoadByteHOL
              (instFinHolFiniteDimension (width := 64)) state.bigEndian
              (bitVecToHolWord (instFinHolFiniteDimension (width := 64))
                (8 : BitVec 64)) state address
    _ = crepRuntimeLoadByte
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).toRuntime)
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address) := by
          symm
          exact crepRuntimeLoadByte_riscv64_eq_panMemLoadByteHOL
            (state.toHolFiniteBitVecState
              (instFinHolFiniteDimension (width := 64)))
            (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address)

/-! RV64 Load32 uses the existing PanSem byte-assembly bridge after explicitly
    viewing a Crep word-lab memory as PanSem word cells. -/

theorem crepHolEvalMemLoad32_riscv64_eq_panMemLoad32HOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat 64 value.toNat) := by
  let source : PanSemState (BitVec 64) (FfiState σ) :=
    { locals := fun _ => none
      globals := fun _ => none
      structs := []
      code := []
      exceptionShapes := fun _ => none
      memory := fun current => some (.word (panTheWord (state.memory current)))
      memaddrs := state.memaddrs
      sharedMemaddrs := state.shMemaddrs
      clock := state.clock
      be := state.bigEndian
      ffi := state.ffi
      baseAddress := state.baseAddress
      topAddress := state.topAddress }
  have hget (byteAddress value : BitVec 64) :
      panSemBitVec64WordModel.getByte (8 : BitVec 64) byteAddress value
          state.bigEndian =
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
          (8 : BitVec 64) byteAddress value state.bigEndian := by
    rw [panSemBitVec64GetByte_eq_panRiscVGetByteEndian]
    simp [RiscV.panRiscVMemoryModelForEndian]
  have hmodel :
      panModelRead32
          (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
          state.memaddrs
          (fun current => some (panTheWord (state.memory current)))
          (8 : BitVec 64) address state.bigEndian =
        (panSemBitVec64MemoryAccess source).read32
          (panSemBitVec64MemoryAccess source).domain source.memory
          panSemBitVec64BytesInWord address := by
    change panModelRead32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian =
      panModelRead32 panSemBitVec64WordModel state.memaddrs
        (panValueWordMemory source.memory) (8 : BitVec 64) address state.bigEndian
    unfold panModelRead32
    have haligned :
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).aligned 4 address =
          panSemBitVec64WordModel.aligned 4 address := rfl
    have hbyteAlign :
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian).byteAlign
            (8 : BitVec 64) address =
          panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address := rfl
    rw [haligned, hbyteAlign]
    by_cases ha : panSemBitVec64WordModel.aligned 4 address = true
    · simp only [if_pos ha]
      by_cases hd : state.memaddrs
          (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address) = true
      · simp only [hd, ↓reduceIte]
        change some ((RiscV.panRiscVMemoryModelForEndian state.bigEndian).wordOfBytes32
            state.bigEndian
            [(RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) address
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 1)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 2)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian,
             (RiscV.panRiscVMemoryModelForEndian state.bigEndian).getByte
                (8 : BitVec 64) (address + 3)
                (panTheWord (state.memory
                  (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address))) state.bigEndian]) =
          (some (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))).bind
            (fun value => some (panSemBitVec64WordModel.wordOfBytes32 state.bigEndian
              [panSemBitVec64WordModel.getByte (8 : BitVec 64) address value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 1) value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 2) value state.bigEndian,
               panSemBitVec64WordModel.getByte (8 : BitVec 64) (address + 3) value state.bigEndian]))
        simp only [Option.bind_some]
        rw [← hget address
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 1)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 2)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rw [← hget (address + 3)
          (panTheWord (state.memory
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address)))]
        rfl
      · cases hdom : state.memaddrs
            (panSemBitVec64WordModel.byteAlign (8 : BitVec 64) address) <;>
          simp_all
    · simp [ha]
  calc
    crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address =
      panModelRead32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian :=
          crepHolEvalMemLoad32_eq_panModelRead32 _ _ _ _
    _ = (panSemBitVec64MemoryAccess source).read32
        (panSemBitVec64MemoryAccess source).domain source.memory
        panSemBitVec64BytesInWord address := hmodel
    _ = (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun value => BitVec.ofNat 64 value.toNat) := by
            have hread := panSemBitVec64Read32_eq_panMemLoad32HOL
              source source.memory address
            have hmemory : panValueWordHOL source.memory =
                (fun current => (state.memory current).toHolWordLab) := by
              funext current
              cases hmem : state.memory current with
              | word value =>
                  simp [panValueWordHOL, source, hmem, panTheWord,
                    PanWordLab.toHolWordLab]
            have hdomain :
                (fun current =>
                  (source.memaddrs current &&
                    decide (panValueWordDefined source.memory current = true)) = true) =
                (fun current => state.memaddrs current = true) := by
              funext current
              cases hmem : state.memory current with
              | word value => cases hdomain : state.memaddrs current <;>
                  simp [source, panValueWordDefined, hdomain]
            simpa [hmemory, hdomain, source, panValueWordHOL, panValueWordDefined,
              panValueWordMemory, panSemBitVec64BytesInWord,
              panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
              PanWordLab.toHolWordLab] using hread

theorem crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL {σ : Type}
    (state : CrepHolState (BitVec 64) σ) (address : BitVec 64) :
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map (fun value => BitVec.ofNat 64 value.toNat) := by
  calc
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : BitVec 64) address state.bigEndian :=
          crepRuntimeLoad32_wordTarget_eq_riscv state.toRuntime address
    _ = panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (8 : BitVec 64) address state.bigEndian := rfl
    _ = crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian) (8 : BitVec 64)
        state address := by
          symm
          exact crepHolEvalMemLoad32_eq_panModelRead32 _ _ _ _
    _ = (panMemLoad32HOL
        (fun current => (state.memory current).toHolWordLab)
        (fun current => state.memaddrs current = true)
        state.bigEndian address).map
          (fun value => BitVec.ofNat 64 value.toNat) :=
            crepHolEvalMemLoad32_riscv64_eq_panMemLoad32HOL state address

theorem crepHolEvalMemLoad32_source_eq_riscv64 {σ : Type}
    (state : CrepHolState (Fin 64 → Bool) σ) (address : Fin 64 → Bool) :
    (crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) state.bigEndian)
        (bitVecToHolWord (instFinHolFiniteDimension (width := 64))
          (8 : BitVec 64)) state address).map
          (holWordToBitVec (instFinHolFiniteDimension (width := 64))) =
      crepRuntimeLoad32
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).toRuntime)
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address) := by
  calc
    _ = (panMemLoad32HOL
        (fun current =>
          ((state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).memory current).toHolWordLab)
        (fun current =>
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).memaddrs current = true)
        state.bigEndian
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address)).map
          (fun value => BitVec.ofNat 64 value.toNat) := by
            exact crepHolEvalMemLoad32_source_eq_panMemLoad32HOL
              (instFinHolFiniteDimension (width := 64))
              (bitVecToHolWord (instFinHolFiniteDimension (width := 64))
                (8 : BitVec 64)) state address
    _ = crepRuntimeLoad32
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState
            (instFinHolFiniteDimension (width := 64))).toRuntime)
        (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address) := by
          symm
          exact crepRuntimeLoad32_riscv64_eq_panMemLoad32HOL
            (state.toHolFiniteBitVecState
              (instFinHolFiniteDimension (width := 64)))
            (holWordToBitVec (instFinHolFiniteDimension (width := 64)) address)

theorem crepHolFiniteDimension_local_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (name : Nat) :
    Option.map (mapCrepHolWordLab (bitVecToHolWord dimension))
        ((state.toHolFiniteBitVecState dimension).locals name) = state.locals name := by
  cases h : state.locals name <;>
    simp [CrepHolState.toHolFiniteBitVecState, h, mapCrepHolWordLab,
      bitVecToHolWord_holWordToBitVec]

theorem crepHolFiniteDimension_global_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (name : BitVec 5) :
    Option.map (mapCrepHolWordLab (bitVecToHolWord dimension))
        ((state.toHolFiniteBitVecState dimension).globals name) = state.globals name := by
  cases h : state.globals name <;>
    simp [CrepHolState.toHolFiniteBitVecState, h, mapCrepHolWordLab,
      bitVecToHolWord_holWordToBitVec]

theorem crepHolFiniteDimension_load_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    crepRuntimeLoad (state.toHolFiniteWordRuntime dimension) address =
      (crepRuntimeLoad
        (state.toHolFiniteBitVecState dimension).toRuntime
        (holWordToBitVec dimension address)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  cases state
  simp only [crepRuntimeLoad, CrepHolState.toHolFiniteWordRuntime,
    CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
    mapCrepHolWordLab, panTheWord, bitVecToHolWord_holWordToBitVec]
  split <;> simp_all [bitVecToHolWord_holWordToBitVec dimension]

theorem crepHolFiniteDimension_loadByte_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    crepRuntimeLoadByte (state.toHolFiniteWordRuntime dimension) address =
      (crepRuntimeLoadByte
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState dimension).toRuntime)
        (holWordToBitVec dimension address)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  cases state
  simp [crepRuntimeLoadByte, CrepHolState.toHolFiniteWordRuntime,
    CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
    holFiniteWordRiscVMemoryModel, transportPanMemoryModel, riscvCrepWordTarget,
    mapCrepHolWordLab, panTheWord,
    holWordToBitVec_bitVecToHolWord] <;>
    (split <;> simp_all)

theorem crepHolFiniteDimension_load32_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (address : ι → Bool) :
    crepRuntimeLoad32 (state.toHolFiniteWordRuntime dimension) address =
      (crepRuntimeLoad32
        (riscvCrepWordTarget
          (state.toHolFiniteBitVecState dimension).toRuntime)
        (holWordToBitVec dimension address)).map (bitVecToHolWord dimension) := by
  letI : HolFiniteDimension ι := dimension
  cases state
  simp [crepRuntimeLoad32, CrepHolState.toHolFiniteWordRuntime,
    CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
    holFiniteWordRiscVMemoryModel, transportPanMemoryModel, riscvCrepWordTarget,
    mapCrepHolWordLab, panTheWord, holFiniteWordToBitVec_add,
    holFiniteWordToBitVec_one, holWordToBitVec_bitVecToHolWord,
    BitVec.add_assoc] <;>
    (split <;> simp_all)

theorem crepHolFiniteDimension_wordOp_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (operator : BinOp) (values : List (ι → Bool)) :
    (state.toHolFiniteWordRuntime dimension).memoryModel.wordOp operator values =
      ((state.toHolFiniteBitVecState dimension).toRuntime.memoryModel.wordOp
        operator (values.map (holWordToBitVec dimension))).map
          (bitVecToHolWord dimension) := by
  cases state
  rfl

theorem crepHolFiniteDimension_compare_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (operator : Cmp) (left right : ι → Bool) :
    (state.toHolFiniteWordRuntime dimension).memoryModel.compare operator left right =
      bitVecToHolWord dimension
        ((state.toHolFiniteBitVecState dimension).toRuntime.memoryModel.compare
          operator (holWordToBitVec dimension left) (holWordToBitVec dimension right)) := by
  cases state
  rfl

theorem crepHolFiniteDimension_shift_toBitVec {ι : Type}
    (dimension : HolFiniteDimension ι) (state : CrepHolState (ι → Bool) σ)
    (operator : Shift) (left right : ι → Bool) :
    (state.toHolFiniteWordRuntime dimension).memoryModel.shift operator left right =
      ((state.toHolFiniteBitVecState dimension).toRuntime.memoryModel.shift
        operator (holWordToBitVec dimension left) (holWordToBitVec dimension right)).map
          (bitVecToHolWord dimension) := by
  cases state
  rfl

/-! State projections commute with the finite-index/BitVec carrier map. These
    equations discharge the target-independent `Var`, `LoadGlob`, and plain
    `Load` cases when proving evaluator transport; they do not yet cover the
    target word operations or byte loads. -/
theorem crepHolWordBits_local_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (name : Nat) :
    (state.toBitVecState.locals name).map
        (mapCrepHolWordLab bitVecToHolWordBits) = state.locals name := by
  cases h : state.locals name <;>
    simp [CrepHolState.toBitVecState, h, mapCrepHolWordLab,
      bitVecToHolWordBits_holWordBitsToBitVec]

theorem crepHolWordBits_global_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (name : BitVec 5) :
    (state.toBitVecState.globals name).map
        (mapCrepHolWordLab bitVecToHolWordBits) = state.globals name := by
  cases h : state.globals name <;>
    simp [CrepHolState.toBitVecState, h, mapCrepHolWordLab,
      bitVecToHolWordBits_holWordBitsToBitVec]

theorem crepHolWordBits_load_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : Fin width → Bool) :
    crepRuntimeLoad state.toHolWordBitsRuntime address =
      (crepRuntimeLoad state.toBitVecState.toRuntime
        (holWordBitsToBitVec address)).map bitVecToHolWordBits := by
  cases state
  simp [crepRuntimeLoad, CrepHolState.toHolWordBitsRuntime, CrepHolState.toRuntime,
    CrepHolState.toBitVecState, mapCrepHolWordLab, panTheWord,
    bitVecToHolWordBits_holWordBitsToBitVec] <;> rfl

theorem crepHolWordBits_loadByte_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : Fin width → Bool) :
    crepRuntimeLoadByte state.toHolWordBitsRuntime address =
      (crepRuntimeLoadByte
        (riscvCrepWordTarget state.toBitVecState.toRuntime)
        (holWordBitsToBitVec address)).map bitVecToHolWordBits := by
  cases state
  simp [crepRuntimeLoadByte, CrepHolState.toHolWordBitsRuntime,
    CrepHolState.toRuntime, CrepHolState.toBitVecState,
    holWordBitsRiscVMemoryModel, riscvCrepWordTarget, mapCrepHolWordLab,
    panTheWord, holWordBitsToBitVec_bitVecToHolWordBits] <;>
    (split <;> simp_all)

theorem crepHolWordBits_load32_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : Fin width → Bool) :
    crepRuntimeLoad32 state.toHolWordBitsRuntime address =
      (crepRuntimeLoad32
        (riscvCrepWordTarget state.toBitVecState.toRuntime)
        (holWordBitsToBitVec address)).map bitVecToHolWordBits := by
  cases state
  simp [crepRuntimeLoad32, CrepHolState.toHolWordBitsRuntime,
    CrepHolState.toRuntime, CrepHolState.toBitVecState,
    holWordBitsRiscVMemoryModel, riscvCrepWordTarget, mapCrepHolWordLab,
    panTheWord, holWordBitsToBitVec_bitVecToHolWordBits,
    BitVec.add_assoc] <;> (split <;> simp_all)

theorem crepHolWordBits_wordOp_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (operator : BinOp) (values : List (Fin width → Bool)) :
    state.toHolWordBitsRuntime.memoryModel.wordOp operator values =
      (state.toBitVecState.toRuntime.memoryModel.wordOp operator
        (values.map holWordBitsToBitVec)).map bitVecToHolWordBits := by
  cases state
  simp [CrepHolState.toHolWordBitsRuntime, CrepHolState.toBitVecState,
    CrepHolState.toRuntime, holWordBitsRiscVMemoryModel]

theorem crepHolWordBits_compare_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (operator : Cmp) (left right : Fin width → Bool) :
    state.toHolWordBitsRuntime.memoryModel.compare operator left right =
      bitVecToHolWordBits
        (state.toBitVecState.toRuntime.memoryModel.compare operator
          (holWordBitsToBitVec left) (holWordBitsToBitVec right)) := by
  cases state
  rfl

theorem crepHolWordBits_shift_toBitVec [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (operator : Shift) (left right : Fin width → Bool) :
    state.toHolWordBitsRuntime.memoryModel.shift operator left right =
      (state.toBitVecState.toRuntime.memoryModel.shift operator
        (holWordBitsToBitVec left) (holWordBitsToBitVec right)).map
          bitVecToHolWordBits := by
  cases state
  rfl

/-- Source-shaped Lean translation of HOL `crepSem$eval_def` for every
    positive BitVec word width. It is untagged because the arbitrary HOL word
    carrier remains unrepresented; `evalCrepRuntimeExp_toRuntime_eq` proves
    this translation agrees constructor by constructor with production.

    Source-reviewed disposition for HOL
    `eval_nested_decs_seq_res_var_eq`
    (`pan_to_crepProofScript.sml:596-620`): HOL implicitly universally
    quantifies `es`, `ns`, `t`, `ev`, and `p`. The four premises are successful
    evaluation of every expression in `es`, equal lengths of `ns` and `es`,
    `distinct_lists ns (FLAT (MAP var_cexp es))`, and distinct `ns`. The
    conclusion is the exact equation for evaluating `nested_decs ns es p`:
    evaluate `p` after installing `ZIP (ns, ev)`, then restore each original
    local with `FOLDL res_var` over `ZIP (ns, MAP (FLOOKUP t.locals) ns)`.
    `nestedDecsHOL` ports only the syntax. This expression evaluator is over
    production `CrepExp` and `CrepHolState`, while the theorem quantifies over
    the full Crep program and finite-map state; `evalCrepClockProg` likewise
    covers only restricted production `CrepClockProg`/`CrepHolState`. There is
    no full evaluator over `CrepProgHOL`/`CrepExpHOL` and
    `CrepSemHOLState`, so the equation cannot be stated with these evaluators
    and no tag is claimed. The faithful replacement is
    `flapjack-4ac.5.19.1`, dependent on `flapjack-4ac.5.82` and exact Crep
    carriers `flapjack-pxn.18.3.5.8.8`. -/
def evalCrepHolExp [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepExp (RiscV.Word width) → Option (RiscV.Word width)
  | .const value => some value
  | .var name => (state.locals name).map panTheWord
  | .load address => do
      let address ← evalCrepHolExp state address
      if state.memaddrs address then some (panTheWord (state.memory address)) else none
  | .load32 address => do
      let address ← evalCrepHolExp state address
      crepHolEvalMemLoad32
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        (BitVec.ofNat width (width / 8)) state address
  | .loadByte address => do
      let address ← evalCrepHolExp state address
      crepHolEvalMemLoadByte
        (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        (BitVec.ofNat width (width / 8)) state address
  | .loadGlob address => (state.globals address).map panTheWord
  | .op operator expressions => do
      let values ← expressions.mapM (evalCrepHolExp state)
      wordOpHOL operator values
  | .crepOp .mul [left, right] => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      pure (left * right)
  | .crepOp _ _ => none
  | .cmp operator left right => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepHolExp state left
      let right ← evalCrepHolExp state right
      evalPanShiftFull operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
termination_by expression => sizeOf expression

/-- HOL-shaped complete result wrapper for the raw word evaluator above. -/
def evalCrepHolExpWordLab [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) :
    CrepExp (RiscV.Word width) → Option (PanWordLab (RiscV.Word width)) :=
  fun expression => (evalCrepHolExp state expression).map PanWordLab.word

/-! HOL evaluator source shape for the Fin-index word representation is
    obtained by transporting the existing source-shaped evaluator through the
    carrier equivalence. Its production relation is proved below for every
    constructor, but the concrete `Fin width` index still does not represent
    every HOL finite dimension type. -/
def evalCrepHolWordBitsExp [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) :
    CrepExp (Fin width → Bool) → Option (Fin width → Bool) :=
  fun expression =>
    (evalCrepHolExp (state.toBitVecState)
      (mapCrepExpWord holWordBitsToBitVec expression)).map bitVecToHolWordBits

def evalCrepHolWordBitsExpWordLab [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) :
    CrepExp (Fin width → Bool) → Option (PanWordLab (Fin width → Bool)) :=
  fun expression => (evalCrepHolWordBitsExp state expression).map PanWordLab.word

/-! Source-shaped evaluator transport for an explicitly enumerated finite
    Boolean-index carrier. `HolFiniteDimension` is an explicit Lean witness
    that the index is equivalent to `Fin width`; it is representation
    infrastructure, and the operations are interpreted through the RISC-V
    BitVec model. A production evaluator correspondence for every expression
    constructor is proved below, but these adapters are not the unrestricted
    HOL-polymorphic semantics and carry no HOL tag. -/
def evalCrepHolFiniteDimensionExp {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepExp (ι → Bool) → Option (ι → Bool) := by
  letI : HolFiniteDimension ι := dimension
  exact fun expression =>
    (evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) expression)).map
        (bitVecToHolWord dimension)

def evalCrepHolFiniteDimensionExpWordLab {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepExp (ι → Bool) → Option (PanWordLab (ι → Bool)) :=
  fun expression =>
    (evalCrepHolFiniteDimensionExp dimension state expression).map PanWordLab.word

/-! Source equations for the HOL evaluator on an explicitly enumerated finite
    word carrier. `holFiniteIndex_bijective` proves that the supplied
    `HolFiniteDimension` dictionary has the defining finite_index property;
    this evaluator remains untagged until its word-operation and evaluation
    equations are reviewed against the corresponding HOL definitions. -/
def evalCrepHolFiniteWordSourceExp {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepExp (ι → Bool) → Option (ι → Bool)
  | .const value => some value
  | .var name => (state.locals name).map panTheWord
  | .load address => do
      let address ← evalCrepHolFiniteWordSourceExp dimension state address
      if state.memaddrs address then some (panTheWord (state.memory address)) else none
  | .load32 address => do
      let address ← evalCrepHolFiniteWordSourceExp dimension state address
      let model := holFiniteWordSourceMemoryModel dimension state.bigEndian
      let bytesInWord := bitVecToHolWord dimension
        (BitVec.ofNat dimension.width (dimension.width / 8))
      crepHolEvalMemLoad32 model bytesInWord state address
  | .loadByte address => do
      let address ← evalCrepHolFiniteWordSourceExp dimension state address
      let model := holFiniteWordSourceMemoryModel dimension state.bigEndian
      let bytesInWord := bitVecToHolWord dimension
        (BitVec.ofNat dimension.width (dimension.width / 8))
      crepHolEvalMemLoadByte model bytesInWord state address
  | .loadGlob address => (state.globals address).map panTheWord
  | .op operator expressions => do
      let values ← expressions.mapM
        (evalCrepHolFiniteWordSourceExp dimension state)
      let model := holFiniteWordSourceMemoryModel dimension state.bigEndian
      model.wordOp operator values
  | .crepOp .mul [left, right] => do
      let left ← evalCrepHolFiniteWordSourceExp dimension state left
      let right ← evalCrepHolFiniteWordSourceExp dimension state right
      holFiniteWordSourceCrepOp dimension .mul [left, right]
  | .crepOp _ _ => none
  | .cmp operator left right => do
      let left ← evalCrepHolFiniteWordSourceExp dimension state left
      let right ← evalCrepHolFiniteWordSourceExp dimension state right
      let model := holFiniteWordSourceMemoryModel dimension state.bigEndian
      pure (model.compare operator left right)
  | .shift operator left right => do
      let left ← evalCrepHolFiniteWordSourceExp dimension state left
      let right ← evalCrepHolFiniteWordSourceExp dimension state right
      let model := holFiniteWordSourceMemoryModel dimension state.bigEndian
      model.shift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
termination_by expression => sizeOf expression

/-- In the source evaluator's `CrepOp` clause, successful child evaluations
    evaluation is followed by the tagged HOL `crep_op_def` operation, with the
    result transported back through the explicit finite-word carrier. This
    is adapter infrastructure rather than a standalone HOL theorem: the
    evaluator and state still use Flapjack's explicit dimension witness. -/
theorem evalCrepHolFiniteWordSourceExp_crepOp_eq_crepOpCrepWord
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension state left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension state right = some rightValue) :
    (evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right])).map (holWordToBitVec dimension) =
    crepOpCrepWord (width := dimension.width) .mul
      [holWordToBitVec dimension leftValue, holWordToBitVec dimension rightValue] := by
  simp [evalCrepHolFiniteWordSourceExp, hLeft, hRight,
    holFiniteWordSourceCrepOp_to_crepOpCrepWord]

/-- Complete `word_lab` view of the source `CrepOp.mul` equation. Transporting
    the finite-word result to BitVec preserves the outer HOL `Word` wrapper
    and yields the tagged `crep_op_def` result. This is Flapjack adapter
    infrastructure; the whole source evaluator/state is still not identified
    with native HOL `crepSem$eval`. -/
theorem evalCrepHolFiniteWordSourceExpWordLab_crepOp_eq_crepOpCrepWord
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool)) (leftValue rightValue : ι → Bool)
    (hLeft : evalCrepHolFiniteWordSourceExp dimension state left = some leftValue)
    (hRight : evalCrepHolFiniteWordSourceExp dimension state right = some rightValue) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.crepOp .mul [left, right])).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (crepOpCrepWord (width := dimension.width) .mul
        [holWordToBitVec dimension leftValue, holWordToBitVec dimension rightValue]).map
          PanWordLab.word := by
  calc
    ((evalCrepHolFiniteWordSourceExp dimension state
        (.crepOp .mul [left, right])).map PanWordLab.word).map
          (mapCrepHolWordLab (holWordToBitVec dimension)) =
        ((evalCrepHolFiniteWordSourceExp dimension state
          (.crepOp .mul [left, right])).map
            (holWordToBitVec dimension)).map PanWordLab.word := by
      simp [Option.map_map, Function.comp_def, mapCrepHolWordLab]
    _ = _ := congrArg (Option.map PanWordLab.word)
      (evalCrepHolFiniteWordSourceExp_crepOp_eq_crepOpCrepWord
        dimension state left right leftValue rightValue hLeft hRight)

/-- The source evaluator's `Op` clause routes a successfully evaluated
    operand list through the tagged HOL `word_op_def` port, preserving the
    `word_lab` wrapper and converting the result back to the finite-index
    word carrier. This is a primitive evaluator bridge; it does not identify
    the complete source evaluator with a native HOL finite-index instance. -/
theorem evalCrepHolFiniteWordSourceExpWordLab_op_eq_wordOpHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool))) (values : List (ι → Bool))
    (hValues : expressions.mapM
      (evalCrepHolFiniteWordSourceExp dimension state) = some values) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.op operator expressions)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (wordOpHOL operator (values.map (holWordToBitVec dimension))).map
      PanWordLab.word := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp only [evalCrepHolFiniteWordSourceExp, Option.bind_eq_bind, hValues,
    Option.bind_some]
  simp [holFiniteWordSourceMemoryModel, mapCrepHolWordLab,
    holWordToBitVec_bitVecToHolWord, Option.map_map, Function.comp_def]

/-- The finite-index source evaluator's successful `Op` clause agrees with
    the executed RISC-V runtime evaluator on the word-converted expression
    and operand values.  The hypotheses expose recursive child evaluation on
    both sides; this pins the constructor dispatch without claiming that the
    source and production memory/state carriers agree. -/
theorem evalCrepHolFiniteWordSourceExp_op_eq_riscvRuntime
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool))) (values : List (ι → Bool))
    (hSource : expressions.mapM
      (evalCrepHolFiniteWordSourceExp dimension state) = some values)
    (hRuntime : (expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
      (evalCrepRuntimeExp (riscvCrepWordTarget
        (state.toHolFiniteBitVecState dimension).toRuntime)) =
        some (values.map (holWordToBitVec dimension))) :
    (evalCrepHolFiniteWordSourceExp dimension state
      (.op operator expressions)).map (holWordToBitVec dimension) =
    evalCrepRuntimeExp (riscvCrepWordTarget
      (state.toHolFiniteBitVecState dimension).toRuntime)
      (.op operator (expressions.map
        (mapCrepExpWord (holWordToBitVec dimension)))) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp only [evalCrepHolFiniteWordSourceExp, Option.bind_eq_bind, hSource,
    Option.bind_some]
  simp only [evalCrepRuntimeExp, hRuntime]
  simpa [riscvCrepWordTarget, CrepHolState.toHolFiniteBitVecState,
    CrepHolState.toRuntime,
    holFiniteWordSourceMemoryModel, Option.map_map, Function.comp_def]
    using (holFiniteWordSourceModel_ops_eq_riscvWordTarget dimension
      state.bigEndian operator values .mul [] .equal .lsl (values.headD 0)
      (values.headD 0)).1

/-- The recursive source `Load` clause transports to the tagged width-indexed
    HOL `mem_load_def`: it checks the same address domain and returns the same
    complete `word_lab` cell after converting the finite-index word state to
    `BitVec`. This remains adapter support because the surrounding recursive
    evaluator and its finite-index dictionary are not identified with native
    HOL `crepSem$eval`. -/
theorem evalCrepHolFiniteWordSourceExpWordLab_load_eq_memLoadCrepHolW
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension state
      addressExpression = some address) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.load addressExpression)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    memLoadCrepHolW (holWordToBitVec dimension address)
      (CrepHolState.toHolFiniteBitVecState dimension state) := by
  letI : NeZero dimension.width := ⟨Nat.ne_of_gt dimension.width_pos⟩
  simp [evalCrepHolFiniteWordSourceExp, hAddress, memLoadCrepHolW,
    CrepHolState.toHolFiniteBitVecState, mapCrepHolWordLab, panTheWord,
    bitVecToHolWord_holWordToBitVec]

/-- Complete HOL `word_lab` result view of the explicitly finite-index
    source evaluator. Since `word_lab` has only the `Word` constructor, this
    is the corresponding `Option (PanWordLab word)` encoding. -/
def evalCrepHolFiniteWordSourceExpWordLab {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    CrepExp (ι → Bool) → Option (PanWordLab (ι → Bool)) :=
  fun expression =>
    (evalCrepHolFiniteWordSourceExp dimension state expression).map
      PanWordLab.word

/-! This all-constructor bridge connects production evaluation to the explicit
    source equations above, including the source load model and source
    multiplication. It remains Flapjack representation support until the
    finite-index witness is related to HOL's implicit word carrier. -/
theorem evalCrepRuntimeExp_sourceWord_eq {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) :
    evalCrepRuntimeExp (state.toHolFiniteWordSourceRuntime dimension) expression =
      evalCrepHolFiniteWordSourceExp dimension state expression := by
  letI : HolFiniteDimension ι := dimension
  have evalExpsMapM (sourceState : CrepHolState (ι → Bool) σ) :
      ∀ expressions,
        evalCrepRuntimeExps
            (sourceState.toHolFiniteWordSourceRuntime dimension) expressions =
          expressions.mapM
            (evalCrepRuntimeExp
              (sourceState.toHolFiniteWordSourceRuntime dimension)) := by
    intro expressions
    induction expressions with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (sourceState : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExp
              (sourceState.toHolFiniteWordSourceRuntime dimension) e =
            evalCrepHolFiniteWordSourceExp dimension sourceState e) ∧
        (∀ (sourceState : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExps
              (sourceState.toHolFiniteWordSourceRuntime dimension) expressions =
            expressions.mapM
              (evalCrepHolFiniteWordSourceExp dimension sourceState))))
      generalizing state
  case const value => simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp]
  case var name =>
    simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime]
  case load address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      Option.bind_eq_bind]
    rw [ih state]
    rfl
  case load32 address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      Option.bind_eq_bind]
    rw [ih state]
    cases hAddress : evalCrepHolFiniteWordSourceExp dimension state address with
    | none => simp
    | some value =>
      simp only [Option.bind_some]
      exact crepHolFiniteWordSourceRuntime_load32 state value
  case loadByte address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      Option.bind_eq_bind]
    rw [ih state]
    cases hAddress : evalCrepHolFiniteWordSourceExp dimension state address with
    | none => simp
    | some value =>
      simp only [Option.bind_some]
      exact crepHolFiniteWordSourceRuntime_loadByte state value
  case loadGlob address =>
    simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime]
  case op operator expressions ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp]
    rw [← evalExpsMapM state expressions]
    rw [ih.2 state]
    rfl
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil =>
      simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp]
    | cons left rest => cases rest with
      | nil =>
        simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp]
      | cons right rest => cases rest with
        | nil =>
          simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
            ih.1 left (by simp) state, ih.1 right (by simp) state,
            holFiniteWordSourceCrepOp,
            crepOpCrep, holFiniteWordSourceMul_eq_mul]
        | cons extra rest =>
          simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp]
  case cmp operator left right ihLeft ihRight =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      Option.bind_eq_bind]
    rw [ihLeft state, ihRight state]
    rfl
  case shift operator left right ihLeft ihRight =>
    simp only [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      Option.bind_eq_bind]
    rw [ihLeft state, ihRight state]
    rfl
  case baseAddr =>
    simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime]
  case topAddr =>
    simp [evalCrepRuntimeExp, evalCrepHolFiniteWordSourceExp,
      CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he sourceState
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead sourceState
      · exact ihTail.1 e he sourceState
    · intro sourceState
      simp [evalCrepRuntimeExps, ihHead sourceState, ihTail.2 sourceState]

/-- Complete `word_lab` result bridge for the all-constructor source/runtime
    evaluator theorem above. Since `word_lab` has only the `Word` constructor,
    mapping the raw runtime result through `PanWordLab.word` gives the source
    evaluator's full `Option (word_lab word)` shape. This remains untagged:
    the explicit `HolFiniteDimension` witness and its word-operation adapters
    have not been identified with HOL's implicit `finite_index` instance. -/
theorem evalCrepRuntimeExp_sourceWordLab_eq {ι : Type} {σ : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) :
    (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression).map
        PanWordLab.word =
      evalCrepHolFiniteWordSourceExpWordLab dimension state expression := by
  change (evalCrepRuntimeExp
      (state.toHolFiniteWordSourceRuntime dimension) expression).map
        PanWordLab.word =
      (evalCrepHolFiniteWordSourceExp dimension state expression).map
        PanWordLab.word
  rw [evalCrepRuntimeExp_sourceWord_eq]

/-- The source evaluator's recursive `LoadByte` case, after a successful
    address evaluation, is exactly the tagged HOL `mem_load_byte_def` port
    followed by HOL's `w2w` widening back to the expression word type. The
    explicit finite-index/BitVec representation remains a parameter, so this
    constructor equation does not claim the whole polymorphic `eval_def`
    correspondence. -/
theorem evalCrepHolFiniteWordSourceExp_loadByte_eq_panMemLoadByteHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension state
      addressExpression = some address) :
    (evalCrepHolFiniteWordSourceExp dimension state
      (.loadByte addressExpression)).map (holWordToBitVec dimension) =
    (panMemLoadByteHOL
      (fun bitAddress =>
        ((CrepHolState.toHolFiniteBitVecState dimension state).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
          bitAddress = true)
      state.bigEndian (holWordToBitVec dimension address)).map
        (fun byte => BitVec.ofNat dimension.width byte.toNat) := by
  simp only [evalCrepHolFiniteWordSourceExp, hAddress]
  exact crepHolEvalMemLoadByte_source_eq_panMemLoadByteHOL dimension
    state.bigEndian
    (bitVecToHolWord dimension
      (BitVec.ofNat dimension.width (dimension.width / 8)))
    state address

/-- Complete `word_lab` result form of the source `LoadByte` equation above.
    It transports the evaluator result through the word wrapper and matches
    the tagged HOL `mem_load_byte_def` result, including the `w2w` conversion.
    This is adapter support: it does not identify the surrounding recursive
    source evaluator with HOL's implicit finite-index evaluator. -/
theorem evalCrepHolFiniteWordSourceExpWordLab_loadByte_eq_panMemLoadByteHOL
    {ι : Type} {σ : Type} (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (addressExpression : CrepExp (ι → Bool)) (address : ι → Bool)
    (hAddress : evalCrepHolFiniteWordSourceExp dimension state
      addressExpression = some address) :
    ((evalCrepHolFiniteWordSourceExp dimension state
      (.loadByte addressExpression)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec dimension)) =
    (panMemLoadByteHOL
      (fun bitAddress =>
        ((CrepHolState.toHolFiniteBitVecState dimension state).memory
          bitAddress).toHolWordLab)
      (fun bitAddress =>
        (CrepHolState.toHolFiniteBitVecState dimension state).memaddrs
          bitAddress = true)
      state.bigEndian (holWordToBitVec dimension address)).map
        (fun byte => PanWordLab.word
          (BitVec.ofNat dimension.width byte.toNat)) := by
  simpa [Option.map_map, Function.comp_def, mapCrepHolWordLab] using
    congrArg (Option.map PanWordLab.word)
      (evalCrepHolFiniteWordSourceExp_loadByte_eq_panMemLoadByteHOL
        dimension state addressExpression address hAddress)

theorem evalCrepRuntimeExp_finiteDimension_const {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (value : ι → Bool) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.const value) =
      evalCrepHolFiniteDimensionExp dimension state (.const value) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, CrepHolState.toHolFiniteWordRuntime,
    evalCrepHolFiniteDimensionExp, evalCrepHolExp, mapCrepExpWord]
  change some value =
    (some (holWordToBitVec dimension value)).map (bitVecToHolWord dimension)
  simp only [Option.map_some, bitVecToHolWord_holWordToBitVec]

theorem evalCrepRuntimeExp_finiteDimension_baseAddr {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) .baseAddr =
      evalCrepHolFiniteDimensionExp dimension state .baseAddr := by
  letI : HolFiniteDimension ι := dimension
  simp [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    CrepHolState.toHolFiniteWordRuntime, CrepHolState.toHolFiniteBitVecState,
    mapCrepExpWord, bitVecToHolWord_holWordToBitVec]

theorem evalCrepRuntimeExp_finiteDimension_topAddr {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) .topAddr =
      evalCrepHolFiniteDimensionExp dimension state .topAddr := by
  letI : HolFiniteDimension ι := dimension
  simp [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    CrepHolState.toHolFiniteWordRuntime, CrepHolState.toHolFiniteBitVecState,
    mapCrepExpWord, bitVecToHolWord_holWordToBitVec]

theorem evalCrepRuntimeExp_finiteDimension_var {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (name : Nat) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.var name) =
      evalCrepHolFiniteDimensionExp dimension state (.var name) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, CrepHolState.toHolFiniteWordRuntime,
    evalCrepHolFiniteDimensionExp, evalCrepHolExp, mapCrepExpWord]
  change (state.locals name).map panTheWord =
    Option.map (bitVecToHolWord dimension)
      (((state.toHolFiniteBitVecState dimension).locals name).map panTheWord)
  rw [← crepHolFiniteDimension_local_toBitVec dimension state name]
  simp [mapCrepHolWordLab, panTheWord, Function.comp_def]

theorem evalCrepRuntimeExp_finiteDimension_loadGlob {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : BitVec 5) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.loadGlob address) =
      evalCrepHolFiniteDimensionExp dimension state (.loadGlob address) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, CrepHolState.toHolFiniteWordRuntime,
    evalCrepHolFiniteDimensionExp, evalCrepHolExp, mapCrepExpWord]
  change (state.globals address).map panTheWord =
    Option.map (bitVecToHolWord dimension)
      (((state.toHolFiniteBitVecState dimension).globals address).map panTheWord)
  rw [← crepHolFiniteDimension_global_toBitVec dimension state address]
  simp [mapCrepHolWordLab, panTheWord, Function.comp_def]

theorem evalCrepRuntimeExp_finiteDimension_load {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (ih : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) address =
      evalCrepHolFiniteDimensionExp dimension state address) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.load address) =
      evalCrepHolFiniteDimensionExp dimension state (.load address) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp,
    evalCrepHolExp, mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) address =
            some (bitVecToHolWord dimension value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [crepHolFiniteDimension_load_toBitVec]
      simp [crepRuntimeLoad, CrepHolState.toRuntime,
        CrepHolState.toHolFiniteBitVecState,
        mapCrepHolWordLab, panTheWord, holWordToBitVec_bitVecToHolWord,
        bitVecToHolWord_holWordToBitVec dimension] <;>
    (split <;> simp_all <;> try rw [bitVecToHolWord_holWordToBitVec dimension])

private theorem evalCrepRuntimeExps_finiteDimension_toMapM {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepRuntimeState (ι → Bool) σ)
    (expressions : List (CrepExp (ι → Bool))) :
    evalCrepRuntimeExps state expressions =
      expressions.mapM (evalCrepRuntimeExp state) := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps]
  | cons head tail ih => simp [evalCrepRuntimeExps, ih]

theorem evalCrepRuntimeExp_finiteDimension_op {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (ι → Bool)))
    (ih : evalCrepRuntimeExps (state.toHolFiniteWordRuntime dimension) expressions =
      ((expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
        (evalCrepHolExp (state.toHolFiniteBitVecState dimension))).map
          (List.map (bitVecToHolWord dimension))) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.op operator expressions) =
      evalCrepHolFiniteDimensionExp dimension state (.op operator expressions) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  rw [← evalCrepRuntimeExps_finiteDimension_toMapM]
  rw [ih]
  cases hvalues :
      (expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
        (evalCrepHolExp (state.toHolFiniteBitVecState dimension)) with
  | none => simp
  | some values =>
      simp
      rw [crepHolFiniteDimension_wordOp_toBitVec dimension state operator
        (List.map (bitVecToHolWord dimension) values)]
      simp [CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
        wordOpHOL, Function.comp_def, holWordToBitVec_bitVecToHolWord dimension,
        RiscV.panRiscVMemoryModelForEndian, panRiscVWordOp_eq_wordOpHOL]

theorem evalCrepRuntimeExp_finiteDimension_cmp {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Cmp)
    (left right : CrepExp (ι → Bool))
    (ihLeft : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
      evalCrepHolFiniteDimensionExp dimension state left)
    (ihRight : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
      evalCrepHolFiniteDimensionExp dimension state right) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.cmp operator left right) =
      evalCrepHolFiniteDimensionExp dimension state (.cmp operator left right) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) left) with
  | none =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftSource]
  | some leftValue =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
            some (bitVecToHolWord dimension leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right) with
      | none =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right = none := by
            simpa [hRight] using ihRight
          simp [hLeftSource, hRightSource]
      | some rightValue =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
                some (bitVecToHolWord dimension rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftSource, hRightSource]
          simp
          rw [crepHolFiniteDimension_compare_toBitVec dimension state operator
            (bitVecToHolWord dimension leftValue) (bitVecToHolWord dimension rightValue)]
          simp [CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
            RiscV.panRiscVMemoryModelForEndian, panRiscVCmp_eq_evalPanCmp,
            holWordToBitVec_bitVecToHolWord dimension]

theorem evalCrepRuntimeExp_finiteDimension_shift {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (operator : Shift)
    (left right : CrepExp (ι → Bool))
    (ihLeft : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
      evalCrepHolFiniteDimensionExp dimension state left)
    (ihRight : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
      evalCrepHolFiniteDimensionExp dimension state right) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.shift operator left right) =
      evalCrepHolFiniteDimensionExp dimension state (.shift operator left right) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) left) with
  | none =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftSource]
  | some leftValue =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
            some (bitVecToHolWord dimension leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right) with
      | none =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right = none := by
            simpa [hRight] using ihRight
          simp [hLeftSource, hRightSource]
      | some rightValue =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
                some (bitVecToHolWord dimension rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftSource, hRightSource]
          simp
          rw [crepHolFiniteDimension_shift_toBitVec dimension state operator
            (bitVecToHolWord dimension leftValue) (bitVecToHolWord dimension rightValue)]
          simp [CrepHolState.toHolFiniteBitVecState, CrepHolState.toRuntime,
            RiscV.panRiscVMemoryModelForEndian, panRiscVShift_eq_evalPanShiftFull,
            holWordToBitVec_bitVecToHolWord dimension]

theorem evalCrepRuntimeExp_finiteDimension_crepOpMul {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (left right : CrepExp (ι → Bool))
    (ihLeft : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
      evalCrepHolFiniteDimensionExp dimension state left)
    (ihRight : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
      evalCrepHolFiniteDimensionExp dimension state right) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension)
        (.crepOp .mul [left, right]) =
      evalCrepHolFiniteDimensionExp dimension state (.crepOp .mul [left, right]) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) left) with
  | none =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftSource, evalCrepHolExp, hLeft]
  | some leftValue =>
      have hLeftSource :
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) left =
            some (bitVecToHolWord dimension leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) right) with
      | none =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right = none := by
            simpa [hRight] using ihRight
          simp [hLeftSource, hRightSource, evalCrepHolExp, hLeft, hRight]
      | some rightValue =>
          have hRightSource :
              evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) right =
                some (bitVecToHolWord dimension rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftSource, hRightSource]
          simp [evalCrepHolExp, hLeft, hRight, crepOpCrep]
          apply holWordToBitVec_injective dimension
          rw [holFiniteWordToBitVec_mul]
          simp [holWordToBitVec_bitVecToHolWord]

private theorem evalCrepRuntimeExps_toMapM_wordBits [NeZero width]
    (state : CrepRuntimeState (Fin width → Bool) σ)
    (expressions : List (CrepExp (Fin width → Bool))) :
    evalCrepRuntimeExps state expressions =
      expressions.mapM (evalCrepRuntimeExp state) := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps]
  | cons head tail ih => simp [evalCrepRuntimeExps, ih]

/-! Production evaluator constructor equations. These are kernel-checked
    correspondences between the production evaluator over the finite-index
    word state and the transported source-shaped evaluator; they supply
    genuine base cases for a later all-constructor induction. -/
theorem evalCrepRuntimeExp_var_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (name : Nat) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.var name) =
      evalCrepHolWordBitsExp state (.var name) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord, CrepHolState.toHolWordBitsRuntime]
  rw [← crepHolWordBits_local_toBitVec state name]
  simp [Function.comp_def, mapCrepHolWordLab, panTheWord]

theorem evalCrepRuntimeExp_loadGlob_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (address : BitVec 5) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.loadGlob address) =
      evalCrepHolWordBitsExp state (.loadGlob address) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord, CrepHolState.toHolWordBitsRuntime]
  rw [← crepHolWordBits_global_toBitVec state address]
  simp [Function.comp_def, mapCrepHolWordLab, panTheWord]

theorem evalCrepRuntimeExp_load_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : CrepExp (Fin width → Bool))
    (ih : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
      evalCrepHolWordBitsExp state address) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.load address) =
      evalCrepHolWordBitsExp state (.load address) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
          some (bitVecToHolWordBits value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp
      rw [crepHolWordBits_load_toBitVec state (bitVecToHolWordBits value)]
      simp [crepRuntimeLoad, CrepHolState.toRuntime,
        CrepHolState.toBitVecState, mapCrepHolWordLab, panTheWord,
        holWordBitsToBitVec_bitVecToHolWordBits] <;> rfl

theorem evalCrepRuntimeExp_op_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (operator : BinOp)
    (expressions : List (CrepExp (Fin width → Bool)))
    (ih : evalCrepRuntimeExps state.toHolWordBitsRuntime expressions =
      ((expressions.map (mapCrepExpWord holWordBitsToBitVec)).mapM
        (evalCrepHolExp state.toBitVecState)).map
          (List.map bitVecToHolWordBits)) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.op operator expressions) =
      evalCrepHolWordBitsExp state (.op operator expressions) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  rw [← evalCrepRuntimeExps_toMapM_wordBits]
  rw [ih]
  cases hvalues :
      (expressions.map (mapCrepExpWord holWordBitsToBitVec)).mapM
        (evalCrepHolExp state.toBitVecState) with
  | none => simp
  | some values =>
      simp
      rw [crepHolWordBits_wordOp_toBitVec state operator
        (List.map bitVecToHolWordBits values)]
      simp [CrepHolState.toBitVecState, CrepHolState.toRuntime, wordOpHOL,
        Function.comp_def, holWordBitsToBitVec_bitVecToHolWordBits,
        RiscV.panRiscVMemoryModelForEndian,
        panRiscVWordOp_eq_wordOpHOL]

theorem evalCrepRuntimeExp_cmp_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (operator : Cmp)
    (left right : CrepExp (Fin width → Bool))
    (ihLeft : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
    evalCrepHolWordBitsExp state left)
    (ihRight : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
      evalCrepHolWordBitsExp state right) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.cmp operator left right) =
    evalCrepHolWordBitsExp state (.cmp operator left right) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec left) with
  | none =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftFin]
  | some leftValue =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
          some (bitVecToHolWordBits leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp state.toBitVecState
          (mapCrepExpWord holWordBitsToBitVec right) with
      | none =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right = none := by
            simpa [hRight] using ihRight
          simp [hLeftFin, hRightFin]
      | some rightValue =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
              some (bitVecToHolWordBits rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftFin, hRightFin]
          simp
          rw [crepHolWordBits_compare_toBitVec state operator
            (bitVecToHolWordBits leftValue) (bitVecToHolWordBits rightValue)]
          simp [CrepHolState.toBitVecState, CrepHolState.toRuntime,
            RiscV.panRiscVMemoryModelForEndian, panRiscVCmp_eq_evalPanCmp,
            holWordBitsToBitVec_bitVecToHolWordBits]

theorem evalCrepRuntimeExp_shift_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ) (operator : Shift)
    (left right : CrepExp (Fin width → Bool))
    (ihLeft : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
      evalCrepHolWordBitsExp state left)
    (ihRight : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
      evalCrepHolWordBitsExp state right) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.shift operator left right) =
    evalCrepHolWordBitsExp state (.shift operator left right) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec left) with
  | none =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftFin]
  | some leftValue =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
          some (bitVecToHolWordBits leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp state.toBitVecState
          (mapCrepExpWord holWordBitsToBitVec right) with
      | none =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right = none := by
            simpa [hRight] using ihRight
          simp [hLeftFin, hRightFin]
      | some rightValue =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
              some (bitVecToHolWordBits rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftFin, hRightFin]
          simp
          rw [crepHolWordBits_shift_toBitVec state operator
            (bitVecToHolWordBits leftValue) (bitVecToHolWordBits rightValue)]
          simp [CrepHolState.toBitVecState, CrepHolState.toRuntime,
            RiscV.panRiscVMemoryModelForEndian, panRiscVShift_eq_evalPanShiftFull,
            holWordBitsToBitVec_bitVecToHolWordBits]

theorem evalCrepRuntimeExp_crepOpMul_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (left right : CrepExp (Fin width → Bool))
    (ihLeft : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
      evalCrepHolWordBitsExp state left)
    (ihRight : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
      evalCrepHolWordBitsExp state right) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime
        (.crepOp .mul [left, right]) =
      evalCrepHolWordBitsExp state (.crepOp .mul [left, right]) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp,
    mapCrepExpWord] at ihLeft ihRight ⊢
  cases hLeft : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec left) with
  | none =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left = none := by
        simpa [hLeft] using ihLeft
      simp [hLeftFin, evalCrepHolExp, hLeft]
  | some leftValue =>
      have hLeftFin : evalCrepRuntimeExp state.toHolWordBitsRuntime left =
          some (bitVecToHolWordBits leftValue) := by
        simpa [hLeft] using ihLeft
      cases hRight : evalCrepHolExp state.toBitVecState
          (mapCrepExpWord holWordBitsToBitVec right) with
      | none =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right = none := by
            simpa [hRight] using ihRight
          simp [hLeftFin, hRightFin, evalCrepHolExp, hLeft, hRight]
      | some rightValue =>
          have hRightFin : evalCrepRuntimeExp state.toHolWordBitsRuntime right =
              some (bitVecToHolWordBits rightValue) := by
            simpa [hRight] using ihRight
          rw [hLeftFin, hRightFin]
          simp [evalCrepHolExp, hLeft, hRight, crepOpCrep]
          apply holWordBitsToBitVec_injective
          rw [holWordBitsToBitVec_mul]
          simp [holWordBitsToBitVec_bitVecToHolWordBits]

/-! Target helpers for the production evaluator relation, retaining the
    source state memory/domain fields. -/

private theorem crepHolState_load32 [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoad32 (riscvCrepWordTarget state.toRuntime) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := by
  have hmem : crepRuntimeMemoryView state.memory =
      (fun current => some (panTheWord (state.memory current))) := rfl
  rw [← hmem]
  exact crepRuntimeLoad32_wordTarget_eq_riscv (state.toRuntime) address

private theorem crepHolState_loadByte [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoadByte (riscvCrepWordTarget state.toRuntime) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs (fun current => some (panTheWord (state.memory current)))
        (BitVec.ofNat width (width / 8)) address state.bigEndian := by
  have hmem : crepRuntimeMemoryView state.memory =
      (fun current => some (panTheWord (state.memory current))) := rfl
  rw [← hmem]
  exact crepRuntimeLoadByte_wordTarget_eq_riscv (state.toRuntime) address

theorem evalCrepRuntimeExp_finiteDimension_loadByte {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (ih : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) address =
      evalCrepHolFiniteDimensionExp dimension state address) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.loadByte address) =
      evalCrepHolFiniteDimensionExp dimension state (.loadByte address) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress : evalCrepRuntimeExp
          (state.toHolFiniteWordRuntime dimension) address =
            some (bitVecToHolWord dimension value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [crepHolFiniteDimension_loadByte_toBitVec dimension state
        (bitVecToHolWord dimension value)]
      rw [crepHolState_loadByte]
      rw [← crepHolEvalMemLoadByte_eq_panModelReadByte]
      simp [holWordToBitVec_bitVecToHolWord dimension]

theorem evalCrepRuntimeExp_finiteDimension_load32 {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ) (address : CrepExp (ι → Bool))
    (ih : evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) address =
      evalCrepHolFiniteDimensionExp dimension state address) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) (.load32 address) =
      evalCrepHolFiniteDimensionExp dimension state (.load32 address) := by
  letI : HolFiniteDimension ι := dimension
  simp only [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
      (mapCrepExpWord (holWordToBitVec dimension) address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress : evalCrepRuntimeExp
          (state.toHolFiniteWordRuntime dimension) address =
            some (bitVecToHolWord dimension value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [crepHolFiniteDimension_load32_toBitVec dimension state
        (bitVecToHolWord dimension value)]
      rw [crepHolState_load32]
      rw [← crepHolEvalMemLoad32_eq_panModelRead32]
      simp [holWordToBitVec_bitVecToHolWord dimension]

private theorem mapM_evalCrepHolFiniteDimensionExp {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expressions : List (CrepExp (ι → Bool))) :
    expressions.mapM (evalCrepHolFiniteDimensionExp dimension state) =
      ((expressions.map (mapCrepExpWord (holWordToBitVec dimension))).mapM
        (evalCrepHolExp (state.toHolFiniteBitVecState dimension))).map
          (List.map (bitVecToHolWord dimension)) := by
  induction expressions with
  | nil => simp
  | cons head tail ih =>
      cases hHead : evalCrepHolExp (state.toHolFiniteBitVecState dimension)
          (mapCrepExpWord (holWordToBitVec dimension) head) with
      | none => simp [evalCrepHolFiniteDimensionExp, hHead]
      | some headValue =>
          cases hTail : List.mapM
              (evalCrepHolExp (state.toHolFiniteBitVecState dimension))
              (List.map (mapCrepExpWord (holWordToBitVec dimension)) tail) with
          | none => simp [evalCrepHolFiniteDimensionExp, hHead, hTail, ih]
          | some tailValues =>
              simp [evalCrepHolFiniteDimensionExp, hHead, hTail, ih]

/-! Complete evaluator transport for an explicitly enumerated finite
    Boolean-index word. This closes all CrepExp constructors over this Lean
    representation, while the explicit finite-dimension witness and its
    RISC-V operation interpretation remain separate from HOL's polymorphic
    type parameter. -/
theorem evalCrepRuntimeExp_finiteDimension_eq {ι : Type}
    (dimension : HolFiniteDimension ι)
    (state : CrepHolState (ι → Bool) σ)
    (expression : CrepExp (ι → Bool)) :
    evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) expression =
      evalCrepHolFiniteDimensionExp dimension state expression := by
  have evalExpsMapM (targetState : CrepRuntimeState (ι → Bool) σ) :
      ∀ expressions,
        evalCrepRuntimeExps targetState expressions =
          expressions.mapM (evalCrepRuntimeExp targetState) := by
    intro expressions
    induction expressions with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExp (state.toHolFiniteWordRuntime dimension) e =
            evalCrepHolFiniteDimensionExp dimension state e) ∧
        (∀ (state : CrepHolState (ι → Bool) σ),
          evalCrepRuntimeExps (state.toHolFiniteWordRuntime dimension) expressions =
            expressions.mapM (evalCrepHolFiniteDimensionExp dimension state))))
      generalizing state
  case const value => exact evalCrepRuntimeExp_finiteDimension_const dimension state value
  case var name => exact evalCrepRuntimeExp_finiteDimension_var dimension state name
  case load address ih => exact evalCrepRuntimeExp_finiteDimension_load dimension state address (ih state)
  case load32 address ih =>
    exact evalCrepRuntimeExp_finiteDimension_load32 dimension state address (ih state)
  case loadByte address ih =>
    exact evalCrepRuntimeExp_finiteDimension_loadByte dimension state address (ih state)
  case loadGlob address =>
    exact evalCrepRuntimeExp_finiteDimension_loadGlob dimension state address
  case op operator expressions ih =>
    apply evalCrepRuntimeExp_finiteDimension_op dimension state operator expressions
    have h := ih.2 state
    rw [mapM_evalCrepHolFiniteDimensionExp] at h
    exact h
  case crepOp operator expressions ih =>
    cases expressions with
    | nil => simp [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp,
        evalCrepHolExp, mapCrepExpWord]
    | cons head tail => cases tail with
      | nil => simp [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp,
          evalCrepHolExp, mapCrepExpWord]
      | cons second tail => cases tail with
        | nil =>
          cases operator with
          | mul =>
            exact evalCrepRuntimeExp_finiteDimension_crepOpMul dimension state head second
              (ih.1 head (by simp) state) (ih.1 second (by simp) state)
        | cons extra rest => simp [evalCrepRuntimeExp, evalCrepHolFiniteDimensionExp,
            evalCrepHolExp, mapCrepExpWord]
  case cmp operator left right ihLeft ihRight =>
    exact evalCrepRuntimeExp_finiteDimension_cmp dimension state operator left right
      (ihLeft state) (ihRight state)
  case shift operator left right ihLeft ihRight =>
    exact evalCrepRuntimeExp_finiteDimension_shift dimension state operator left right
      (ihLeft state) (ihRight state)
  case baseAddr =>
    exact evalCrepRuntimeExp_finiteDimension_baseAddr dimension state
  case topAddr =>
    exact evalCrepRuntimeExp_finiteDimension_topAddr dimension state
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state
      · exact ihTail.1 e he state
    · intro state
      simp [evalCrepRuntimeExps, ihHead state, ihTail.2 state]

/-! Flapjack-only all-constructor correspondence for the positive-width
BitVec adapter. -/
theorem evalCrepRuntimeExp_toRuntime_eq [NeZero width]
    (state : CrepHolState (RiscV.Word width) σ)
    (expression : CrepExp (RiscV.Word width)) :
    evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime) expression =
      evalCrepHolExp state expression := by
  have evalExpsMapM (targetState : CrepRuntimeState (RiscV.Word width) σ) :
      ∀ expressions,
        evalCrepRuntimeExps targetState expressions =
          expressions.mapM (evalCrepRuntimeExp targetState) := by
    intro xs
    induction xs with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepHolState (RiscV.Word width) σ),
          evalCrepRuntimeExp (riscvCrepWordTarget state.toRuntime) e =
            evalCrepHolExp state e) ∧
        (∀ (state : CrepHolState (RiscV.Word width) σ),
          evalCrepRuntimeExps (riscvCrepWordTarget state.toRuntime) expressions =
            expressions.mapM (evalCrepHolExp state))))
      generalizing state
  case const value => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case var name => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case load address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [riscvCrepWordTarget, CrepHolState.toRuntime, crepRuntimeLoad,
      panTheWord]
    rfl
  case load32 address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [crepHolState_load32, crepHolEvalMemLoad32_eq_panModelRead32]
  case loadByte address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [crepHolState_loadByte, crepHolEvalMemLoadByte_eq_panModelReadByte]
  case loadGlob address => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case op operator expressions ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [← evalExpsMapM (riscvCrepWordTarget state.toRuntime) expressions]
    rw [ih.2 state]
    simp [RiscV.panRiscVWordOp,
      wordOpHOL, wordOp,
      CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian]
  case crepOp operator expressions ih =>
    cases operator <;> cases expressions with
    | nil => simp [evalCrepRuntimeExp, evalCrepHolExp]
    | cons head tail => cases tail with
      | nil => simp [evalCrepRuntimeExp, evalCrepHolExp]
      | cons second tail => cases tail with
        | nil =>
          simp only [evalCrepRuntimeExp, evalCrepHolExp]
          rw [ih.1 head (by simp) state, ih.1 second (by simp) state]
          simp [crepOpCrep]
        | cons extra rest => simp [evalCrepRuntimeExp, evalCrepHolExp]
  case cmp operator left right ihl ihr =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ihl, ihr]
    simp [CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian, panRiscVCmp_eq_evalPanCmp]
  case shift operator left right ihl ihr =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ihl, ihr]
    simp [CrepHolState.toRuntime, riscvCrepWordTarget,
      RiscV.panRiscVMemoryModelForEndian, panRiscVShift_eq_evalPanShiftFull]
  case baseAddr => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case topAddr => simp [evalCrepRuntimeExp, evalCrepHolExp,
    riscvCrepWordTarget, CrepHolState.toRuntime]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state
      · exact ihTail.1 e he state
    · intro state
      simp [evalCrepRuntimeExps, ihHead state, ihTail.2 state]

theorem evalCrepRuntimeExp_loadByte_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : CrepExp (Fin width → Bool))
    (ih : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
      evalCrepHolWordBitsExp state address) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.loadByte address) =
      evalCrepHolWordBitsExp state (.loadByte address) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
          some (bitVecToHolWordBits value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [crepHolWordBits_loadByte_toBitVec state
        (bitVecToHolWordBits value)]
      rw [crepHolState_loadByte]
      rw [← crepHolEvalMemLoadByte_eq_panModelReadByte]
      simp [holWordBitsToBitVec_bitVecToHolWordBits]

theorem evalCrepRuntimeExp_load32_toHolWordBits [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (address : CrepExp (Fin width → Bool))
    (ih : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
      evalCrepHolWordBitsExp state address) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime (.load32 address) =
      evalCrepHolWordBitsExp state (.load32 address) := by
  simp only [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
    mapCrepExpWord] at ih ⊢
  cases hEval : evalCrepHolExp state.toBitVecState
      (mapCrepExpWord holWordBitsToBitVec address) with
  | none =>
      simp [hEval] at ih
      simp [ih]
  | some value =>
      have hAddress : evalCrepRuntimeExp state.toHolWordBitsRuntime address =
          some (bitVecToHolWordBits value) := by
        simpa [hEval] using ih
      rw [hAddress]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [crepHolWordBits_load32_toBitVec state
        (bitVecToHolWordBits value)]
      rw [crepHolState_load32]
      rw [← crepHolEvalMemLoad32_eq_panModelRead32]
      simp [holWordBitsToBitVec_bitVecToHolWordBits]

private theorem mapM_evalCrepHolWordBitsExp [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (expressions : List (CrepExp (Fin width → Bool))) :
    expressions.mapM (evalCrepHolWordBitsExp state) =
      ((expressions.map (mapCrepExpWord holWordBitsToBitVec)).mapM
        (evalCrepHolExp state.toBitVecState)).map
          (List.map bitVecToHolWordBits) := by
  induction expressions with
  | nil => simp
  | cons head tail ih =>
      cases hHead : evalCrepHolExp state.toBitVecState
          (mapCrepExpWord holWordBitsToBitVec head) with
      | none => simp [evalCrepHolWordBitsExp, hHead]
      | some headValue =>
          cases hTail : List.mapM
              (evalCrepHolExp state.toBitVecState)
              (List.map (mapCrepExpWord holWordBitsToBitVec) tail) with
          | none => simp [evalCrepHolWordBitsExp, hHead, hTail, ih]
          | some tailValues =>
              simp [evalCrepHolWordBitsExp, hHead, hTail, ih]

/-! This all-constructor theorem closes the production evaluator relation for
    the concrete finite-index Boolean representation. It is still only a
    representation-specific prerequisite: HOL quantifies over arbitrary
    finite index types and their word instances, which this theorem does not
    quantify over. -/
theorem evalCrepRuntimeExp_toHolWordBits_eq [NeZero width]
    (state : CrepHolState (Fin width → Bool) σ)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepRuntimeExp state.toHolWordBitsRuntime expression =
      evalCrepHolWordBitsExp state expression := by
  have evalExpsMapM (targetState : CrepRuntimeState (Fin width → Bool) σ) :
      ∀ expressions,
        evalCrepRuntimeExps targetState expressions =
          expressions.mapM (evalCrepRuntimeExp targetState) := by
    intro xs
    induction xs with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        (∀ e, e ∈ expressions → ∀ (state : CrepHolState (Fin width → Bool) σ),
          evalCrepRuntimeExp state.toHolWordBitsRuntime e =
            evalCrepHolWordBitsExp state e) ∧
        (∀ (state : CrepHolState (Fin width → Bool) σ),
          evalCrepRuntimeExps state.toHolWordBitsRuntime expressions =
            expressions.mapM (evalCrepHolWordBitsExp state))))
      generalizing state
  case const value =>
    simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
      mapCrepExpWord, CrepHolState.toHolWordBitsRuntime,
      CrepHolState.toBitVecState, bitVecToHolWordBits_holWordBitsToBitVec]
  case var name => exact evalCrepRuntimeExp_var_toHolWordBits state name
  case load address ih => exact evalCrepRuntimeExp_load_toHolWordBits state address (ih state)
  case load32 address ih =>
    exact evalCrepRuntimeExp_load32_toHolWordBits state address (ih state)
  case loadByte address ih =>
    exact evalCrepRuntimeExp_loadByte_toHolWordBits state address (ih state)
  case loadGlob address => exact evalCrepRuntimeExp_loadGlob_toHolWordBits state address
  case op operator expressions ih =>
    apply evalCrepRuntimeExp_op_toHolWordBits
    have h := ih.2 state
    rw [mapM_evalCrepHolWordBitsExp state expressions] at h
    exact h
  case crepOp operator expressions ih =>
    cases expressions with
    | nil => simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp,
        evalCrepHolExp, mapCrepExpWord]
    | cons head tail => cases tail with
      | nil => simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp,
          evalCrepHolExp, mapCrepExpWord]
      | cons second tail => cases tail with
        | nil =>
          cases operator with
          | mul =>
            exact evalCrepRuntimeExp_crepOpMul_toHolWordBits state head second
              (ih.1 head (by simp) state) (ih.1 second (by simp) state)
        | cons extra rest => simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp,
            evalCrepHolExp, mapCrepExpWord]
  case cmp operator left right ihLeft ihRight =>
    exact evalCrepRuntimeExp_cmp_toHolWordBits state operator left right
      (ihLeft state) (ihRight state)
  case shift operator left right ihLeft ihRight =>
    exact evalCrepRuntimeExp_shift_toHolWordBits state operator left right
      (ihLeft state) (ihRight state)
  case baseAddr =>
    simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
      mapCrepExpWord, CrepHolState.toHolWordBitsRuntime,
      CrepHolState.toBitVecState, bitVecToHolWordBits_holWordBitsToBitVec]
  case topAddr =>
    simp [evalCrepRuntimeExp, evalCrepHolWordBitsExp, evalCrepHolExp,
      mapCrepExpWord, CrepHolState.toHolWordBitsRuntime,
      CrepHolState.toBitVecState, bitVecToHolWordBits_holWordBitsToBitVec]
  case nil => simp [evalCrepRuntimeExps]
  case cons head tail ihHead ihTail =>
    constructor
    · intro e he state
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ihHead state
      · exact ihTail.1 e he state
    · intro state
      simp [evalCrepRuntimeExps, ihHead state, ihTail.2 state]

end Flapjack
