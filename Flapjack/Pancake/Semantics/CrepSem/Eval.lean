import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.WordLang

/-!
# Pancake Crepe expression evaluation

This file encodes the HOL `crepSem$state` fields without the target-only
operation and FFI-context fields carried by Flapjack's executable runtime.
The adapter below supplies the operations derived from a positive-width word
type, and the source-shaped evaluator follows `crepSem$eval_def`.
-/

namespace Flapjack

/-! HOL's polymorphic `'a word` carrier is a Boolean function indexed by the
    finite dimension type `'a`. This canonical `Fin width` representation
    exposes that carrier in Lean's core library. The conversions below use
    little-endian bit order, matching BitVec's low-bit indexing. They are
    Flapjack representation infrastructure, not a claim about the Crep
    evaluator or any HOL theorem. -/
def holWordBitsToBitVec {width : Nat} (word : Fin width → Bool) :
    BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn word)).cast (by simp)

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

/-! A dimension-indexed HOL word is isomorphic to the canonical Fin-index
    representation once its finite dimension is enumerated. Lean core/Std in
    this project does not provide Fintype/equivFin, so the enumeration data is
    represented explicitly here. This is representation infrastructure only;
    the evaluator and word-operation transport are proved separately below. -/
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

theorem holWordToBitVec_bitVecToHolWord {ι : Type u}
    (dimension : HolFiniteDimension ι) (word : BitVec dimension.width) :
    holWordToBitVec dimension (bitVecToHolWord dimension word) = word := by
  change holWordBitsToBitVec
      (holWordToFinBits dimension
        (finBitsToHolWord dimension (bitVecToHolWordBits word))) = word
  rw [holWordToFinBits_finBitsToHolWord]
  exact holWordBitsToBitVec_bitVecToHolWordBits word

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
    fun left right => RiscV.signedLess (holWordToBitVec dimension left)
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

theorem holFiniteWordToBitVec_and {ι : Type u}
    [dimension : HolFiniteDimension ι] (left right : ι → Bool) :
    holWordToBitVec dimension (AndOp.and left right) =
      AndOp.and (holWordToBitVec dimension left) (holWordToBitVec dimension right) := by
  change holWordToBitVec dimension
    (bitVecToHolWord dimension
      (AndOp.and (holWordToBitVec dimension left) (holWordToBitVec dimension right))) = _
  rw [holWordToBitVec_bitVecToHolWord]

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
    fun left right => RiscV.signedLess
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
    wordOp := fun operator values =>
      (model.wordOp operator (values.map holWordBitsToBitVec)).map
        bitVecToHolWordBits
    compare := fun operator left right => bitVecToHolWordBits
      (model.compare operator (holWordBitsToBitVec left) (holWordBitsToBitVec right))
    shift := fun operator left right =>
      (model.shift operator (holWordBitsToBitVec left) (holWordBitsToBitVec right)).map
        bitVecToHolWordBits }

/-- Flapjack's field-only encoding of HOL `crepSem$state` for a fixed
    `RiscV.Word width` carrier. Finite maps are represented extensionally by
    lookup functions. It is untagged because it does not quantify over HOL's
    arbitrary word carrier. -/
structure CrepHolState (α σ : Type u) where
  locals : Nat → Option (PanWordLab α)
  globals : BitVec 5 → Option (PanWordLab α)
  code : FunName → Option (List Nat × CrepProg α)
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  clock : Nat
  bigEndian : Bool
  ffi : FfiState σ
  baseAddress : α
  topAddress : α

/-- Exact HOL-shaped port of `crepSem$set_globals_def` (crepSemScript.sml:61)
    over the 11-field `CrepHolState`:
    `set_globals gv w s = s with globals := s.globals |+ (gv,w)`.
    The production 14-field `CrepRuntimeState` version is the separate untagged
    `setCrepRuntimeGlobals`; `setCrepHolGlobals_toRuntime` relates the two. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "set_globals_def"]
def setCrepHolGlobals (key : BitVec 5) (value : PanWordLab α)
    (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with globals := FUPDATE state.globals (key, value) }

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
    this translation agrees constructor by constructor with production. -/
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
      let memory : RiscV.Word width → Option (RiscV.Word width) :=
        fun current => some (panTheWord (state.memory current))
      (panModelRead32 (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs memory (BitVec.ofNat width (width / 8)) address
        state.bigEndian)
  | .loadByte address => do
      let address ← evalCrepHolExp state address
      let memory : RiscV.Word width → Option (RiscV.Word width) :=
        fun current => some (panTheWord (state.memory current))
      (panModelReadByte (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
        state.memaddrs memory (BitVec.ofNat width (width / 8)) address
        state.bigEndian)
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
          simp [evalCrepHolExp, hLeft, hRight]
          apply congrArg (bitVecToHolWord dimension)
          simp [holWordToBitVec_bitVecToHolWord dimension]

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
          simp [evalCrepHolExp, hLeft, hRight]
          change bitVecToHolWordBits
              (holWordBitsToBitVec (bitVecToHolWordBits leftValue) *
                holWordBitsToBitVec (bitVecToHolWordBits rightValue)) =
            bitVecToHolWordBits (leftValue * rightValue)
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
    simp [crepHolState_load32]
  case loadByte address ih =>
    simp only [evalCrepRuntimeExp, evalCrepHolExp]
    rw [ih state]
    simp [crepHolState_loadByte]
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
