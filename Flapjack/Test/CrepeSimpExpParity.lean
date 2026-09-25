import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeSimpExpParity

private def emptyHolFiniteMapExact (α β : Type) : HolFiniteMapExact α β where
  lookup := fun _ => none
  finiteSupport := ⟨[], by intro key h; simp at h⟩

private def crepSemLoadState64 : CrepSemHOLState 64 Unit :=
  { locals := emptyHolFiniteMapExact Nat (HolWordLab 64)
    globals := emptyHolFiniteMapExact (BitVec 5) (HolWordLab 64)
    code := emptyHolFiniteMapExact
      Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL 64)
    memory := fun _ => .word (BitVec.ofNat 64 0x1122334455667788)
    memaddrs := fun address => address = BitVec.ofNat 64 8
    shMemaddrs := fun _ => False
    clock := 0
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed
             ffiState := ()
             ioEvents := [] }
    baseAddr := 0
    topAddr := 0 }

private def crepSemLoadAddress64 : Fin 64 → Bool :=
  bitVecToHolWordBits (BitVec.ofNat 64 8)

/-! Direct `crepSem$eval_def`/`mem_load_def` source rows for the exact-state
Load clause: the finite-support state's stored word is returned on an address
in `memaddrs`, and an out-of-domain address returns `NONE`. The proof uses the
all-width source adapter theorem without claiming the complete native evaluator
correspondence. -/
example :
    (((evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 64))
      crepSemLoadState64.toExpressionEvaluatorState
      (.load (.const crepSemLoadAddress64))).map PanWordLab.word).map
      (mapCrepHolWordLab
        (holWordToBitVec (instFinHolFiniteDimension (width := 64))))).map
      PanWordLab.toHolWordLab =
      some (.word (BitVec.ofNat 64 0x1122334455667788)) := by
  have hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 64))
      crepSemLoadState64.toExpressionEvaluatorState
      (.const crepSemLoadAddress64) = some crepSemLoadAddress64 := by
    simp [evalCrepHolFiniteWordSourceExp]
  have hAddressBitVec : holWordToBitVec
      (instFinHolFiniteDimension (width := 64)) crepSemLoadAddress64 =
      BitVec.ofNat 64 8 := by
    change holWordBitsToBitVec
      (bitVecToHolWordBits (BitVec.ofNat 64 8)) = BitVec.ofNat 64 8
    exact holWordBitsToBitVec_bitVecToHolWordBits _
  have hDomain : crepSemLoadState64.memaddrs
      (holWordToBitVec (instFinHolFiniteDimension (width := 64))
        crepSemLoadAddress64) := by
    rw [hAddressBitVec]
    simp [crepSemLoadState64]
  exact (evalCrepSemHOLStateSource_load_eq_memLoad
    crepSemLoadState64 (.const crepSemLoadAddress64)
    crepSemLoadAddress64 hAddress).1 hDomain

example :
    (((evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 64))
      crepSemLoadState64.toExpressionEvaluatorState
      (.load (.const (bitVecToHolWordBits (BitVec.ofNat 64 9))))).map
        PanWordLab.word).map
      (mapCrepHolWordLab
        (holWordToBitVec (instFinHolFiniteDimension (width := 64))))).map
      PanWordLab.toHolWordLab = none := by
  have hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 64))
      crepSemLoadState64.toExpressionEvaluatorState
      (.const (bitVecToHolWordBits (BitVec.ofNat 64 9))) =
      some (bitVecToHolWordBits (BitVec.ofNat 64 9)) := by
    simp [evalCrepHolFiniteWordSourceExp]
  have hAddressBitVec : holWordToBitVec
      (instFinHolFiniteDimension (width := 64))
      (bitVecToHolWordBits (BitVec.ofNat 64 9)) = BitVec.ofNat 64 9 := by
    change holWordBitsToBitVec
      (bitVecToHolWordBits (BitVec.ofNat 64 9)) = BitVec.ofNat 64 9
    exact holWordBitsToBitVec_bitVecToHolWordBits _
  have hOutside : ¬ crepSemLoadState64.memaddrs
      (holWordToBitVec (instFinHolFiniteDimension (width := 64))
        (bitVecToHolWordBits (BitVec.ofNat 64 9))) := by
    rw [hAddressBitVec]
    simp [crepSemLoadState64]
  exact (evalCrepSemHOLStateSource_load_eq_memLoad
    crepSemLoadState64 (.const (bitVecToHolWordBits (BitVec.ofNat 64 9)))
    (bitVecToHolWordBits (BitVec.ofNat 64 9)) hAddress).2 hOutside

/-! The direct BitVec evaluator translation has the same exact-state Load
branch behavior, independently of the production finite-word adapter above. -/
example :
    (evalCrepHolExpWordLab crepSemLoadState64.toBitVecEvaluatorState
      (.load (.const (BitVec.ofNat 64 8)))).map PanWordLab.toHolWordLab =
      some (.word (BitVec.ofNat 64 0x1122334455667788)) := by
  have hAddress : evalCrepHolExp crepSemLoadState64.toBitVecEvaluatorState
      (crepExpOfHOL (.const (BitVec.ofNat 64 8))) =
      some (BitVec.ofNat 64 8) := by
    simp [crepExpOfHOL, evalCrepHolExp]
  simpa [crepExpOfHOL, crepSemLoadState64] using (evalCrepSemHOLStateHolEval_load_eq_memLoad
    crepSemLoadState64 (.const (BitVec.ofNat 64 8)) (BitVec.ofNat 64 8)
    hAddress).1 (by simp [crepSemLoadState64])

example :
    (evalCrepHolExpWordLab crepSemLoadState64.toBitVecEvaluatorState
      (.load (.const (BitVec.ofNat 64 9)))).map PanWordLab.toHolWordLab = none := by
  have hAddress : evalCrepHolExp crepSemLoadState64.toBitVecEvaluatorState
      (crepExpOfHOL (.const (BitVec.ofNat 64 9))) =
      some (BitVec.ofNat 64 9) := by
    simp [crepExpOfHOL, evalCrepHolExp]
  simpa [crepExpOfHOL, crepSemLoadState64] using (evalCrepSemHOLStateHolEval_load_eq_memLoad
    crepSemLoadState64 (.const (BitVec.ofNat 64 9)) (BitVec.ofNat 64 9)
    hAddress).2 (by simp [crepSemLoadState64])

/-! HOL words use a finite Boolean-function carrier. This direct check
    exercises its `Fin n` encoding and conversion to the production BitVec
    representation independently of the expression evaluator bridge. -/
def holBits4 : Fin 4 → Bool := fun index => index.val == 0 || index.val == 2

#guard holWordBitsToBitVec holBits4 == BitVec.ofNat 4 5
#guard holWordBitsToBitVec (holBits4 + holBits4) == BitVec.ofNat 4 10
#guard holWordBitsToBitVec (holBits4 * holBits4) == BitVec.ofNat 4 9

@[instance_reducible] private def fin4WordDimension :
    HolFiniteDimension (Fin 4) := inferInstance

/-! HOL word addition and multiplication are defined by `n2w` after natural
    arithmetic on `w2n`; the generic source-shaped adapters reduce to the same
    BitVec operations under the explicit finite-index enumeration. -/
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceAdd fin4WordDimension holBits4 holBits4) ==
      BitVec.ofNat 4 10
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceMul fin4WordDimension holBits4 holBits4) ==
      BitVec.ofNat 4 9
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceSub fin4WordDimension holBits4 (fun _ => true)) ==
      BitVec.ofNat 4 6

/-! These kernel checks mirror the original HOL `n2w_def` probe for zero,
    one, and the high set bit. Numeric FCP index 0 is the least-significant
    bit, as stated generally by HOL `word_index_n2w`. -/
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 0 i.val) ==
  BitVec.ofNat 8 0
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 1 i.val) ==
  BitVec.ofNat 8 1
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 128 i.val) ==
  BitVec.ofNat 8 128

example : Nat.testBit 0 0 = false := by decide
example : Nat.testBit 1 0 = true := by decide
example : Nat.testBit 1 1 = false := by decide
example : Nat.testBit 128 7 = true := by decide
example : Nat.testBit 128 6 = false := by decide

example : bitVecToHolWordBits (holWordBitsToBitVec holBits4) = holBits4 :=
  bitVecToHolWordBits_holWordBitsToBitVec holBits4

example :
    holWordBitsToBitVec (bitVecToHolWordBits (BitVec.ofNat 4 5)) =
      BitVec.ofNat 4 5 :=
  holWordBitsToBitVec_bitVecToHolWordBits (BitVec.ofNat 4 5)

/-! The general finite-dimension adapter also works when the dimension is not
    represented by `Fin` in the source theorem. Here `Bool` is explicitly
    enumerated as two indices and its word carrier is transported to BitVec. -/
@[instance_reducible] def boolWordDimension : HolFiniteDimension Bool where
  width := 2
  width_pos := by decide
  encode := fun index => if index then 1 else 0
  decode := fun index => index.val == 1
  encode_decode := by decide
  decode_encode := by decide

local instance : HolFiniteDimension Bool := boolWordDimension

/-! The arbitrary-index n2w adapter is pointwise `BIT` at the number assigned
    by the dimension encoding, matching HOL's FCP `finite_index` convention.
    The dimension decoder itself satisfies HOL's unique-in-range property. -/
#guard holFiniteWordN2W boolWordDimension 1 false == true
#guard holFiniteWordN2W boolWordDimension 1 true == false
#guard holFiniteWordN2W boolWordDimension 2 true == true

example (value : Bool) :
    ∃ index, index < boolWordDimension.width ∧
      holFiniteIndex boolWordDimension index = value ∧
      ∀ other, other < boolWordDimension.width →
        holFiniteIndex boolWordDimension other = value → other = index :=
  holFiniteIndex_bijective boolWordDimension value

example (value index : Nat) (hindex : index < boolWordDimension.width) :
    holFiniteWordN2W boolWordDimension value
        (holFiniteIndex boolWordDimension index) = Nat.testBit value index :=
  holFiniteWordN2W_at_finiteIndex boolWordDimension value index hindex

example (word : Bool → Bool) :
    holFiniteWordW2N boolWordDimension word =
      finWordSBitSum boolWordDimension.width
        (fun index => word (holFiniteIndex boolWordDimension index.val)) :=
  holFiniteWordW2N_eq_finiteIndexSBitSum boolWordDimension word

@[instance_reducible] def boolWordDimensionSwapped : HolFiniteDimension Bool where
  width := 2
  width_pos := by decide
  encode := fun index => if index then 0 else 1
  decode := fun index => index.val == 0
  encode_decode := by decide
  decode_encode := by decide

example (value : Bool) :
    ∃ index, index < boolWordDimensionSwapped.width ∧
      holFiniteIndex boolWordDimensionSwapped index = value ∧
      ∀ other, other < boolWordDimensionSwapped.width →
        holFiniteIndex boolWordDimensionSwapped other = value → other = index :=
  holFiniteIndex_bijective boolWordDimensionSwapped value

example (value index : Nat) (hindex : index < boolWordDimensionSwapped.width) :
    holFiniteWordN2W boolWordDimensionSwapped value
        (holFiniteIndex boolWordDimensionSwapped index) = Nat.testBit value index :=
  holFiniteWordN2W_at_finiteIndex boolWordDimensionSwapped value index hindex

/-! Both witnesses satisfy HOL's finite_index bijection property, while they
    encode different dictionaries: `n2w 1` changes when the index order is
    permuted. The all-width proof works under either dictionary; the exact HOL
    instance for a concrete index type still needs to be identified. -/
example :
    bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1) ≠
      bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1) := by
  intro h
  have hFalse := congrFun h false
  have hleft :
      bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1) false = true := by decide
  have hright :
      bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1) false = false := by decide
  rw [hleft, hright] at hFalse
  cases hFalse

def boolDimensionWord : Bool → Bool := id
def boolDimensionOne : Bool → Bool :=
  bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1)

/-! The generic finite-word comparison instance handles signed order from the
    source word encoding: the 2-bit value 2 (two's-complement -2) is below 1. -/
#guard PanCmp.less boolDimensionWord boolDimensionOne
#guard holWordToBitVec boolWordDimension
  (evalPanCmp .less boolDimensionWord boolDimensionOne) == BitVec.ofNat 2 1

/-! Generic finite-dimension `dest_2exp` support is checked on Bool-indexed
    words, in addition to the existing BitVec fixture. These remain support
    instances under this explicit enumeration, not HOL tags. -/
example : crepDest2Exp 0 boolDimensionWord = some 1 := by decide +kernel

example : 1 < boolWordDimension.width :=
  crepDest2ExpHolFiniteDimension_lt_width boolWordDimension
    boolDimensionWord 1 (by decide +kernel)

example : boolDimensionWord = ShiftLeft.shiftLeft (1 : Bool → Bool)
    (bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1)) :=
  crepDest2ExpHolFiniteDimension_eq_shift boolWordDimension
    boolDimensionWord 1 (by decide +kernel)

example : boolDimensionWord = bitVecToHolWord boolWordDimension
    (BitVec.shiftLeft (holWordToBitVec boolWordDimension (1 : Bool → Bool)) 1) :=
  crepDest2ExpHolFiniteDimension_eq_lsl boolWordDimension
    boolDimensionWord 1 (by decide +kernel)

example (word : Bool → Bool) (exponent : Nat) (hbound : exponent < 2) :
    holWordToBitVec boolWordDimension
        (ShiftLeft.shiftLeft word
          (bitVecToHolWord boolWordDimension (BitVec.ofNat 2 exponent))) =
      BitVec.shiftLeft (holWordToBitVec boolWordDimension word) exponent :=
  holFiniteDimension_wordLsl_toBitVec boolWordDimension word exponent hbound

#guard wordOp .add [] == some (0 : Bool → Bool)
#guard wordOp .and [] == some (Complement.complement (0 : Bool → Bool))
#guard wordOp .or [] == some (0 : Bool → Bool)
#guard wordOp .xor [] == some (0 : Bool → Bool)
#guard wordOp .sub [boolDimensionWord] == none
#guard wordOp .sub [boolDimensionWord, boolDimensionWord, boolDimensionWord] == none

example (operator : BinOp) (values : List (Bool → Bool)) :
    wordOp operator values =
      (wordOpHOL operator (values.map (holWordToBitVec boolWordDimension))).map
        (bitVecToHolWord boolWordDimension) :=
  holFiniteWord_wordOp_toBitVec boolWordDimension operator values

/-! The source `word_sh` contract is width-generic. This theorem checks all
    four operators for arbitrary Bool-index operands; the HOL-generated probe
    below records the zero, maximum-valid, width, and above-width boundaries. -/
example (operator : Shift) (left right : Bool → Bool) :
    evalPanShiftFull operator left right =
      (evalPanShiftFull operator (holWordToBitVec boolWordDimension left)
        (holWordToBitVec boolWordDimension right)).map
          (bitVecToHolWord boolWordDimension) :=
  holFiniteWord_evalPanShift_toBitVec boolWordDimension operator left right

def boolDimensionZero : Bool → Bool :=
  bitVecToHolWord boolWordDimension (BitVec.ofNat 2 0)

#guard (evalPanShiftFull .lsl boolDimensionWord boolDimensionZero).isSome
#guard (evalPanShiftFull .lsl boolDimensionWord boolDimensionWord).isSome == false

#guard holFiniteWordSBitSum boolWordDimension boolDimensionWord == 2

example : holFiniteWordW2N boolWordDimension boolDimensionWord = 2 := by
  rw [holFiniteWordW2N_eq_SBitSum]
  rfl

example : bitVecToHolWord boolWordDimension
    (holWordToBitVec boolWordDimension boolDimensionWord) = boolDimensionWord :=
  bitVecToHolWord_holWordToBitVec boolWordDimension boolDimensionWord

example : holWordToBitVec boolWordDimension
    (bitVecToHolWord boolWordDimension (BitVec.ofNat 2 2)) = BitVec.ofNat 2 2 :=
  holWordToBitVec_bitVecToHolWord boolWordDimension (BitVec.ofNat 2 2)

def boolDimensionSimplifiedMultiply : CrepExp (Bool → Bool) := by
  letI : HolFiniteDimension Bool := boolWordDimension
  exact crepSimpExp (fun value =>
    bitVecToHolWord boolWordDimension (BitVec.ofNat 2 value))
    (.crepOp .mul [.var 0, .const (boolDimensionWord)])

def boolDimensionSimplifyHasExpectedShift : Bool :=
  match boolDimensionSimplifiedMultiply with
  | .shift .lsl (.var 0) (.const value) =>
      holWordToBitVec boolWordDimension value == BitVec.ofNat 2 1
  | _ => false

#guard boolDimensionSimplifyHasExpectedShift

def boolDimensionHolState : CrepHolState (Bool → Bool) Unit where
  locals := fun name => if name == 0 then some (.word boolDimensionWord) else none
  globals := fun address => if address == 0 then some (.word boolDimensionWord) else none
  code := fun _ => none
  memory := fun _ => .word boolDimensionWord
  memaddrs := fun _ => true
  shMemaddrs := fun _ => false
  clock := 10
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := boolDimensionWord
  topAddress := boolDimensionWord

#guard evalCrepRuntimeExp
    (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.var 0) ==
      some boolDimensionWord
#guard evalCrepRuntimeExp
    (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.loadGlob 0) ==
      some boolDimensionWord

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.var 0) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState (.var 0) :=
  evalCrepRuntimeExp_finiteDimension_var boolWordDimension boolDimensionHolState 0

/-- The arbitrary-index source evaluator's full `Word` result agrees with the
direct BitVec state evaluator through a noncanonical Bool-index dimension,
for both a local hit and a local miss. -/
example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.var 0)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.var 0) :=
  evalCrepHolFiniteWordSourceExp_var_toHolEval
    boolWordDimension boolDimensionHolState 0

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      { boolDimensionHolState with locals := fun _ => none }
      (.var 0)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        ({ boolDimensionHolState with locals := fun _ => none }
          |>.toHolFiniteBitVecState boolWordDimension)
        (.var 0) :=
  evalCrepHolFiniteWordSourceExp_var_toHolEval
    boolWordDimension { boolDimensionHolState with locals := fun _ => none } 0

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.loadGlob 0)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.loadGlob 0) :=
  evalCrepHolFiniteWordSourceExp_loadGlob_toHolEval
    boolWordDimension boolDimensionHolState 0

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState .baseAddr).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        .baseAddr :=
  evalCrepHolFiniteWordSourceExp_baseAddr_toHolEval
    boolWordDimension boolDimensionHolState

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState .topAddr).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        .topAddr :=
  evalCrepHolFiniteWordSourceExp_topAddr_toHolEval
    boolWordDimension boolDimensionHolState

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.const boolDimensionZero)).map PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.const (holWordToBitVec boolWordDimension boolDimensionZero)) :=
  evalCrepHolFiniteWordSourceExp_const_toHolEval
    boolWordDimension boolDimensionHolState boolDimensionZero

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.load (.const boolDimensionZero))).map
        PanWordLab.word).map (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.load (.const (holWordToBitVec boolWordDimension boolDimensionZero))) := by
  have hAddress :
      (evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
        (.const boolDimensionZero)).map (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension)
          (.const boolDimensionZero)) := by
    simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
  simpa [mapCrepExpWord] using evalCrepHolFiniteWordSourceExp_load_toHolEval
    boolWordDimension boolDimensionHolState (.const boolDimensionZero) hAddress

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (.op .add [.const boolDimensionWord, .const boolDimensionOne])).map
        PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.op .add
          [.const (holWordToBitVec boolWordDimension boolDimensionWord),
           .const (holWordToBitVec boolWordDimension boolDimensionOne)]) := by
  have hChildren : ∀ expression,
      expression ∈ [.const boolDimensionWord, .const boolDimensionOne] →
      (evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
        expression).map (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension) expression) := by
    intro expression hMember
    simp only [List.mem_cons, List.not_mem_nil] at hMember
    rcases hMember with hMember | hMember | hMember
    · subst expression
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
    · subst expression
      simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
    · contradiction
  simpa [mapCrepExpWord] using evalCrepHolFiniteWordSourceExp_op_toHolEval
    boolWordDimension boolDimensionHolState .add
    [.const boolDimensionWord, .const boolDimensionOne] hChildren

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord))).map
        PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.cmp .equal (.const (holWordToBitVec boolWordDimension boolDimensionWord))
          (.const (holWordToBitVec boolWordDimension boolDimensionWord))) := by
  have hChild : (evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.const boolDimensionWord)).map
        (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension)
          (.const boolDimensionWord)) := by
    simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
  simpa [mapCrepExpWord] using evalCrepHolFiniteWordSourceExp_cmp_toHolEval
    boolWordDimension boolDimensionHolState .equal (.const boolDimensionWord)
    (.const boolDimensionWord) hChild hChild

/-- At width one, shifting by the word value one fails in both evaluators;
the bridge therefore preserves the full `Option` failure case too. -/
example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (.shift .lsl (.const boolDimensionWord) (.const boolDimensionWord))).map
        PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.shift .lsl
          (.const (holWordToBitVec boolWordDimension boolDimensionWord))
          (.const (holWordToBitVec boolWordDimension boolDimensionWord))) := by
  have hChild : (evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.const boolDimensionWord)).map
        (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension)
          (.const boolDimensionWord)) := by
    simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
  simpa [mapCrepExpWord] using evalCrepHolFiniteWordSourceExp_shift_toHolEval
    boolWordDimension boolDimensionHolState .lsl (.const boolDimensionWord)
    (.const boolDimensionWord) hChild hChild

example :
    ((evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (.crepOp .mul [.const boolDimensionWord, .const boolDimensionOne])).map
        PanWordLab.word).map
        (mapCrepHolWordLab (holWordToBitVec boolWordDimension)) =
      evalCrepHolExpWordLab
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (.crepOp .mul
          [.const (holWordToBitVec boolWordDimension boolDimensionWord),
           .const (holWordToBitVec boolWordDimension boolDimensionOne)]) := by
  have hLeft : (evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.const boolDimensionWord)).map
        (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension)
          (.const boolDimensionWord)) := by
    simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
  have hRight : (evalCrepHolFiniteWordSourceExp boolWordDimension
      boolDimensionHolState (.const boolDimensionOne)).map
        (holWordToBitVec boolWordDimension) =
      evalCrepHolExp
        (boolDimensionHolState.toHolFiniteBitVecState boolWordDimension)
        (mapCrepExpWord (holWordToBitVec boolWordDimension)
          (.const boolDimensionOne)) := by
    simp [evalCrepHolFiniteWordSourceExp, evalCrepHolExp, mapCrepExpWord]
  simpa [mapCrepExpWord] using
    evalCrepHolFiniteWordSourceExp_crepOpMul_toHolEval
      boolWordDimension boolDimensionHolState
      (.const boolDimensionWord) (.const boolDimensionOne) hLeft hRight

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.loadGlob 0) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState (.loadGlob 0) :=
  evalCrepRuntimeExp_finiteDimension_loadGlob
    boolWordDimension boolDimensionHolState 0

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

/-! The Op case of `simp_exp_correct1` applies to every word operation and
    obtains one induction hypothesis for each argument expression. Exercise
    the exact HOL-word source evaluator with a successful two-argument Add;
    the recursive children use the tagged Const case above. -/
example :
    evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) ≠ none := by
  simp [evalCrepHolFiniteWordSourceExp, holFiniteWordSourceMemoryModel,
    wordOpHOL, wordOp]

example :
    evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.op .add [.const boolDimensionWord, .const boolDimensionWord])) =
      evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        boolDimensionHolState
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) := by
  apply crepSimpExpCorrect1OpHolFiniteWordSourceCase
  · exact .word boolDimensionWord
  · simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holFiniteWordSourceMemoryModel,
      wordOpHOL, wordOp]
  · intro child hmem source result hsuccess
    have hchild : child = .const boolDimensionWord := by
      simpa using hmem
    subst child
    exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
      (f := fun (_, entry) => entry) source boolDimensionWord result hsuccess

/-! The recursive Cmp case preserves the full source-evaluator result under an
    arbitrary code-map update. This exercises the all-width support theorem
    independently of the separate native HOL evaluator correspondence. -/
example :
    evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord))) =
      evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        boolDimensionHolState
        (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord)) := by
  apply crepSimpExpCorrect1CmpHolFiniteWordSourceCase
  · exact .word boolDimensionWord
  · simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holFiniteWordSourceMemoryModel]
  · intro child hmem source result hsuccess
    simp only [List.mem_cons] at hmem
    rcases hmem with hleft | htail
    · have hshape : child = .const boolDimensionWord := by simpa using hleft
      subst child
      exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
        (f := fun (_, entry) => entry) source boolDimensionWord result hsuccess
    · rcases htail with hright | hnil
      · have hshape : child = .const boolDimensionWord := by simpa using hright
        subst child
        exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
          (f := fun (_, entry) => entry) source boolDimensionWord result hsuccess
      · cases hnil

/-! The all-width Shift case preserves successful shift evaluation under the
    same arbitrary code-map update, using the successful left-shift-by-zero
    fixture and the recursive Const case for its children. -/
example :
    evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.shift .lsl (.const boolDimensionWord) (.const boolDimensionZero))) =
      evalCrepHolFiniteWordSourceExpWordLab boolWordDimension
        boolDimensionHolState
        (.shift .lsl (.const boolDimensionWord) (.const boolDimensionZero)) := by
  apply crepSimpExpCorrect1ShiftHolFiniteWordSourceCase
  · exact .word boolDimensionWord
  · simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holFiniteWordSourceMemoryModel,
      wordShiftHOL, boolDimensionWord, boolDimensionZero,
      holWordToBitVec_bitVecToHolWord]
  · intro child hmem source result hsuccess
    simp only [List.mem_cons] at hmem
    rcases hmem with hleft | htail
    · have hshape : child = .const boolDimensionWord := by simpa using hleft
      subst child
      exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
        (f := fun (_, entry) => entry) source boolDimensionWord result hsuccess
    · rcases htail with hright | hnil
      · have hshape : child = .const boolDimensionZero := by simpa using hright
        subst child
        exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
          (f := fun (_, entry) => entry) source boolDimensionZero result hsuccess
      · cases hnil

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.shift .lsl (.const boolDimensionWord) (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.shift .lsl (.const boolDimensionWord) (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.loadByte (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.loadByte (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.load32 (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.load32 (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (crepMulConst
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.const boolDimensionWord) boolDimensionWord) =
      some (boolDimensionWord * boolDimensionWord) := by
  exact crepEvalMulConstHolFiniteDimension boolWordDimension boolDimensionHolState
    (.const boolDimensionWord) boolDimensionWord boolDimensionWord
    (by simp [evalCrepRuntimeExp])

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])) =
      evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
  exact crepSimpExpEvalPreservesHolFiniteDimension boolWordDimension
    boolDimensionHolState _ (by simp [evalCrepRuntimeExp, crepOpCrep])

example :
    (evalCrepRuntimeExp
      (crepArithMapCode (fun (_, entry) => entry)
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension))
      (crepSimpExp
        (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]))).map
        PanWordLab.word =
      (evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
        PanWordLab.word := by
  exact crepSimpExpCorrect1HolFiniteDimension (fun (_, entry) => entry)
    boolDimensionHolState _
    (by simp [evalCrepRuntimeExp, crepOpCrep])

example :
    evalCrepHolFiniteDimensionExpWordLab boolWordDimension
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])) =
      evalCrepHolFiniteDimensionExpWordLab boolWordDimension boolDimensionHolState
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
  apply crepSimpExpCorrect1HolFiniteDimensionSource (fun (_, entry) => entry)
    boolDimensionHolState _
  have hEval := evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState
      (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])
  change (evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
    (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
      PanWordLab.word ≠ none
  rw [← hEval]
  simp [evalCrepRuntimeExp, crepOpCrep]

example :
    (evalCrepRuntimeExp
      (CrepHolState.toHolFiniteWordSourceRuntime boolWordDimension
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState))
      (crepSimpExp
        (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]))).map
        PanWordLab.word =
    (evalCrepRuntimeExp
      (boolDimensionHolState.toHolFiniteWordSourceRuntime boolWordDimension)
      (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
        PanWordLab.word := by
  apply crepSimpExpCorrect1HolFiniteWordSource (fun (_, entry) => entry)
    boolDimensionHolState _
  simp [evalCrepRuntimeExp, crepOpCrep]

/-! Instantiate the complete successful-result theorem at the non-`Fin`
    Bool index carrier. The premise remains universally supplied, matching
    HOL's conditional result statement rather than fixing a single output. -/
example (value : PanWordLab (Bool → Bool))
    (h : (evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (.crepOp .mul [.var 0, .const boolDimensionWord])).map PanWordLab.word =
        some value) :
    (evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
      (crepSimpExp
        (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
        (.crepOp .mul [.var 0, .const boolDimensionWord]))).map PanWordLab.word =
      some value := by
  exact @crepSimpExpCorrectHolFiniteWordSourceEvalClass Bool Unit
    boolWordDimension (fun (_, entry) => entry) boolDimensionHolState
    (.crepOp .mul [.var 0, .const boolDimensionWord]) value h

/-! The all-width full-result theorem also proves a concrete simplification
    over a different valid finite_index dictionary for Bool. This does not
    claim that the swapped dictionary is HOL's ambient Bool instance. -/
section SwappedFiniteIndex

local instance : HolFiniteDimension Bool := boolWordDimensionSwapped

example :
    evalCrepHolFiniteWordSourceExpWordLab boolWordDimensionSwapped
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 n))
          (.crepOp .mul
            [.const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1)),
             .const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 2))])) =
    evalCrepHolFiniteWordSourceExpWordLab boolWordDimensionSwapped
      boolDimensionHolState
      (.crepOp .mul
        [.const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1)),
         .const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 2))]) := by
  have hsuccess :
      evalCrepHolFiniteWordSourceExpWordLab boolWordDimensionSwapped
        boolDimensionHolState
        (.crepOp .mul
          [.const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1)),
           .const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 2))]) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holFiniteWordSourceCrepOp,
      holFiniteWordSourceMul]
  exact @crepSimpExpCorrect1HolFiniteWordSourceWordLab Bool Unit
    boolWordDimensionSwapped (fun (_, entry) => entry) boolDimensionHolState
    (.crepOp .mul
      [.const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1)),
       .const (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 2))])
    (.word (bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 2))) hsuccess

end SwappedFiniteIndex

example : True := by
  letI : HolFiniteDimension Bool := boolWordDimensionSwapped
  have hresult :
      evalCrepHolFiniteDimensionExpWordLab boolWordDimensionSwapped
          (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
            boolDimensionHolState)
          (crepSimpExp
            (fun n => bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 n))
            (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])) =
        evalCrepHolFiniteDimensionExpWordLab boolWordDimensionSwapped
          boolDimensionHolState
          (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
    apply crepSimpExpCorrect1HolFiniteDimensionSource (fun (_, entry) => entry)
      boolDimensionHolState _
    have hEval := evalCrepRuntimeExp_finiteDimension_eq boolWordDimensionSwapped
      boolDimensionHolState
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])
    change (evalCrepHolFiniteDimensionExp boolWordDimensionSwapped
      boolDimensionHolState
      (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
        PanWordLab.word ≠ none
    rw [← hEval]
    simp [evalCrepRuntimeExp, crepOpCrep]
  exact True.intro

#guard crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat 4 value))
    (.crepOp .mul [.var 2, .const (bitVecToHolWordBits (BitVec.ofNat 4 2))]) ==
  .shift .lsl (.var 2) (.const (bitVecToHolWordBits (BitVec.ofNat 4 1)))

def holWordBitsState4 : CrepHolState (Fin 4 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word holBits4
  memaddrs := fun _ => false
  shMemaddrs := fun _ => false
  clock := 0
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holBits4
  topAddress := holBits4

def holWordBitsVarState4 (value : Fin 4 → Bool) :
    CrepHolState (Fin 4 → Bool) Unit :=
  { holWordBitsState4 with locals := fun _ => some (.word value) }

def holWordBitsGlobalState4 (value : Fin 4 → Bool) :
    CrepHolState (Fin 4 → Bool) Unit :=
  { holWordBitsState4 with globals := fun _ => some (.word value) }

def holWordBitsLoadState4 (value : Fin 4 → Bool) :
    CrepHolState (Fin 4 → Bool) Unit :=
  { holWordBitsState4 with
    memory := fun _ => .word value
    memaddrs := fun _ => true }

example (value : Fin 4 → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        (holWordBitsLoadState4 value))
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
        (.load (.const value))) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsLoadState4 value) (.load (.const value)) := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsLoadState4 value) (.load (.const value)) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holWordBitsLoadState4,
      holWordBitsState4]
  have ih : ∀ (source : CrepHolState (Fin 4 → Bool) Unit)
      (_result : PanWordLab (Fin 4 → Bool)),
      evalCrepHolFiniteWordSourceExpWordLab
          (instFinHolFiniteDimension (width := 4)) source (.const value) ≠ none →
      evalCrepHolFiniteWordSourceExpWordLab
          (instFinHolFiniteDimension (width := 4))
          (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry) source)
          (crepSimpExp
            (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
              (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n)) (.const value)) =
        evalCrepHolFiniteWordSourceExpWordLab
          (instFinHolFiniteDimension (width := 4)) source (.const value) := by
    intro source result h
    exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
      (f := fun (_, entry) => entry) source value result h
  exact crepSimpExpCorrect1LoadHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (holWordBitsLoadState4 value)
    (.const value) (.word value) hsuccess ih

private theorem constSourceCaseIH {ι : Type} {σ : Type}
    [dimension : HolFiniteDimension ι]
    (f : FunName × (List Nat × CrepProg (ι → Bool)) →
      List Nat × CrepProg (ι → Bool)) (value : ι → Bool) :
    ∀ (source : CrepHolState (ι → Bool) σ) (_result : PanWordLab (ι → Bool)),
      evalCrepHolFiniteWordSourceExpWordLab dimension source (.const value) ≠ none →
      evalCrepHolFiniteWordSourceExpWordLab dimension
        (crepArithHolFiniteDimensionMapCode f source)
        (crepSimpExp
          (fun n => bitVecToHolWord dimension (BitVec.ofNat dimension.width n))
          (.const value)) =
        evalCrepHolFiniteWordSourceExpWordLab dimension source (.const value) := by
  intro source result h
  exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase f source value result h

/-! The hard all-width `Crepop Mul` constructor case is instantiated over a
    four-bit HOL word carrier. The original HOL probe records the same
    `mul_const` shift rewrite (`mul_eight_shape`); this local fixture checks
    the source evaluator before and after simplification and applies the named
    case theorem using only the `Var` and `Const` constructor hypotheses. -/
example :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        (holWordBitsVarState4 holBits4))
      (crepSimpExp
        (fun n => bitVecToHolWord
          (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
        (.crepOp .mul [.var 2, .const (bitVecToHolWordBits (BitVec.ofNat 4 2))])) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsVarState4 holBits4)
      (.crepOp .mul [.var 2, .const (bitVecToHolWordBits (BitVec.ofNat 4 2))]) := by
  let dimension := instFinHolFiniteDimension (width := 4)
  let source := holWordBitsVarState4 holBits4
  let fromNat := fun n => bitVecToHolWord dimension
    (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n)
  let left : CrepExp (Fin 4 → Bool) := .var 2
  let right : CrepExp (Fin 4 → Bool) :=
    .const (bitVecToHolWordBits (BitVec.ofNat 4 2))
  let f : FunName × (List Nat × CrepProg (Fin 4 → Bool)) →
      List Nat × CrepProg (Fin 4 → Bool) := fun (_, entry) => entry
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab dimension source
      (.crepOp .mul [left, right]) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, source, left, right,
      holWordBitsVarState4, holFiniteWordSourceCrepOp,
      holFiniteWordSourceMul]
  have ih : ∀ (subexpression : CrepExp (Fin 4 → Bool)),
      subexpression ∈ [left, right] →
      ∀ (state : CrepHolState (Fin 4 → Bool) Unit)
        (_value : PanWordLab (Fin 4 → Bool)),
        evalCrepHolFiniteWordSourceExpWordLab dimension state subexpression ≠ none →
        evalCrepHolFiniteWordSourceExpWordLab dimension
          (crepArithHolFiniteDimensionMapCode f state)
          (crepSimpExp fromNat subexpression) =
        evalCrepHolFiniteWordSourceExpWordLab dimension state subexpression := by
    intro subexpression hmem state value hvalue
    simp only [List.mem_cons] at hmem
    rcases hmem with hleft | htail
    · subst subexpression
      exact crepSimpExpCorrect1VarHolFiniteWordSourceCase
        f state 2 value hvalue
    · rcases htail with hright | hnil
      · subst subexpression
        exact crepSimpExpCorrect1ConstHolFiniteWordSourceCase
          f state (bitVecToHolWordBits (BitVec.ofNat 4 2)) value hvalue
      · cases hnil
  exact crepSimpExpCorrect1CrepOpHolFiniteWordSourceCase
    (dimension := dimension) f source .mul [left, right] (.word holBits4)
    hsuccess ih

example (address : BitVec 5) (value : Fin 4 → Bool) :
    evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsGlobalState4 value) (.loadGlob address) =
    evalCrepHolFiniteDimensionExp
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsGlobalState4 value) (.loadGlob address) := by
  exact evalCrepHolFiniteWordSourceExp_loadGlob_eq_finiteDimension
    (instFinHolFiniteDimension (width := 4))
    (holWordBitsGlobalState4 value) address

example (value : Fin 4 → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsState4)
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
        (.const value)) = some (.word value) := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4
      (.const value) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp]
  have hcase := crepSimpExpCorrect1ConstHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsState4)
    value (.word value) hsuccess
  have hvalue : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4
      (.const value) = some (.word value) := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp]
  calc
    evalCrepHolFiniteWordSourceExpWordLab
        (instFinHolFiniteDimension (width := 4))
        (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
          holWordBitsState4)
        (crepSimpExp
          (fun n => bitVecToHolWord
            (instFinHolFiniteDimension (width := 4))
            (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
          (.const value)) =
      evalCrepHolFiniteWordSourceExpWordLab
        (instFinHolFiniteDimension (width := 4)) holWordBitsState4
        (.const value) := hcase
    _ = some (.word value) := hvalue

example (name : Nat) (value : Fin 4 → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        (holWordBitsVarState4 value))
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
        (.var name)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) (holWordBitsVarState4 value)
      (.var name) := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) (holWordBitsVarState4 value)
      (.var name) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holWordBitsVarState4]
  exact crepSimpExpCorrect1VarHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsVarState4 value)
    name (.word value) hsuccess

example (address : BitVec 5) (value : Fin 4 → Bool) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        (holWordBitsGlobalState4 value))
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n))
        (.loadGlob address)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsGlobalState4 value) (.loadGlob address) := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (holWordBitsGlobalState4 value) (.loadGlob address) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, holWordBitsGlobalState4]
  exact crepSimpExpCorrect1LoadGlobHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsGlobalState4 value)
    address (.word value) hsuccess

example :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsState4)
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n)) .baseAddr) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4 .baseAddr := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4 .baseAddr ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp]
  exact crepSimpExpCorrect1BaseAddrHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsState4)
    (.word holBits4) hsuccess

example :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsState4)
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 4))
          (BitVec.ofNat (HolFiniteDimension.width (Fin 4)) n)) .topAddr) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4 .topAddr := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 4)) holWordBitsState4 .topAddr ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp]
  exact crepSimpExpCorrect1TopAddrHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsState4)
    (.word holBits4) hsuccess

def holWordBits64 (value : Nat) : Fin 64 → Bool :=
  bitVecToHolWordBits (BitVec.ofNat 64 value)

def holWordBitsState64 : CrepHolState (Fin 64 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word (holWordBits64 0x0807060504030201)
  memaddrs := fun address => address == holWordBits64 8
  shMemaddrs := fun _ => false
  clock := 0
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holWordBits64 0
  topAddress := holWordBits64 0

def holWordBitsMemoryEverywhereState64 : CrepHolState (Fin 64 → Bool) Unit :=
  { holWordBitsState64 with memaddrs := fun _ => true }

/-! Successful load cases reuse a 64-bit little-endian memory cell. The domain
    is total here so the constructor cases exercise the byte operations without
    adding an address-domain side condition. -/
example :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 64))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsMemoryEverywhereState64)
      (crepSimpExp
        (fun n => bitVecToHolWord (instFinHolFiniteDimension (width := 64))
          (BitVec.ofNat 64 n))
        (.loadByte (.const (0 : Fin 64 → Bool)))) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
      (.loadByte (.const (0 : Fin 64 → Bool))) := by
  have hsuccess : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
    (.loadByte (.const (holWordBits64 0))) ≠ none := by
    simp [evalCrepHolFiniteWordSourceExpWordLab,
      evalCrepHolFiniteWordSourceExp, crepHolEvalMemLoadByte,
      holFiniteWordSourceMemoryModel, holFiniteWordSourceByteAlign,
      holByteAlignBitVec,
      holWordBitsMemoryEverywhereState64, holWordBitsState64, holWordBits64]
  exact crepSimpExpCorrect1LoadByteHolFiniteWordSourceCase
    (f := fun (_, entry) => entry) (state := holWordBitsMemoryEverywhereState64)
    (.const (0 : Fin 64 → Bool)) (.word (holWordBits64 1)) hsuccess
    (constSourceCaseIH (fun (_, entry) => entry) (0 : Fin 64 → Bool))

#guard evalCrepHolFiniteWordSourceExp
    (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
    (.load32 (.const (0 : Fin 64 → Bool))) == some (holWordBits64 0x04030201)
#guard evalCrepHolFiniteWordSourceExp
    (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
    (.loadByte (.const (0 : Fin 64 → Bool))) == some (holWordBits64 1)

def holWordBitsState64WithLocal : CrepHolState (Fin 64 → Bool) Unit :=
  { holWordBitsState64 with
    locals := fun name =>
      if name == 2 then some (.word (holWordBits64 5)) else none }

def holWordBitsCmpResult (operator : Cmp) (left right : Nat) :
    Option (PanWordLab (Fin 64 → Bool)) :=
  (evalCrepRuntimeExp
    (holWordBitsState64.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    (.cmp operator (.const (holWordBits64 left)) (.const (holWordBits64 right)))).map
      PanWordLab.word

/-! The corresponding original HOL probe exercises all eight `word_cmp`
    constructors through `crepSem$eval`. These guards run the production
    source runtime on the same RV64 word cases, including signed-vs-unsigned
    order and overlapping/disjoint bit tests. -/
#guard holWordBitsCmpResult .equal 5 5 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .equal 5 6 == some (.word (holWordBits64 0))
#guard holWordBitsCmpResult .lower 3 5 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .less 0xFFFFFFFFFFFFFFFF 1 ==
  some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notEqual 5 6 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notLower 5 3 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notLess 1 0xFFFFFFFFFFFFFFFF ==
  some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .test 0xF0 0x10 == some (.word (holWordBits64 0))
#guard holWordBitsCmpResult .test 0xF0 0x0F == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notTest 0xF0 0x10 == some (.word (holWordBits64 1))

/-! Direct `word_sh_def` parity against the HOL observations in
`crep_eval_shift_rv64_probe.out`, including the zero-amount and width-bound
cases. -/
#guard wordShiftHOL .lsl (BitVec.ofNat 64 1) 3 == some (BitVec.ofNat 64 8)
#guard wordShiftHOL .lsr (BitVec.ofNat 64 16) 2 == some (BitVec.ofNat 64 4)
#guard wordShiftHOL .asr (BitVec.ofNat 64 0x8000000000000000) 4 ==
  some (BitVec.ofNat 64 0xF800000000000000)
#guard wordShiftHOL .ror (BitVec.ofNat 64 1) 1 ==
  some (BitVec.ofNat 64 0x8000000000000000)
#guard wordShiftHOL .lsl (BitVec.ofNat 64 7) 0 == some (BitVec.ofNat 64 7)
#guard wordShiftHOL .lsl (BitVec.ofNat 64 7) 64 == none

def holWordBitsMulEight : CrepExp (Fin 64 → Bool) :=
  .crepOp .mul [.var 2, .const (holWordBits64 8)]

def holWordBitsMulEightSimplified : CrepExp (Fin 64 → Bool) :=
  crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat 64 value))
    holWordBitsMulEight

/-! The HOL fixture evaluates the same local-times-eight expression before
    and after `simp_exp`; both results are `SOME (Word 40w)`. These guards
    exercise that original result through production evaluation configured
    with the source memory model, not just the simplifier's output shape. -/
#guard holWordBitsMulEightSimplified ==
  .shift .lsl (.var 2) (.const (holWordBits64 3))
#guard (evalCrepRuntimeExp
    (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    holWordBitsMulEight).map PanWordLab.word ==
  some (.word (holWordBits64 40))
#guard (evalCrepRuntimeExp
    (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    holWordBitsMulEightSimplified).map PanWordLab.word ==
  some (.word (holWordBits64 40))

example : (evalCrepRuntimeExp
    (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    holWordBitsMulEightSimplified).map PanWordLab.word =
  (evalCrepRuntimeExp
    (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    holWordBitsMulEight).map PanWordLab.word := by
  have hEval : (evalCrepRuntimeExp
      (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 64)))
      holWordBitsMulEight).map PanWordLab.word ≠ none := by
    simp [evalCrepRuntimeExp, crepOpCrep, CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime, holWordBitsMulEight,
      holWordBitsState64WithLocal,
      holWordBitsState64, holWordBits64]
  exact crepSimpExpCorrect1HolWordBitsSourceRuntime (fun (_, entry) => entry)
    holWordBitsState64WithLocal holWordBitsMulEight hEval

/-! This also instantiates the arbitrary-index HOL-shaped source evaluator
   theorem on the expression with direct HOL result `SOME (Word 40w)`. -/
example :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 64))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsState64WithLocal)
      (crepSimpExp
        (fun value => bitVecToHolWord
          (instFinHolFiniteDimension (width := 64))
          (BitVec.ofNat 64 value)) holWordBitsMulEight) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := 64))
      holWordBitsState64WithLocal holWordBitsMulEight := by
  have hRuntime : evalCrepRuntimeExp
      (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 64))) holWordBitsMulEight ≠ none := by
    simp [evalCrepRuntimeExp, crepOpCrep, CrepHolState.toHolFiniteWordSourceRuntime,
      CrepHolState.toHolFiniteWordRuntime, holWordBitsMulEight,
      holWordBitsState64WithLocal, holWordBitsState64, holWordBits64]
  have hRuntimeWordLab : (evalCrepRuntimeExp
      (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 64))) holWordBitsMulEight).map
        PanWordLab.word ≠ none := by
    cases hResult : evalCrepRuntimeExp
        (holWordBitsState64WithLocal.toHolFiniteWordSourceRuntime
          (instFinHolFiniteDimension (width := 64))) holWordBitsMulEight with
    | none => exact (hRuntime hResult).elim
    | some value => simp
  have hSource : (evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 64))
      holWordBitsState64WithLocal holWordBitsMulEight).map
        PanWordLab.word ≠ none := by
    rw [← congrArg (Option.map PanWordLab.word)
      (evalCrepRuntimeExp_sourceWord_eq
        (instFinHolFiniteDimension (width := 64))
        holWordBitsState64WithLocal holWordBitsMulEight)]
    exact hRuntimeWordLab
  exact crepSimpExpCorrect1HolFiniteWordSourceWordLab (fun (_, entry) => entry)
    holWordBitsState64WithLocal holWordBitsMulEight
    (.word (holWordBits64 40)) hSource

#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime (.const holBits4) ==
  some holBits4
#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
    (.crepOp .mul [.const holBits4, .const holBits4]) ==
  some (bitVecToHolWordBits (BitVec.ofNat 4 9))

example :
    evalCrepHolWordBitsExp holWordBitsState4
        (crepMulConst (fun value => bitVecToHolWordBits (BitVec.ofNat 4 value))
          (.const holBits4) holBits4) =
      some (holBits4 * holBits4) := by
  refine crepEvalMulConstHolWordBits (state := holWordBitsState4)
    (expression := .const holBits4) (constant := holBits4)
    (value := holBits4) ?_
  change (evalCrepHolExp holWordBitsState4.toBitVecState
    (mapCrepExpWord holWordBitsToBitVec (.const holBits4))).map
      bitVecToHolWordBits = some holBits4
  simp [evalCrepHolExp, mapCrepExpWord,
    bitVecToHolWordBits_holWordBitsToBitVec]

example :
    evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
        (.loadByte (.const holBits4)) =
      evalCrepHolWordBitsExp holWordBitsState4 (.loadByte (.const holBits4)) :=
  evalCrepRuntimeExp_toHolWordBits_eq holWordBitsState4
    (.loadByte (.const holBits4))

example :
    evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
        (.load32 (.const holBits4)) =
      evalCrepHolWordBitsExp holWordBitsState4 (.load32 (.const holBits4)) :=
  evalCrepRuntimeExp_toHolWordBits_eq holWordBitsState4
    (.load32 (.const holBits4))

example :
    (evalCrepRuntimeExp
      (CrepHolState.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 4))
      (crepArithHolFiniteDimensionMapCode (fun (_, entry) => entry)
        holWordBitsState4))
      (crepSimpExp (fun value => bitVecToHolWordBits (BitVec.ofNat 4 value))
        (.const holBits4))).map PanWordLab.word =
    (evalCrepRuntimeExp
      (holWordBitsState4.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 4)))
      (.const holBits4)).map PanWordLab.word := by
  apply crepSimpExpCorrect1HolWordBitsSourceRuntime (fun (_, entry) => entry)
    holWordBitsState4 _
  simp [evalCrepRuntimeExp]

example :
    crepRuntimeLoadByte
        (CrepHolState.toHolFiniteWordSourceRuntime
          (instFinHolFiniteDimension (width := 64)) holWordBitsState64)
        (holWordBits64 9) =
      crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) false)
        (holWordBits64 8) holWordBitsState64 (holWordBits64 9) :=
  crepHolFiniteWordSourceRuntime_loadByte holWordBitsState64 (holWordBits64 9)

example :
    crepRuntimeLoad32
        (CrepHolState.toHolFiniteWordSourceRuntime
          (instFinHolFiniteDimension (width := 64)) holWordBitsState64)
        (holWordBits64 8) =
      crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) false)
        (holWordBits64 8) holWordBitsState64 (holWordBits64 8) :=
  crepHolFiniteWordSourceRuntime_load32 holWordBitsState64 (holWordBits64 8)

/-! Direct parity for `crep_arith$simp_exp_def`
    (`crep_arithScript.sml:59`).  These cases cover constant folding,
    constant-on-either-side multiplication, recursive children, and the
    unchanged fallback shape. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.const (word8 2), .const (word8 3)]) with
  | .const value => value == word8 6
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.const (word8 2), .var 2]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.var 2, .const (word8 2)]) with
  | .shift .lsl (.var 2) (.const value) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul [.var 2, .const (word8 3)]) with
  | .crepOp .mul [.var 2, .const value] => value == word8 3
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.load (.crepOp .mul [.var 2, .const (word8 2)])) with
  | .load (.shift .lsl (.var 2) (.const value)) => value == word8 1
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8)
      (.crepOp .mul
        [.crepOp .mul [.const (word8 2), .const (word8 3)],
         .const (word8 4)]) with
  | .const value => value == word8 24
  | _ => false) &&
  (match crepSimpExp (BitVec.ofNat 8) (.var 7 : CrepExp (RiscV.Word 8)) with
  | .var 7 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

def noWords : RiscV.Word 64 → PanWordLab (RiscV.Word 64) := fun _ => .word 0
def noDomain : RiscV.Word 64 → Bool := fun _ => false

def runtimeBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noWords
    memaddrs := noDomain
    shMemaddrs := noDomain
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := (8 : RiscV.Word 64)
    ffiContext := riscv64PanValueFfiContext noDomain
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def runtimeState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { riscv64CrepRuntimeTarget runtimeBase with
    locals := updateCrepRuntimeLocal (fun _ => none) 2 (.word (7 : RiscV.Word 64)) }

/-! These checks exercise the production evaluator before and after the pass,
    including the power-of-two shift branch and bottom-up nested folding.
    They are executable support checks while the polymorphic HOL theorem port
    remains open. -/
def runtimeEvalSimpParity : Bool :=
  let source : CrepExp (RiscV.Word 64) :=
    .crepOp .mul [.var 2, .const (8 : RiscV.Word 64)]
  let nested : CrepExp (RiscV.Word 64) :=
    .crepOp .mul [source, .const (3 : RiscV.Word 64)]
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState) source == some 56 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepSimpExp (BitVec.ofNat 64) source) == some 56 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState) nested == some 168 &&
  evalCrepRuntimeExp (riscv64CrepRuntimeTarget runtimeState)
    (crepSimpExp (BitVec.ofNat 64) nested) == some 168

#guard runtimeEvalSimpParity

/-! An 8-bit all-width instance exercises the source-shaped state adapter and
    the proved production evaluator correspondence, beyond the RV64 executable
    fixture above. This remains untagged support for the arbitrary HOL word
    carrier gap documented beside `crepSimpExpCorrect1BitVec`. -/
def holState8 : CrepHolState (RiscV.Word 8) Unit :=
  { locals := updateCrepRuntimeLocal (fun _ => none) 2 (.word (word8 7))
    globals := fun _ => none
    code := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def holState8WithGlobal : CrepHolState (RiscV.Word 8) Unit :=
  { holState8 with globals := fun _ => some (.word (word8 9)) }

private def keySensitiveCodeMap :
    FunName × (List Nat × CrepProg (RiscV.Word 8)) →
      List Nat × CrepProg (RiscV.Word 8)
  | (name, (parameters, body)) =>
      if name == "selected" then (parameters.reverse, body)
      else (parameters, body)

private def holState8WithCode : CrepHolState (RiscV.Word 8) Unit :=
  { holState8 with code := fun name =>
      if name == "selected" then some ([1, 2], .skip)
      else if name == "untouched" then some ([1, 2], .skip)
      else none }

/-! HOL `FMAP_MAP2` passes the map key together with the stored value to its
    callback. This regression makes the selected function's parameter list
    change while another function's entry remains unchanged. -/
#guard
  let mapped := crepArithHolMapCode keySensitiveCodeMap holState8WithCode
  (match mapped.code "selected" with
   | some (parameters, .skip) => parameters == [2, 1]
   | _ => false) &&
  (match mapped.code "untouched" with
   | some (parameters, .skip) => parameters == [1, 2]
   | _ => false)

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) (.const (word8 4))) =
    evalCrepHolExpWordLab holState8 (.const (word8 4)) :=
    crepSimpExpCorrect1ConstCase (fun (_, entry) => entry) holState8 (word8 4)
    (.word (word8 4)) (by simp [evalCrepHolExpWordLab, evalCrepHolExp])

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) (.var 2)) =
    evalCrepHolExpWordLab holState8 (.var 2) :=
  crepSimpExpCorrect1VarCase (fun (_, entry) => entry) holState8 2
    (.word (word8 7)) (by
      simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8,
        updateCrepRuntimeLocal, panTheWord])

example :
    evalCrepHolExpWordLab
        (crepArithHolMapCode (fun (_, entry) => entry) holState8WithGlobal)
        (crepSimpExp (BitVec.ofNat 8) (.loadGlob 0)) =
      evalCrepHolExpWordLab holState8WithGlobal (.loadGlob 0) :=
  crepSimpExpCorrect1LoadGlobCase (fun (_, entry) => entry) holState8WithGlobal 0
    (.word (word8 9)) (by
      simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8WithGlobal,
        holState8, panTheWord])

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) .baseAddr) =
    evalCrepHolExpWordLab holState8 .baseAddr :=
  crepSimpExpCorrect1BaseAddrCase (fun (_, entry) => entry) holState8
    (.word 0) (by simp [evalCrepHolExpWordLab, evalCrepHolExp])

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) .topAddr) =
    evalCrepHolExpWordLab holState8 .topAddr :=
  crepSimpExpCorrect1TopAddrCase (fun (_, entry) => entry) holState8
    (.word 0) (by simp [evalCrepHolExpWordLab, evalCrepHolExp])

def holExpression8 : CrepExp (RiscV.Word 8) :=
  .crepOp .mul [.var 2, .const (word8 8)]

example :
    evalCrepHolExpWordLab
        (crepArithHolMapCode keySensitiveCodeMap holState8WithCode)
        (crepSimpExp (BitVec.ofNat 8) holExpression8) =
      evalCrepHolExpWordLab holState8WithCode holExpression8 := by
  apply crepSimpExpCorrect1BitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8WithCode,
    holState8, holExpression8, updateCrepRuntimeLocal, panTheWord]

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
    evalCrepHolExpWordLab holState8 holExpression8 := by
  apply crepSimpExpCorrect1BitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal]

example :
    evalCrepHolExpWordLab
      (crepArithHolMapCode (fun (_, entry) => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
      some (.word (word8 56)) := by
  apply crepSimpExpCorrectBitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal, panTheWord, word8]

/-! Direct HOL `eval_def` oracle `eval_const=SOME (Word 5w)` from
    `scripts/hol-probes/crep_eval_probe.out`. Check the full `Option word_lab`
    result through the source/runtime bridge, not only the raw word
    projection. -/
private def holWord64 (value : Nat) : Fin 64 → Bool :=
  bitVecToHolWordBits (BitVec.ofNat 64 value)

private def holWord64EvalState : CrepHolState (Fin 64 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word (holWord64 0)
  memaddrs := fun _ => false
  shMemaddrs := fun _ => false
  clock := 10
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holWord64 0
  topAddress := holWord64 0

example :
    (evalCrepRuntimeExp
      (holWord64EvalState.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 64)))
      (.const (holWord64 5))).map PanWordLab.word =
      some (.word (holWord64 5)) := by
  calc
    _ = evalCrepHolFiniteWordSourceExpWordLab
        (instFinHolFiniteDimension (width := 64)) holWord64EvalState
        (.const (holWord64 5)) :=
          evalCrepRuntimeExp_sourceWordLab_eq
            (instFinHolFiniteDimension (width := 64)) holWord64EvalState _
    _ = some (.word (holWord64 5)) := by
      simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp]

/-! The Const branch of simp_exp_correct1 leaves the direct HOL `eval_const`
row unchanged. The theorem is all-positive-width support; this fixture pins
its 64-bit instance to `crep_eval_probe.out`. -/
example :
    evalCrepHolExpWordLab (crepSemLoadState64.toBitVecEvaluatorState)
      (crepSimpExp (BitVec.ofNat 64) (.const (BitVec.ofNat 64 5))) =
      some (.word (BitVec.ofNat 64 5)) := by
  have h := crepSimpExpCorrect1ConstCaseBitVecSupport
    (update := fun pair : Flapjack.Basis.Pure.MlString.MlString ×
      (List Nat × CrepProgHOL 64) => pair.2)
    crepSemLoadState64 (BitVec.ofNat 64 5) (.word (BitVec.ofNat 64 5))
    (by simp [evalCrepHolExpWordLab, evalCrepHolExp])
  simpa [evalCrepHolExpWordLab, evalCrepHolExp] using h

end Flapjack.Test.CrepeSimpExpParity
