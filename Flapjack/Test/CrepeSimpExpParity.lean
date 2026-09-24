import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeSimpExpParity

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
    by the dimension encoding, matching HOL's FCP `finite_index` convention. -/
#guard holFiniteWordN2W boolWordDimension 1 false == true
#guard holFiniteWordN2W boolWordDimension 1 true == false
#guard holFiniteWordN2W boolWordDimension 2 true == true

@[instance_reducible] def boolWordDimensionSwapped : HolFiniteDimension Bool where
  width := 2
  width_pos := by decide
  encode := fun index => if index then 0 else 1
  decode := fun index => index.val == 0
  encode_decode := by decide
  decode_encode := by decide

/-! This witness demonstrates why an arbitrary finite enumeration alone is
    not a HOL word representation: `n2w 1` changes when the index order is
    permuted. The generic preservation theorem holds under either selected
    model, but an exact HOL port must identify HOL's canonical index order. -/
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
    boolDimensionHolState _ (by simp [evalCrepRuntimeExp])

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
    (by simp [evalCrepRuntimeExp])

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
  simp [evalCrepRuntimeExp]

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
  simp [evalCrepRuntimeExp]

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
    simp [evalCrepRuntimeExp]
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
    simp [evalCrepRuntimeExp, CrepHolState.toHolFiniteWordSourceRuntime,
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
    simp [evalCrepRuntimeExp, CrepHolState.toHolFiniteWordSourceRuntime,
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

end Flapjack.Test.CrepeSimpExpParity
