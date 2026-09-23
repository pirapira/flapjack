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
      (crepArithMapCode id
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension))
      (crepSimpExp
        (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]))).map
        PanWordLab.word =
      (evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
        PanWordLab.word := by
  exact crepSimpExpCorrect1HolFiniteDimension id boolDimensionHolState _
    (by simp [evalCrepRuntimeExp])

example :
    evalCrepHolFiniteDimensionExpWordLab boolWordDimension
        (crepArithHolFiniteDimensionMapCode id boolDimensionHolState)
        (crepSimpExp
          (fun n => bitVecToHolWord boolWordDimension (BitVec.ofNat 2 n))
          (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])) =
      evalCrepHolFiniteDimensionExpWordLab boolWordDimension boolDimensionHolState
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
  apply crepSimpExpCorrect1HolFiniteDimensionSource id
    boolDimensionHolState _
  have hEval := evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState
      (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])
  change (evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
    (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])).map
      PanWordLab.word ≠ none
  rw [← hEval]
  simp [evalCrepRuntimeExp]

example : True := by
  letI : HolFiniteDimension Bool := boolWordDimensionSwapped
  have hresult :
      evalCrepHolFiniteDimensionExpWordLab boolWordDimensionSwapped
          (crepArithHolFiniteDimensionMapCode id boolDimensionHolState)
          (crepSimpExp
            (fun n => bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 n))
            (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord])) =
        evalCrepHolFiniteDimensionExpWordLab boolWordDimensionSwapped
          boolDimensionHolState
          (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
    apply crepSimpExpCorrect1HolFiniteDimensionSource id
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

def holExpression8 : CrepExp (RiscV.Word 8) :=
  .crepOp .mul [.var 2, .const (word8 8)]

example :
    evalCrepHolExpWordLab (crepArithHolMapCode (fun entry => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
    evalCrepHolExpWordLab holState8 holExpression8 := by
  apply crepSimpExpCorrect1BitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal]

example :
    evalCrepHolExpWordLab (crepArithHolMapCode (fun entry => entry) holState8)
      (crepSimpExp (BitVec.ofNat 8) holExpression8) =
      some (.word (word8 56)) := by
  apply crepSimpExpCorrectBitVec
  simp [evalCrepHolExpWordLab, evalCrepHolExp, holState8, holExpression8,
    updateCrepRuntimeLocal, panTheWord, word8]

end Flapjack.Test.CrepeSimpExpParity
