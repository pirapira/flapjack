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

@[simp] theorem holWordBitsToBitVec_add {width : Nat}
    (left right : Fin width → Bool) :
    holWordBitsToBitVec (left + right) =
      holWordBitsToBitVec left + holWordBitsToBitVec right := by
  change holWordBitsToBitVec (bitVecToHolWordBits
    (holWordBitsToBitVec left + holWordBitsToBitVec right)) = _
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
    carrier equivalence. This adapter is untagged until its relation to the
    full production evaluator is proved for every constructor. -/
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

/-! The next desired bridge would show that the production runtime evaluator on
    the finite-index HOL-word carrier equals the transported source evaluator
    above. This is not implied by the carrier equivalence alone: the 32-bit
    load, list-valued `wordOp`, comparisons, and shifts must commute with the
    conversion. Keep the statement out of the HOL map until those operation
    and state equations are proved. -/

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

/-! Flapjack-only all-constructor correspondence for the positive-width
BitVec adapter. This removes the evaluator mismatch for that representation,
but does not establish the arbitrary HOL word-carrier theorem. -/
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

end Flapjack
