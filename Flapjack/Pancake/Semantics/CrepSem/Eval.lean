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
