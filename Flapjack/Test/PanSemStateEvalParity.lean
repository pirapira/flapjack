import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.WordLang

/-! The expected values are recorded by direct HOL EVAL of the source
`panSem$eval` probe. The Lean cases exercise the state-derived word and memory
inputs, including Cake's list-valued word operator arity, against those
checked-in results. -/

namespace Flapjack.Test.PanSemStateEvalParity

open Flapjack

private abbrev Word64 := RiscV.Word 64

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:209-297 (eval_def)"

def originalProbeCommand : String :=
  "HOL_PROBE_ONLY=pan_sem_state_eval_probeScript.sml scripts/hol-probes/regenerate.sh"

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:209-297 (eval_def)"
#guard originalProbeCommand ==
  "HOL_PROBE_ONLY=pan_sem_state_eval_probeScript.sml scripts/hol-probes/regenerate.sh"

def sourceMemoryWord : Word64 := BitVec.ofNat 64 0x1122334455667788

def sourceState (bigEndian inWordDomain inSharedDomain : Bool) :
    PanSemState Word64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun address =>
      if address == 0 then some (.word sourceMemoryWord) else none
    memaddrs := fun _ => inWordDomain
    sharedMemaddrs := fun _ => inSharedDomain
    clock := 0
    be := bigEndian
    ffi := ()
    baseAddress := 0
    topAddress := 0 }

private def isWordResult (result : Option (PanValue Word64))
    (expected : Word64) : Bool :=
  match result with
  | some (.word value) => value == expected
  | _ => false

private def isNoneResult {α : Type} (result : Option α) : Bool :=
  match result with
  | none => true
  | some _ => false

private def isErrorControlResult
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

def littleEndianState : PanSemState Word64 Unit := sourceState false true true
def bigEndianState : PanSemState Word64 Unit := sourceState true true true

def sourceFfiOracle : FfiOracle Unit := fun _ state _ bytes => .returned state bytes

def sourceFfiState : FfiState Unit :=
  { oracle := sourceFfiOracle, state := (), ioEvents := [] }

def sourceCodeState (bigEndian inWordDomain : Bool) :
    PanSemState Word64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun address =>
      if address == 0 then some (.word sourceMemoryWord) else none
    memaddrs := fun _ => inWordDomain
    sharedMemaddrs := fun _ => false
    clock := 0
    be := bigEndian
    ffi := sourceFfiState
    baseAddress := 0
    topAddress := 0 }

def sourceFfiContext : PanValueFfiContext Word64 :=
  { sharedDomain := fun _ => false
    byteAlign := RiscV.panRiscVByteAlign (BitVec.ofNat 64 8)
    bigEndian := false
    wordToBytes := fun _ _ => []
    wordOfBytes := fun _ _ => 0
    wordToByte := fun value => UInt8.ofNat value.toNat
    byteToWord := fun value => BitVec.ofNat 64 value.toNat
    valueToNat := fun value => value.toNat }

def sourceFfiHandler : PanValueStatefulFfiHandler Word64 Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def sourcePrimitive : PanPrimitiveHandler Word64 := fun _ _ => none

private def observesReturnedWord
    (result : Option (PanValueFfiClockResult Word64 Unit)) (expected : Word64) : Bool :=
  match result with
  | some (.control (.returned _ _ _ _ [.word value]), _) => value == expected
  | _ => false

#guard observesReturnedWord
  (panSemEvaluateRiscV64CodeState sourceFfiContext sourcePrimitive sourceFfiHandler
    (sourceCodeState false true) (.return (.loadByte (.const 0))))
  (BitVec.ofNat 64 0x88)
#guard isErrorControlResult
  (panSemEvaluateRiscV64CodeState sourceFfiContext sourcePrimitive sourceFfiHandler
    (sourceCodeState false false) (.return (.loadByte (.const 0))))

#guard isWordResult
  (evalPanSemStateExp littleEndianState (.load .one (.const 0)))
  sourceMemoryWord
#guard isNoneResult (evalPanSemStateExp (sourceState false false true)
  (.load .one (.const 0)))
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.loadByte (.const 0)))
  (BitVec.ofNat 64 0x88)
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.loadByte (.const 7)))
  (BitVec.ofNat 64 0x11)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.loadByte (.const 0)))
  (BitVec.ofNat 64 0x11)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.loadByte (.const 7)))
  (BitVec.ofNat 64 0x88)
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.load32 (.const 0)))
  (BitVec.ofNat 64 0x55667788)
#guard isWordResult
  (evalPanSemStateExp bigEndianState (.load32 (.const 0)))
  (BitVec.ofNat 64 0x11223344)

/- These model checks exercise the same endian-sensitive get_byte and
   word_of_bytes path used by the width-generic Crep target adapter. -/
#guard (RiscV.panRiscVMemoryModelForEndian true).getByte
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 0) sourceMemoryWord true ==
  BitVec.ofNat 64 0x11
#guard panModelRead32 (RiscV.panRiscVMemoryModelForEndian true)
    (fun _ : Word64 => true) (fun _ : Word64 => some sourceMemoryWord)
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 0) true ==
  some (BitVec.ofNat 64 0x11223344)
#guard isWordResult
  (evalPanSemStateExp littleEndianState
    (.op .add [.const 1, .const 2, .const 3]))
  (BitVec.ofNat 64 6)
#guard isNoneResult
  (evalPanSemStateExp littleEndianState (.op .sub [.const 1]))

/- The direct HOL `eval_def` rows above exercise `word_op_def`'s list fold and
   invalid Sub arity. These checks compare the tagged source-shaped definition
   with the RISC-V operation used by production expression evaluation. -/
#guard wordOpHOL .add
    [BitVec.ofNat 64 1, BitVec.ofNat 64 2, BitVec.ofNat 64 3] ==
  some (BitVec.ofNat 64 6)
#guard wordOpHOL .sub [BitVec.ofNat 64 1] == none
#guard RiscV.panRiscVWordOp .add
    [BitVec.ofNat 64 1, BitVec.ofNat 64 2, BitVec.ofNat 64 3] ==
  some (BitVec.ofNat 64 6)
#guard RiscV.panRiscVWordOp .sub [BitVec.ofNat 64 1] == none

#guard isWordResult ((panSemBitVec64MemoryAccess littleEndianState).sharedRead
  littleEndianState.memory panSemBitVec64BytesInWord .opW 0)
  sourceMemoryWord
#guard isNoneResult ((panSemBitVec64MemoryAccess
  (sourceState false true false)).sharedRead
    littleEndianState.memory panSemBitVec64BytesInWord .opW 0)


/- The executed exact-state `.op` path delegates to the tagged `wordOpHOL`
   list fold for arbitrary operand lists. These build-checked theorems record
   that delegation; the `#guard`s pin the checked-in direct HOL rows for
   0/1/2/3 operands and the Sub arities. -/
theorem panSemBitVec64MemoryAccess_wordOp_tagged :
    (panSemBitVec64MemoryAccess littleEndianState).wordOp .add
        [BitVec.ofNat 64 1, BitVec.ofNat 64 2, BitVec.ofNat 64 3] =
      wordOpHOL .add [BitVec.ofNat 64 1, BitVec.ofNat 64 2, BitVec.ofNat 64 3] :=
  Flapjack.panSemBitVec64MemoryAccess_wordOp littleEndianState .add _

theorem evalPanSemStateExp_op_delegates (operator : BinOp)
    (arguments : List (Exp Word64)) :
    evalPanSemStateExp littleEndianState (.op operator arguments) =
      (evalPanSemStateExps littleEndianState arguments).bind (fun values =>
        (values.mapM panValueWordProjection).bind (fun words =>
          (wordOpHOL operator words).map PanValue.word)) :=
  Flapjack.evalPanSemStateExp_op littleEndianState operator arguments

#guard isWordResult (evalPanSemStateExp littleEndianState (.op .add []))
  (BitVec.ofNat 64 0)
#guard isWordResult (evalPanSemStateExp littleEndianState (.op .add [.const 1]))
  (BitVec.ofNat 64 1)
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.op .add [.const 1, .const 2]))
  (BitVec.ofNat 64 3)
#guard isWordResult
  (evalPanSemStateExp littleEndianState
    (.op .and [.const 15, .const 6, .const 3]))
  (BitVec.ofNat 64 2)
#guard isWordResult
  (evalPanSemStateExp littleEndianState
    (.op .or [.const 1, .const 2, .const 4]))
  (BitVec.ofNat 64 7)
#guard isWordResult
  (evalPanSemStateExp littleEndianState
    (.op .xor [.const 1, .const 2, .const 4]))
  (BitVec.ofNat 64 7)
#guard isNoneResult (evalPanSemStateExp littleEndianState (.op .sub []))
#guard isWordResult
  (evalPanSemStateExp littleEndianState (.op .sub [.const 3, .const 5]))
  (BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE)

/- Exact `mem_load_byte_def` port over the faithful total word-cell memory.
   The expected values are the checked-in direct HOL rows
   `mem_load_byte_def_little_first/little_last/big_first/missing` in
   `scripts/hol-probes/pan_sem_state_eval_probe.out`. -/
def holMemory64 : Word64 → HolWordLab 64 :=
  fun address => if address = 0 then .word sourceMemoryWord else .word 0

#guard panMemLoadByteHOL (width := 64) holMemory64 (fun a => a = 0) false 0 ==
  some (UInt8.ofNat 136)
#guard panMemLoadByteHOL (width := 64) holMemory64 (fun a => a = 0) false 7 ==
  some (UInt8.ofNat 17)
#guard panMemLoadByteHOL (width := 64) holMemory64 (fun a => a = 0) true 0 ==
  some (UInt8.ofNat 17)
#guard panMemLoadByteHOL (width := 64) holMemory64 (fun _ => False) false 0 ==
  none

example : panMemLoadByteHOL (width := 64) holMemory64 (fun a => a = 0) false 0 =
    some (UInt8.ofNat 136) := by decide
example : panMemLoadByteHOL (width := 64) holMemory64 (fun _ => False) false 0 =
    none := by decide

/- Exact `mem_load_32_def` port; expected values are the checked-in direct HOL
   rows `mem_load_32_def_little/big/misaligned/missing`. -/
#guard panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) false 0 ==
  some (BitVec.ofNat 32 0x55667788)
#guard panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) true 0 ==
  some (BitVec.ofNat 32 0x11223344)
#guard panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) false 1 ==
  none
#guard panMemLoad32HOL (width := 64) holMemory64 (fun _ => False) false 0 ==
  none

example : panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) false 0 =
    some (BitVec.ofNat 32 0x55667788) := by decide
example : panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) true 0 =
    some (BitVec.ofNat 32 0x11223344) := by decide
example : panMemLoad32HOL (width := 64) holMemory64 (fun a => a = 0) false 1 =
    none := by decide
example : panMemLoad32HOL (width := 64) holMemory64 (fun _ => False) false 0 =
    none := by decide


/- Structured `mem_load` port; expected values are the checked-in direct HOL rows
   `mem_load_def_one_hit/one_miss/comb_pair/named_found/named_missing`. -/
private def structsS : StructContextHOL :=
  [("S", { fields := [("f", Shape.one)], size := 3 })]

private def memStructured : Word64 → HolWordLab 64 := fun address =>
  if address == 0 then .word (BitVec.ofNat 64 0x11)
  else if address == 8 then .word (BitVec.ofNat 64 0x22) else .word 0

private abbrev domStructured : Word64 → Prop := fun address => address = 0 ∨ address = 8

private def isVal (expected : Word64) : Option (HolValue 64) → Bool
  | some (.val (.word value)) => value == expected
  | _ => false

private def isCombPair (left right : Word64) : Option (HolValue 64) → Bool
  | some (.rStruct [.val (.word first), .val (.word second)]) =>
      first == left && second == right
  | _ => false

private def isNamedField (name field : String) (expected : Word64) :
    Option (HolValue 64) → Bool
  | some (.nStruct actual [(actualField, .val (.word value))]) =>
      actual == name && actualField == field && value == expected
  | _ => false

#guard isVal (BitVec.ofNat 64 0x11)
  (panMemLoadHOL (width := 64) .one 0 domStructured memStructured structsS)
#guard panMemLoadHOL (width := 64) .one 0 (fun _ => False) memStructured structsS
  = none
#guard isCombPair (BitVec.ofNat 64 0x11) (BitVec.ofNat 64 0x22)
  (panMemLoadHOL (width := 64) (.comb [.one, .one]) 0 domStructured memStructured structsS)
#guard isNamedField "S" "f" (BitVec.ofNat 64 0x11)
  (panMemLoadHOL (width := 64) (.named "S") 0 domStructured memStructured structsS)
#guard panMemLoadHOL (width := 64) (.named "T") 0 domStructured memStructured structsS
  = none
#guard sizeOfShWithCtxt structsS (.named "S") == 3
#guard sizeOfShWithCtxt structsS (.comb [.one, .one]) == 2


/- width-24 alignment rows `mem_load_byte_def_w24_addr5=SOME 17w` and
   `mem_load_32_def_w24_addr4=SOME 0x22331122w`. -/
private def mem24 : RiscV.Word 24 → HolWordLab 24 := fun address =>
  if address == 4 then .word (BitVec.ofNat 24 0x112233) else .word 0

private abbrev dom24 : RiscV.Word 24 → Prop := fun address => address = 4

#guard panMemLoadByteHOL (width := 24) mem24 dom24 false (BitVec.ofNat 24 5) = some 17
#guard panMemLoad32HOL (width := 24) mem24 dom24 false (BitVec.ofNat 24 4) =
  some (BitVec.ofNat 32 0x22331122)

/-- Direct HOL width-4 parity with nonzero word 0xB: little endian uses
    `address MOD 0`, while big endian's natural subtraction saturates to zero. -/
private def mem4 : RiscV.Word 4 → HolWordLab 4 := fun _ => .word 1
private abbrev dom4 : RiscV.Word 4 → Prop := fun address => address = 1

#guard panMemLoadByteHOL (width := 4) mem4 dom4 false 1 == some (UInt8.ofNat 0)
example : panMemLoadByteHOL (width := 4) mem4 dom4 false 1 =
    some (UInt8.ofNat 0) := by decide

private def mem4Nonzero : RiscV.Word 4 → HolWordLab 4 := fun _ => .word 11
private abbrev dom4All : RiscV.Word 4 → Prop := fun _ => True

#guard panMemLoadByteHOL (width := 4) mem4Nonzero dom4All false 0 ==
  some (UInt8.ofNat 11)
#guard panMemLoadByteHOL (width := 4) mem4Nonzero dom4All false 1 ==
  some (UInt8.ofNat 0)
#guard panMemLoadByteHOL (width := 4) mem4Nonzero dom4All true 0 ==
  some (UInt8.ofNat 11)
#guard panMemLoadByteHOL (width := 4) mem4Nonzero dom4All true 1 ==
  some (UInt8.ofNat 11)

/-! ### Executed-path widening adapter (flapjack-pxn.18.3.6.9.2) -/

/-- The executed `readByte` on the source state agrees with the tagged exact
    `panMemLoadByteHOL` over the word view of its `PanValue` memory. -/
example :
    (panSemBitVec64MemoryAccess littleEndianState).readByte
        (panSemBitVec64MemoryAccess littleEndianState).domain littleEndianState.memory
        panSemBitVec64BytesInWord 0 =
      (panMemLoadByteHOL (width := 64) (panValueWordHOL littleEndianState.memory)
        (fun a => littleEndianState.memaddrs a &&
          panValueWordDefined littleEndianState.memory a = true) littleEndianState.be
        0).map (fun byte => BitVec.ofNat 64 byte.toNat) :=
  panSemBitVec64ReadByte_eq_panMemLoadByteHOL littleEndianState littleEndianState.memory 0

/- The adapter's right-hand side computes the expected little-endian first byte
   (`0x88`) of `sourceMemoryWord`. -/
#guard
  ((panMemLoadByteHOL (width := 64) (panValueWordHOL littleEndianState.memory)
      (fun a => littleEndianState.memaddrs a &&
        panValueWordDefined littleEndianState.memory a = true) littleEndianState.be
      0).map (fun byte => BitVec.ofNat 64 byte.toNat)
    == some (BitVec.ofNat 64 (UInt8.ofNat 0x88).toNat))

/-- The executed `read32` on the source state agrees with the tagged exact
    `panMemLoad32HOL` over the word view of its `PanValue` memory. -/
example :
    (panSemBitVec64MemoryAccess littleEndianState).read32
        (panSemBitVec64MemoryAccess littleEndianState).domain littleEndianState.memory
        panSemBitVec64BytesInWord 0 =
      (panMemLoad32HOL (width := 64) (panValueWordHOL littleEndianState.memory)
        (fun a => littleEndianState.memaddrs a &&
          panValueWordDefined littleEndianState.memory a = true) littleEndianState.be
        0).map (fun word => BitVec.ofNat 64 word.toNat) :=
  panSemBitVec64Read32_eq_panMemLoad32HOL littleEndianState littleEndianState.memory 0

/- The adapter's right-hand side computes the expected little-endian 32-bit word
   (`0x55667788`) of `sourceMemoryWord`. -/
#guard
  ((panMemLoad32HOL (width := 64) (panValueWordHOL littleEndianState.memory)
      (fun a => littleEndianState.memaddrs a &&
        panValueWordDefined littleEndianState.memory a = true) littleEndianState.be
      0).map (fun word => BitVec.ofNat 64 word.toNat)
    == some (BitVec.ofNat 64 0x55667788))

/-- The structured `.load` on a `One` shape agrees with the tagged exact
    `panMemLoadHOL` over the word view of the `PanValue` memory. -/
example :
    panValueFlatLoad ([] : StructContext) littleEndianState.memory
        panSemBitVec64BytesInWord 0 .one
        (some (panSemBitVec64MemoryAccess littleEndianState)) =
      (panMemLoadHOL (width := 64) .one 0
        (fun a => littleEndianState.memaddrs a &&
          panValueWordDefined littleEndianState.memory a = true)
        (panValueWordHOL littleEndianState.memory)
        (StructContext.toHOL ([] : StructContext))).map HolValue.toPanValue :=
  panValueFlatLoad_one_eq_panMemLoadHOL littleEndianState
    littleEndianState.memory ([] : StructContext) 0

/- The structured `One` load returns the source word. -/
#guard
  isWordResult
    (panValueFlatLoad ([] : StructContext) littleEndianState.memory
      panSemBitVec64BytesInWord 0 .one
      (some (panSemBitVec64MemoryAccess littleEndianState)))
    sourceMemoryWord

/- The production context-size agrees with the exact HOL context-size. -/
example : shapeSizeWithContext ([] : StructContext) Shape.one =
    sizeOfShWithCtxt (StructContext.toHOL ([] : StructContext)) Shape.one :=
  panValueFlatShapeSize_eq_sizeOfShWithCtxt ([] : StructContext) Shape.one

/- The production offset agrees with the exact `address + bytes_in_word * n`. -/
example : panValueFlatOffset (8 : RiscV.Word 64) (16 : RiscV.Word 64) 3 =
    (16 : RiscV.Word 64) + BitVec.ofNat 64 8 * BitVec.ofNat 64 3 :=
  panValueFlatOffset_eq_widen 16 3

/- The nested `Comb` sub-shape fuel stays within the shape's list fuel. -/
example :
    panValueFlatShapeFuel Shape.one ≤
      panValueFlatShapeFuel.panValueFlatShapeListFuel [Shape.named "S", Shape.one] :=
  panValueFlatShapeFuel_le_listFuel (by simp)

/- The `Named` field-shape fuel stays within the field-list fuel. -/
example :
    panValueFlatShapeFuel Shape.one ≤
      panValueFlatFieldsFuel ([("f", Shape.one)] : List (FieldName × Shape)) :=
  panValueFlatFieldsFuel_shapeFuel_le (field := ("f", Shape.one)) (by simp)

/-- The `Named` lookup fuel bound: the matched struct's field fuel plus the
    remaining context fuel stays below the whole-context fuel. -/
example :
    panValueFlatFieldsFuel ([("f", Shape.one)] : List (FieldName × Shape)) +
        panValueFlatContextFuel ([] : StructContext) ≤
      panValueFlatContextFuel
        ([("S", { fields := [("f", Shape.one)], size := 1 })] : StructContext) :=
  panValueFlatContextFuel_lookupInfoWithRest_le "S"
    ([("S", { fields := [("f", Shape.one)], size := 1 })] : StructContext)
    { fields := [("f", Shape.one)], size := 1 } [] (by simp [lookupInfoWithRest])

#guard decide (panValueFlatShapeFuel Shape.one ≤
  panValueFlatShapeFuel.panValueFlatShapeListFuel [Shape.named "S", Shape.one])

#guard decide (panValueFlatShapeFuel Shape.one ≤
  panValueFlatFieldsFuel ([("f", Shape.one)] : List (FieldName × Shape)))

/- The per-node word read agrees with the exact domain/memory pair. -/
example :
    panValueFlatReadWord littleEndianState.memory panSemBitVec64BytesInWord
        (some (panSemBitVec64MemoryAccess littleEndianState)) 0 =
      (if littleEndianState.memaddrs 0 &&
          panValueWordDefined littleEndianState.memory 0 = true
        then some (panValueWordHOL littleEndianState.memory 0) else none).map
        (fun lab => match lab with | .word value => value) :=
  panValueFlatReadWord_eq_panValueWordHOL littleEndianState
    littleEndianState.memory 0

#guard
  (panValueFlatReadWord littleEndianState.memory panSemBitVec64BytesInWord
      (some (panSemBitVec64MemoryAccess littleEndianState)) 0 ==
    some sourceMemoryWord)

/-! Structured `.load` Comb/Named induction prerequisites (flapjack-pxn.18.3.6.9.2.2.1). -/

example : 1 ≤ panValueFlatShapeFuel Shape.one := panValueFlatShapeFuel_pos Shape.one

example : 1 ≤ panValueFlatShapeFuel.panValueFlatShapeListFuel [Shape.one] :=
  panValueFlatShapeListFuel_pos Shape.one []

example : 1 ≤ panValueFlatFieldsFuel [("f", Shape.one)] :=
  panValueFlatFieldsFuel_pos ("f", Shape.one) []

example :
    panMemLoadHOL (width := 64) (.named "S")
        (0 : RiscV.Word 64)
        (fun a => littleEndianState.memaddrs a && panValueWordDefined littleEndianState.memory a = true)
        (panValueWordHOL littleEndianState.memory)
        (StructContext.toHOL ([] : StructContext)) = none :=
  panMemLoadHOL_named_none "S" ([] : StructContext) 0
    (fun a => littleEndianState.memaddrs a && panValueWordDefined littleEndianState.memory a = true)
    (panValueWordHOL littleEndianState.memory) (by simp [lookupInfoWithRest])

example :
    panMemLoadHOL (width := 64) (.named "S")
        (0 : RiscV.Word 64)
        (fun a => littleEndianState.memaddrs a && panValueWordDefined littleEndianState.memory a = true)
        (panValueWordHOL littleEndianState.memory)
        (StructContext.toHOL ([("S", { fields := [("f", Shape.one)], size := 1 })] : StructContext)) =
      (panMemLoadFldsHOL [("f", Shape.one)]
        (0 : RiscV.Word 64)
        (fun a => littleEndianState.memaddrs a && panValueWordDefined littleEndianState.memory a = true)
        (panValueWordHOL littleEndianState.memory)
        (StructContext.toHOL ([] : StructContext))).map
        (fun fields => HolValue.nStruct "S" fields) :=
  panMemLoadHOL_named_some "S" [("S", { fields := [("f", Shape.one)], size := 1 })] 0
    (fun a => littleEndianState.memaddrs a && panValueWordDefined littleEndianState.memory a = true)
    (panValueWordHOL littleEndianState.memory)
    { fields := [("f", Shape.one)], size := 1 } []
    (by simp [lookupInfoWithRest])

/-- Equation lemmas of the exact-HOL `HolValue.toPanValue` isomorphism. -/
example :
    HolValue.toPanValue (width := 64) (HolValue.val (HolWordLab.word (7 : RiscV.Word 64))) =
      PanValue.word (7 : RiscV.Word 64) :=
  HolValue.toPanValue_val (7 : RiscV.Word 64)

example :
    HolValue.toPanValue (width := 64) (HolValue.rStruct []) =
      PanValue.rStruct ([] : List (PanValue (RiscV.Word 64))) :=
  HolValue.toPanValue_rStruct ([] : List (HolValue 64))

example :
    HolValue.toPanValue (width := 64)
        (HolValue.nStruct "S" [("f", HolValue.val (HolWordLab.word (7 : RiscV.Word 64)))]) =
      PanValue.nStruct "S" [("f", PanValue.word (7 : RiscV.Word 64))] :=
  by
    simpa [HolValue.toPanValue_val] using
      HolValue.toPanValue_nStruct "S" [("f", HolValue.val (HolWordLab.word (7 : RiscV.Word 64)))]

/-- Fuel-indexed Comb/List/Fields/Named equivalence with the tagged exact `mem_load_def`
port, extracted from the conjunction produced by the mutual fuel induction. -/
example :
    panValueFlatLoadFuel ([] : StructContext)
        (panValueFlatMachineReadWord littleEndianState littleEndianState.memory)
        panSemBitVec64BytesInWord 3 (.comb [Shape.one]) 0 =
      (panMemLoadHOL (width := 64) (.comb [Shape.one]) 0
        (panValueFlatMachineDomain littleEndianState littleEndianState.memory)
        (panValueWordHOL littleEndianState.memory) (StructContext.toHOL ([] : StructContext))).map HolValue.toPanValue :=
  (panValueFlatLoadFuel_eq_panMemLoadHOL littleEndianState littleEndianState.memory 3).1
    [] (.comb [Shape.one]) 0 (by decide)


/-- Capstone: the guarded production `panValueFlatLoad` over the executed RV64
memory-access state equals the tagged exact `panMemLoadHOL` mapped by
`HolValue.toPanValue`. -/
example (hwf : isWfShape ([] : StructContext) Shape.one = true) :
    panValueFlatLoad ([] : StructContext) littleEndianState.memory
        panSemBitVec64BytesInWord 0 Shape.one
        (some (panSemBitVec64MemoryAccess littleEndianState)) =
      (panMemLoadHOL (width := 64) Shape.one 0
        (panValueFlatMachineDomain littleEndianState littleEndianState.memory)
        (panValueWordHOL littleEndianState.memory)
        (StructContext.toHOL ([] : StructContext))).map HolValue.toPanValue :=
  panValueFlatLoad_eq_panMemLoadHOL littleEndianState littleEndianState.memory
    ([] : StructContext) Shape.one 0 hwf

end Flapjack.Test.PanSemStateEvalParity
