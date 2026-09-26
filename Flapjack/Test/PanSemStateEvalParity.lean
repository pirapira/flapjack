import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.ByteAlignBridge
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

/- Direct HOL mem_load_32 rows distinguish the little-endian 0,0,0,0 MOD 0
   byte indices from the big-endian saturating subtraction case. -/
#guard panMemLoad32HOL (width := 4) mem4Nonzero dom4All false 0 ==
  some (BitVec.ofNat 32 11)
#guard panMemLoad32HOL (width := 4) mem4Nonzero dom4All true 0 ==
  some (BitVec.ofNat 32 0x0B0B0B0B)

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
    HolValue.toPanValue (width := 64) (HolValue.val (PanWordLab.word (7 : RiscV.Word 64))) =
      PanValue.word (7 : RiscV.Word 64) :=
  HolValue.toPanValue_val (7 : RiscV.Word 64)

example :
    HolValue.toPanValue (width := 64) (HolValue.rStruct []) =
      PanValue.rStruct ([] : List (PanValue (RiscV.Word 64))) :=
  HolValue.toPanValue_rStruct ([] : List (HolValue 64))

example :
    HolValue.toPanValue (width := 64)
        (HolValue.nStruct "S" [("f", HolValue.val (PanWordLab.word (7 : RiscV.Word 64)))]) =
      PanValue.nStruct "S" [("f", PanValue.word (7 : RiscV.Word 64))] :=
  by
    simpa [HolValue.toPanValue_val] using
      HolValue.toPanValue_nStruct "S" [("f", HolValue.val (PanWordLab.word (7 : RiscV.Word 64)))]

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

/-! ## Exact `panSem$eval_def` evaluator parity (flapjack-pxn.18.3.6.9.3)

The HOL rows are the `word_load_hit`, `byte_little_first`, `word32_little`,
`op_add_fold_three`, and `op_sub_wrong_arity` lines of
`scripts/hol-probes/pan_sem_state_eval_probe.out` (direct HOL EVAL of
`panSem$eval`). -/

abbrev holEvalState : PanSemHolState 64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := fun address => if address == 0 then .word sourceMemoryWord else .word 0
    memaddrs := fun address => address = 0
    shMemaddrs := fun _ => False
    clock := 0
    be := false
    ffi := sourceFfiState
    baseAddr := 0
    topAddr := 0 }

def evalWordResult (result : Option (HolValue 64)) : Option Word64 :=
  match result with
  | some (.val (.word value)) => some value
  | _ => none

#guard evalWordResult (evalHOL holEvalState (.const 7)) == some 7
#guard evalWordResult (evalHOL holEvalState (.load Shape.one (.const 0))) ==
  some sourceMemoryWord
#guard evalWordResult (evalHOL holEvalState (.loadByte (.const 0))) ==
  some (BitVec.ofNat 64 136)
#guard evalWordResult (evalHOL holEvalState (.load32 (.const 0))) ==
  some (BitVec.ofNat 64 0x55667788)
#guard evalWordResult (evalHOL holEvalState (.op .add [.const 1, .const 2, .const 3])) ==
  some 6
#guard evalWordResult (evalHOL holEvalState (.op .sub [.const 1])) == none

/-- State with a single `Pair` struct (field `f : One`), matching the
    `nstruct_*` rows of `scripts/hol-probes/pan_sem_state_eval_probe.out`. -/
abbrev holEvalStateWithPair : PanSemHolState 64 Unit :=
  { holEvalState with
    structs := [("Pair", { fields := [("f", Shape.one)], size := 1 })] }

/-- Projection of the field word from a `NStruct` result (single field). -/
def nstructFieldWord (result : Option (HolValue 64)) : Option Word64 :=
  match result with
  | some (.nStruct _ [(_, .val (.word value))]) => some value
  | _ => none

def evalResultIsNone (result : Option (HolValue 64)) : Bool :=
  match result with
  | none => true
  | some _ => false

#guard nstructFieldWord
    (evalHOL holEvalStateWithPair (.nStruct "Pair" [("f", .const 7)])) == some 7
#guard evalResultIsNone (evalHOL holEvalStateWithPair (.nStruct "Pair" [("f", .rStruct [])]))
#guard evalResultIsNone (evalHOL holEvalStateWithPair (.nStruct "Pair" [("g", .const 7)]))
#guard evalResultIsNone (evalHOL holEvalState (.nStruct "Pair" [("f", .const 7)]))

/-- Production struct context matching `holEvalStateWithPair`. -/
abbrev pairStructContext : StructContext :=
  [("Pair", { fields := [("f", Shape.one)], size := 1 })]

example :
    evalPanValueExp pairStructContext (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.nStruct "Pair" [("f", .const 7)])
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalStateWithPair (.nStruct "Pair" [("f", .const 7)])).map
          HolValue.toPanValue :=
  evalPanValueExp_nStruct_eq_evalHOL holEvalStateWithPair pairStructContext (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) "Pair" [("f", .const 7)]
    (by simp [pairStructContext, StructContext.toHOL])
    (fun pair hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl
      exact evalPanValueExp_const_eq_evalHOL holEvalStateWithPair pairStructContext
        (fun _ => none) (fun _ => none) (fun _ => none) 0 0
        panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 7)

example :
    evalPanValueExp pairStructContext (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.nField "f" (.const 7))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalStateWithPair (.nField "f" (.const 7))).map HolValue.toPanValue :=
  evalPanValueExp_nField_eq_evalHOL holEvalStateWithPair pairStructContext (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) "f" (.const 7)
    (by simp [pairStructContext, StructContext.toHOL])
    (evalPanValueExp_const_eq_evalHOL holEvalStateWithPair pairStructContext (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (panSemBitVec64MemoryAccess littleEndianState)) 7)

/- Bridge: production `panValueShape` agrees with `holShapeOf` on the `HolValue`
   image used by tagged `evalHOL` (bead flapjack-pxn.18.3.6.9.4). -/
example (value : PanValue (BitVec 64)) :
    holShapeOf value.toHolValue = panValueShape ([] : StructContext) value :=
  holShapeOf_toHolValue ([] : StructContext) value

example :
    (([PanValue.word (3 : BitVec 64), PanValue.rStruct []] : List (PanValue (BitVec 64))).map
        PanValue.toHolValue).map holShapeOf
      = ([PanValue.word (3 : BitVec 64), PanValue.rStruct []] : List (PanValue (BitVec 64))).map
          (panValueShape ([] : StructContext)) :=
  holShapeOf_map_toHolValue ([] : StructContext) _

example (shape : Shape) (value : PanValue (BitVec 64)) :
    panShapeMatches shape (holShapeOf value.toHolValue) =
      panShapeMatches shape (panValueShape ([] : StructContext) value) :=
  panShapeMatches_holShapeOf_toHolValue ([] : StructContext) shape value

/- Bridges: the production `NStruct` field check equals the inline `evalHOL`
   predicate over the `HolValue` image (bead flapjack-pxn.18.3.6.9.5). -/
example (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue (BitVec 64))) :
    List.all
        ((expected.map Prod.snd).zip
          ((actual.map (fun pair => (pair.1, pair.2.toHolValue))).map Prod.snd))
        (fun pair => panShapeMatches pair.1 (holShapeOf pair.2))
      = List.all
        ((expected.map Prod.snd).zip (actual.map Prod.snd))
        (fun pair => panShapeMatches pair.1 (panValueShape ([] : StructContext) pair.2)) :=
  panValueFieldsShapeHOL_eq ([] : StructContext) expected actual

example (info : StructInfo) (actual : List (FieldName × PanValue (BitVec 64))) :
    panValueFieldsExactHOL ([] : StructContext) info.fields actual =
      (decide (info.fields.map Prod.fst = actual.map Prod.fst) &&
        List.all
          ((info.fields.map Prod.snd).zip
            ((actual.map (fun pair => (pair.1, pair.2.toHolValue))).map Prod.snd))
          (fun pair => panShapeMatches pair.1 (holShapeOf pair.2))) :=
  panValueFieldsExactHOL_eq_evalHOL ([] : StructContext) info actual

#guard panValueFieldsExactHOL ([] : StructContext) [("f", Shape.one)]
    [("f", PanValue.word (7 : BitVec 64))] ==
  (decide ((["f"] : List FieldName) = ["f"]) &&
    List.all [(Shape.one, (PanValue.word (7 : BitVec 64)).toHolValue)]
      (fun pair => panShapeMatches pair.1 (holShapeOf pair.2)))

/- Modular production-to-`evalHOL` bridges at a concrete state (bead
   flapjack-pxn.18.3.6.9.2); the per-expression agreement is supplied by the
   `Const` clause for these concrete single-element lists. -/
example (value : BitVec 64) :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.const value)
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.const value)).map HolValue.toPanValue :=
  evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) value

example (value : BitVec 64) :
    evalPanValueExp.evalPanValueExps ([] : StructContext) (fun _ => none) (fun _ => none)
        (fun _ => none) 0 0 panSemBitVec64BytesInWord [.const value]
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalListHOL holEvalState [.const value]).map (List.map HolValue.toPanValue) :=
  evalPanValueExps_eq_evalListHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) [.const value]
    (fun expression hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
        (fun _ => none) (fun _ => none) (fun _ => none) 0 0
        panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) value)

example (value : BitVec 64) :
    evalPanValueExp.evalPanValueFields ([] : StructContext) (fun _ => none) (fun _ => none)
        (fun _ => none) 0 0 panSemBitVec64BytesInWord [("f", .const value)]
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalFieldsHOL holEvalState [("f", .const value)]).map
          (List.map (fun pair => (pair.1, HolValue.toPanValue pair.2))) :=
  evalPanValueFields_eq_evalFieldsHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) [("f", .const value)]
    (fun pair hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
        (fun _ => none) (fun _ => none) (fun _ => none) 0 0
        panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) value)


/- State-projection clause bridges (bead flapjack-pxn.18.3.6.9.2.6): the leaf
   clauses agree given the environment/state agreement hypotheses. -/
example (name : VarName) :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.var .local name)
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.var .local name)).map HolValue.toPanValue :=
  evalPanValueExp_var_local_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) name (fun _ => rfl)

example (name : VarName) :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.var .global name)
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.var .global name)).map HolValue.toPanValue :=
  evalPanValueExp_var_global_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) name (fun _ => rfl)

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord .baseAddr
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState .baseAddr).map HolValue.toPanValue :=
  evalPanValueExp_baseAddr_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) rfl

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord .topAddr
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState .topAddr).map HolValue.toPanValue :=
  evalPanValueExp_topAddr_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) rfl

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord .bytesInWord
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState .bytesInWord).map HolValue.toPanValue :=
  evalPanValueExp_bytesInWord_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) rfl

/- `rStruct`/`rField` clause bridges (bead flapjack-pxn.18.3.6.9.2.7), matched
   against the direct HOL `rstruct_pair`/`rfield_*` rows. -/
def rStructWords (result : Option (HolValue 64)) : Option (List Word64) :=
  match result with
  | some (.rStruct values) =>
      some (values.map (fun value => match value with | .val (.word word) => word | _ => 0))
  | _ => none

#guard rStructWords (evalHOL holEvalState (.rStruct [.const 3, .const 4])) == some [3, 4]
#guard evalWordResult (evalHOL holEvalState (.rField 0 (.rStruct [.const 3, .const 4]))) == some 3
#guard evalWordResult (evalHOL holEvalState (.rField 1 (.rStruct [.const 3, .const 4]))) == some 4
#guard evalResultIsNone (evalHOL holEvalState (.rField 2 (.rStruct [.const 3, .const 4])))
#guard evalResultIsNone (evalHOL holEvalState (.rField 0 (.const 3)))

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.rStruct [.const 3, .const 4])
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.rStruct [.const 3, .const 4])).map HolValue.toPanValue :=
  evalPanValueExp_rStruct_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) [.const 3, .const 4]
    (fun expression hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 3
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 4)

example (index : Nat) :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.rField index (.const 3))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.rField index (.const 3))).map HolValue.toPanValue :=
  evalPanValueExp_rField_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) index (.const 3)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (panSemBitVec64MemoryAccess littleEndianState)) 3)

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.op .add [.const 1, .const 2])
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.op .add [.const 1, .const 2])).map HolValue.toPanValue :=
  evalPanValueExp_op_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (panSemBitVec64MemoryAccess littleEndianState) .add [.const 1, .const 2]
    (fun expression hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 1
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 2)
    (fun op values => rfl)

def evalPanValueWordResult (result : Option (PanValue (BitVec 64))) : Option Word64 :=
  match result with
  | some (.word value) => some value
  | _ => none

#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
      0 0 panSemBitVec64BytesInWord (.op .add [.const 1, .const 2])
      (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))) == some 3

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.panOp .mul [.const 3, .const 4])
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holEvalState (.panOp .mul [.const 3, .const 4])).map HolValue.toPanValue :=
  evalPanValueExp_panOp_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (some (panSemBitVec64MemoryAccess littleEndianState)) .mul [.const 3, .const 4]
    (fun expression hmem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 3
      · exact evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext)
          (fun _ => none) (fun _ => none) (fun _ => none) 0 0
          panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess littleEndianState)) 4)

#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
      0 0 panSemBitVec64BytesInWord (.panOp .mul [.const 3, .const 4])
      (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))) == some 12
def storeMem : RiscV.Word 8 → HolWordLab 8 :=
  fun _ => .word (BitVec.ofNat 8 0x01)

def storeDomain : RiscV.Word 8 → Prop :=
  fun address => address = (1 : RiscV.Word 8) ∨ address = 2

instance : DecidablePred storeDomain := fun x => by
  unfold storeDomain
  infer_instance

#guard (panMemStoreByteHOL (width := 8) storeMem storeDomain false (1 : RiscV.Word 8)
    0xAB).isSome
#guard (panMemStoreByteHOL (width := 8) storeMem (fun _ => False) false
    (1 : RiscV.Word 8) 0xAB).isNone
#guard ((panMemStoreByteHOL (width := 8) storeMem storeDomain false
      (1 : RiscV.Word 8) 0xAB).map (fun memory => memory 3)) == some (storeMem 3)
#guard ((panWriteBytearrayHOL (width := 8) (1 : RiscV.Word 8) [0x11, 0x22] storeMem
      storeDomain false) 3) == storeMem 3
#guard ((panWriteBytearrayHOL (width := 8) (1 : RiscV.Word 8) [0x11, 0x22] storeMem
      storeDomain false) 1) != storeMem 1
#guard ((panWriteBytearrayHOL (width := 8) (5 : RiscV.Word 8) [0x11] storeMem
      storeDomain false) 1) == storeMem 1


def holCodecAccess (state : PanSemState (RiscV.Word 64) Unit) :
    PanValueMemoryAccess (RiscV.Word 64) :=
  { panSemBitVec64MemoryAccess state with
    compare := fun op l r => (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op l r then 1 else 0)
    shift := fun op l r => wordShiftHOL op l r.toNat }

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.cmp .equal (.const 3) (.const 3))
        (memoryAccess := some (holCodecAccess littleEndianState))
      = (evalHOL holEvalState (.cmp .equal (.const 3) (.const 3))).map HolValue.toPanValue :=
  evalPanValueExp_cmp_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (holCodecAccess littleEndianState) .equal (.const 3) (.const 3)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holCodecAccess littleEndianState)) 3)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holCodecAccess littleEndianState)) 3)
    (by intro op l r; rfl)

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.shift .lsl (.const 1) (.const 2))
        (memoryAccess := some (holCodecAccess littleEndianState))
      = (evalHOL holEvalState (.shift .lsl (.const 1) (.const 2))).map HolValue.toPanValue :=
  evalPanValueExp_shift_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (holCodecAccess littleEndianState) .lsl (.const 1) (.const 2)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holCodecAccess littleEndianState)) 1)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holCodecAccess littleEndianState)) 2)
    (by intro op l r; rfl)

/-- Access whose `read32`/`readByte` are the exact tagged HOL load functions on
    `holEvalState`, used by the production `load32`/`loadByte` clause bridges. -/
def holLoadAccess (base : PanValueMemoryAccess (RiscV.Word 64)) :
    PanValueMemoryAccess (RiscV.Word 64) :=
  { base with
    read32 := fun _ _ _ address =>
      (panMemLoad32HOL (width := 64) holEvalState.memory holEvalState.memaddrs
          holEvalState.be address).map (fun value => BitVec.ofNat 64 value.toNat),
    readByte := fun _ _ _ address =>
      (panMemLoadByteHOL (width := 64) holEvalState.memory holEvalState.memaddrs
          holEvalState.be address).map (fun byte => BitVec.ofNat 64 byte.toNat) }

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.load32 (.const 0))
        (memoryAccess := some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState)))
      = (evalHOL holEvalState (.load32 (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_load32_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState)) (.const 0)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState))) 0)
    (by intro word; simp only [holLoadAccess]; rw [Option.map_map]; rfl)

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.loadByte (.const 0))
        (memoryAccess := some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState)))
      = (evalHOL holEvalState (.loadByte (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_loadByte_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState)) (.const 0)
    (evalPanValueExp_const_eq_evalHOL holEvalState ([] : StructContext) (fun _ => none)
      (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
      (some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState))) 0)
    (by intro word; simp only [holLoadAccess]; rw [Option.map_map]; rfl)

#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.load32 (.const 0))
        (memoryAccess := some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState))))
  == some (BitVec.ofNat 64 0x55667788)
#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) (fun _ => none)
        0 0 panSemBitVec64BytesInWord (.loadByte (.const 0))
        (memoryAccess := some (holLoadAccess (panSemBitVec64MemoryAccess littleEndianState))))
  == some (BitVec.ofNat 64 136)

/-- Exact source state matching the executed `littleEndianState` memory/domain
    for the structured `.load` bridge: memory is the word view of the production
    memory and `memaddrs` is the production machine domain. -/
abbrev holLoadState : PanSemHolState 64 Unit :=
  { holEvalState with
    memory := panValueWordHOL littleEndianState.memory
    memaddrs := panValueFlatMachineDomain littleEndianState littleEndianState.memory }

example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load Shape.one (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holLoadState (.load Shape.one (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_load_eq_evalHOL holLoadState littleEndianState littleEndianState.memory
    ([] : StructContext) (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    Shape.one (.const 0)
    (evalPanValueExp_const_eq_evalHOL holLoadState ([] : StructContext) (fun _ => none)
      (fun _ => none) littleEndianState.memory 0 0 panSemBitVec64BytesInWord
      (some (panSemBitVec64MemoryAccess littleEndianState)) 0)
    rfl rfl rfl rfl
    (by simp [isWfShape, StructContext.toHOL])

#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load Shape.one (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState)))
  == some sourceMemoryWord

/-- The arbitrary-`Shape` `.load` bridge also covers an ill-formed shape, where
both the production `panValueFlatLoad` and the tagged `isWfShapeHOL` guard fail. -/
example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load (.named "Nope") (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holLoadState (.load (.named "Nope") (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_load_eq_evalHOL_anyShape holLoadState littleEndianState littleEndianState.memory
    ([] : StructContext) (fun _ => none) (fun _ => none) 0 0 panSemBitVec64BytesInWord
    (.named "Nope") (.const 0)
    (evalPanValueExp_const_eq_evalHOL holLoadState ([] : StructContext) (fun _ => none)
      (fun _ => none) littleEndianState.memory 0 0 panSemBitVec64BytesInWord
      (some (panSemBitVec64MemoryAccess littleEndianState)) 0)
    rfl rfl rfl rfl

#guard evalPanValueWordResult
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load (.named "Nope") (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState)))
  == none

/-- The source and target `byte_align` renderings agree (`byte$byte_align_def`):
    this is the alignment half of the source/target byte-store correspondence. -/
example : riscvByteAlignHOL (9 : RiscV.Word 64) = panByteAlignHOL (9 : RiscV.Word 64) :=
  riscvByteAlignHOL_eq_panByteAlignHOL 9

example : riscvByteAlignHOL (17 : RiscV.Word 64) = panByteAlignHOL (17 : RiscV.Word 64) :=
  riscvByteAlignHOL_eq_panByteAlignHOL 17

/-- The source and target byte-read renderings agree, and both reproduce the
    direct HOL `get_byte` oracle rows `get_byte_0=8w`, `get_byte_1=7w`,
    `get_byte_7=1w` of `scripts/hol-probes/crep_runtime_ffi_boundary_probe.out`
    on the word `0x0102030405060708`. -/
example :
    panGetByteHOL (0 : RiscV.Word 64) (BitVec.ofNat 64 0x0102030405060708) false =
      (8 : UInt8) := by decide

example :
    panGetByteHOL (1 : RiscV.Word 64) (BitVec.ofNat 64 0x0102030405060708) false =
      (7 : UInt8) := by decide

example :
    panGetByteHOL (7 : RiscV.Word 64) (BitVec.ofNat 64 0x0102030405060708) false =
      (1 : UInt8) := by decide

example :
    riscvGetByteHOL false (1 : RiscV.Word 64) (BitVec.ofNat 64 0x0102030405060708) =
      (7 : UInt8) := by decide

example (address value : RiscV.Word 64) (bigEndian : Bool) :
    panGetByteHOL address value bigEndian = riscvGetByteHOL bigEndian address value :=
  panGetByteHOL_eq_riscvGetByteHOL address value bigEndian

/-- The whole-expression capstone type-checks for the bundled relation; the codec
    fields are the remaining executable-path obligations. -/
example
    (rel : PanValueEvalRel holLoadState littleEndianState ([] : StructContext)
      (fun _ => none) (fun _ => none) littleEndianState.memory 0 0 panSemBitVec64BytesInWord) :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load Shape.one (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL holLoadState (.load Shape.one (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_eq_evalHOL_of_rel holLoadState littleEndianState ([] : StructContext)
    (fun _ => none) (fun _ => none) littleEndianState.memory 0 0 panSemBitVec64BytesInWord rel
    (.load Shape.one (.const 0))

/-- The unconditional executed-path capstone: the projected state built from the
    executed `PanSemState` satisfies the relation with no codec hypotheses. -/
example :
    evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none) littleEndianState.memory
        0 0 panSemBitVec64BytesInWord (.load Shape.one (.const 0))
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL
            (machineHolState littleEndianState sourceFfiState littleEndianState.memory
              ([] : StructContext) (fun _ => none) (fun _ => none) 0 0)
            (.load Shape.one (.const 0))).map HolValue.toPanValue :=
  evalPanValueExp_eq_evalHOL_executed littleEndianState sourceFfiState
    littleEndianState.memory ([] : StructContext) (fun _ => none) (fun _ => none) 0 0
    (.load Shape.one (.const 0))

/-- Actual-state corollary: the executed `PanSemState`'s own fields feed the
    observational projection with no extra arguments. -/
example :
    evalPanValueExp littleEndianState.structs littleEndianState.locals littleEndianState.globals
        littleEndianState.memory littleEndianState.baseAddress littleEndianState.topAddress
        panSemBitVec64BytesInWord (.const 0)
        (memoryAccess := some (panSemBitVec64MemoryAccess littleEndianState))
      = (evalHOL
            (machineHolState littleEndianState sourceFfiState littleEndianState.memory
              littleEndianState.structs littleEndianState.locals littleEndianState.globals
              littleEndianState.baseAddress littleEndianState.topAddress)
            (.const 0)).map HolValue.toPanValue :=
  evalPanValueExp_eq_evalHOL_state littleEndianState sourceFfiState (.const 0)

/-! ### HOL `panSem` helper definitions (flapjack-pxn.18.4.3.77.8)

`nbOpHOL` is an exact tagged port. `lookupKvarHOL`/`setKvarHOL` are
FLAPJACK-SPECIFIC: their key type is Lean `String` while HOL `varname` is
`mlstring`, so they are untagged (exact MlString-keyed port tracked by
`flapjack-pxn.18.4.3.77.8.1`).

Direct-HOL rows in `scripts/hol-probes/pan_sem_e2e_probe.out`:
`nb_op_op8=1`, `nb_op_op16=2`, `nb_op_opW=0`, `nb_op_op32=4`,
`lookup_kvar_local=SOME (ValWord 3w)`, `lookup_kvar_global=SOME (ValWord 4w)`,
`lookup_kvar_missing=NONE`. -/

example : nbOpHOL OpSize.op8 = 1 := rfl
example : nbOpHOL OpSize.op16 = 2 := rfl
example : nbOpHOL OpSize.opW = 0 := rfl
example : nbOpHOL OpSize.op32 = 4 := rfl

/-- A state with one bound local and one bound global, mirroring the HOL rows. -/
abbrev kvarState : PanSemHolState 64 Unit :=
  { holEvalState with
    locals := fun name => if name = "x" then some (.val (.word 3)) else none
    globals := fun name => if name = "y" then some (.val (.word 4)) else none }

example : lookupKvarHOL VarKind.local "x" kvarState = some (.val (.word 3)) := rfl

example : lookupKvarHOL VarKind.global "y" kvarState = some (.val (.word 4)) := rfl

example : lookupKvarHOL VarKind.local "z" kvarState = none := rfl

example : (setKvarHOL VarKind.local "z" (.val (.word 5)) kvarState).locals "z"
    = some (.val (.word 5)) := rfl

example : (setKvarHOL VarKind.local "z" (.val (.word 5)) kvarState).locals "x"
    = some (.val (.word 3)) := rfl

/-! ## Exact HOL `dec_clock`/`fix_clock` parity

`scripts/hol-probes/pan_sem_e2e_probe.out` records the direct HOL EVAL rows
`dec_clock_step=<|clock := 4|>`, `fix_clock_clamps=(NONE,2)` and
`fix_clock_keeps_new=(NONE,4)`. The examples below check the exact ports
`decClockHOL`/`fixClockHOL` against those values. -/

example : (decClockHOL (width := 64) { holEvalState with clock := 5 }).clock = 4 := rfl

example :
    (fixClockHOL (width := 64) { holEvalState with clock := 2 }
      ((none : Option Nat), { holEvalState with clock := 7 })).2.clock = 2 := rfl

example :
    (fixClockHOL (width := 64) { holEvalState with clock := 9 }
      ((none : Option Nat), { holEvalState with clock := 4 })).2.clock = 4 := rfl

/-! ### Exact `mem_store`/`mem_stores` parity (flapjack-pxn.18.4.3.77.12)

Direct original-HOL EVAL rows for `mem_store_def`/`mem_stores_def`
(`cakeml/pancake/semantics/panSemScript.sml:373-386`) are checked in
`scripts/hol-probes/pan_flat_store_probe.out` (`store_hit`, `store_miss`,
`stores_hit`, `stores_blocked`). -/

abbrev flatStoreMemory : Word64 → HolWordLab 64 := fun _ => .word 0

abbrev flatStoreDomain : Word64 → Prop := fun address => address = 10 ∨ address = 18

#guard (panMemStoreHOL (10 : Word64) (.word 3) flatStoreDomain flatStoreMemory).map
  (fun memory => memory 10) == some (.word 3)
#guard (panMemStoreHOL (11 : Word64) (.word 3) flatStoreDomain flatStoreMemory).isNone
#guard (panMemStoresHOL (10 : Word64) [(.word 3), (.word 5)] flatStoreDomain
  flatStoreMemory).map (fun memory => (memory 10, memory 18)) == some ((.word 3), (.word 5))
#guard (panMemStoresHOL (10 : Word64) [(.word 3), (.word 5)]
  (fun address => address = 10) flatStoreMemory).isNone

/- Exact HOL `word_lab` helpers: `scripts/hol-probes/pan_sem_e2e_probe.out` rows
   `isWord_def_word=T` and `theWord_def_word=3w`. -/
example : isWordHOL (width := 64) (HolWordLab.word (3 : Word64)) = true :=
  isWordHOL_word 3
example : theWordHOL (width := 64) (HolWordLab.word (3 : Word64)) = 3 :=
  theWordHOL_word 3
#guard isWordHOL (width := 64) (HolWordLab.word (3 : Word64)) == true
#guard theWordHOL (width := 64) (HolWordLab.word (3 : Word64)) == 3

end Flapjack.Test.PanSemStateEvalParity
