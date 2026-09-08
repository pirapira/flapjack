import Flapjack.RiscV.PanMemory
import Flapjack.PanSteppedSemantics

/-!
Executable regressions for the shared Pancake word-cell memory model.

These examples deliberately exercise byte and 32-bit operations through the
generic model, rather than through the older RISC-V-specific wrappers.  This
keeps the source-memory contract visible at the point where later semantic
proofs will use it.
-/

namespace Flapjack

def memoryModelDomain : PanMemoryDomain (RiscV.Word 64) :=
  fun address => address == BitVec.ofNat 64 8

def memoryModelMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (BitVec.ofNat 64 0x0807060504030201)
    else none

def memoryModel : PanMemoryModel (RiscV.Word 64) :=
  RiscV.panRiscVMemoryModel

def memoryModelFfi : PanValueFfiHandler (RiscV.Word 64) :=
  fun _ _ _ _ _ locals => some locals

def memoryModelPrimitive : PanPrimitiveHandler (RiscV.Word 64) :=
  fun _ _ => some (.word 0)

def memoryModelReadByte : Option (RiscV.Word 64) :=
  panModelReadByte memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 9) false

def memoryModelRead32 : Option (RiscV.Word 64) :=
  panModelRead32 memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) false

def memoryModelByteStore : Option (PanFlatMemory (RiscV.Word 64)) :=
  panModelStoreByte memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 9) (BitVec.ofNat 64 0xaa) false

def memoryModelWordAfterByteStore : Option (RiscV.Word 64) := do
  let memory ← memoryModelByteStore
  panModelReadWord memoryModelDomain memory (BitVec.ofNat 64 8)

def memoryModel32Store : Option (PanFlatMemory (RiscV.Word 64)) :=
  panModelStore32 memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 8)
    (BitVec.ofNat 64 0x11223344) false

def memoryModelByteAfter32Store : Option (RiscV.Word 64) := do
  let memory ← memoryModel32Store
  panModelReadByte memoryModel memoryModelDomain memory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) false

def memoryModelLastByteAfter32Store : Option (RiscV.Word 64) := do
  let memory ← memoryModel32Store
  panModelReadByte memoryModel memoryModelDomain memory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 11) false

def memoryModelUnalignedRead : Option (RiscV.Word 64) :=
  panModelRead32 memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 9) false

def memoryModelOutOfDomainRead : Option (RiscV.Word 64) :=
  panModelReadByte memoryModel memoryModelDomain memoryModelMemory
    (BitVec.ofNat 64 8) (BitVec.ofNat 64 16) false

def memoryModelGenericByteProgram : Option (RiscV.Word 64) :=
  (evalPanFlatProg [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      memoryModelDomain (fun _ => some 0)
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 0xaa)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9)))))
      (memoryAccess := some (panMemoryAccessOfModel memoryModel))).bind
    fun result => match result.2.2.2 with
      | [.word value] => some value
      | _ => none

def memoryModelGeneric32Program : Option (RiscV.Word 64) :=
  (evalPanFlatProg [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      memoryModelDomain (fun _ => some 0)
      (.seq (.store32 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 0x11223344)))
        (.return (.load32 (.const (BitVec.ofNat 64 8)))))
      (memoryAccess := some (panMemoryAccessOfModel memoryModel))).bind
    fun result => match result.2.2.2 with
      | [.word value] => some value
      | _ => none

def memoryModelSteppedByteProgram : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun _ => none) (fun _ => none)
      (fun _ => some (.word 0))
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 0xaa)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9)))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.1 with
      | .returned _ _ _ [.word value] => some (value, result.2)
      | _ => none

def memoryModelSteppedShared16Program : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun name => if name == "x" then some (.word 0) else none)
      (fun _ => none) (fun address => (memoryModelMemory address).map .word)
      (.seq (.shMemStore .op16 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 0xbeef)))
        (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
          (.return (.var .local "x"))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.1 with
      | .returned _ _ _ [.word value] => some (value, result.2)
      | _ => none

def memoryModelPanValuesByteProgram : Option (RiscV.Word 64) :=
  (evalPanValueProg [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none)
      (fun _ => some (.word 0))
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 0xaa)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9)))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.2.2.2 with
      | [.word value] => some value
      | _ => none

def memoryModelControlByteProgram : Option (RiscV.Word 64) :=
  (evalPanValueProgWithCallsAndFfi []
      [("read", [], .return (.loadByte (.const (BitVec.ofNat 64 9))))]
      memoryModelFfi (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 30
      (fun name => if name == "x" then some (.word 0) else none)
      (fun _ => none) (fun _ => some (.word 0))
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 0xaa)))
        (.seq (.call (some (some (.local, "x"), none)) "read" [])
          (.return (.var .local "x"))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result with
      | .returned _ _ _ [.word value] => some value
      | _ => none

def memoryModelPrimitiveControlByteProgram : Option (RiscV.Word 64) :=
  (evalPanValueProgWithPrimitiveCallsAndFfi memoryModelPrimitive memoryModelFfi [] []
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 30
      (fun name => if name == "x" then some (.word 0) else none)
      (fun _ => none) (fun _ => some (.word 0))
      (.seq (.primitive "x" .addCarry [])
        (.seq (.storeByte (.const (BitVec.ofNat 64 9))
            (.const (BitVec.ofNat 64 0xaa)))
          (.seq (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 9)))
            (.return (.var .local "x")))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result with
      | .returned _ _ _ [.word value] => some value
      | _ => none

def memoryModelProgramState : PanValueProgramState (RiscV.Word 64) :=
  { structs := []
    globals := fun _ => none
    functions := []
    returnShapes := []
    exceptions := []
    memory := fun address => (memoryModelMemory address).map .word
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8 }

def memoryModelPublicProgram : Option (RiscV.Word 64) :=
  (panValueProgramResult memoryModelProgramState memoryModelPrimitive memoryModelFfi 30
      [.decl .one "initial" (.loadByte (.const (BitVec.ofNat 64 9))),
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.storeByte (.const (BitVec.ofNat 64 9))
               (.const (BitVec.ofNat 64 0xaa)))
             (.seq (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 9)))
               (.return (.var .local "x"))),
           returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun values => match values with
      | [.word value] => some value
      | _ => none

#guard memoryModelReadByte = some (BitVec.ofNat 64 2)
#guard memoryModelRead32 = some (BitVec.ofNat 64 0x04030201)
#guard memoryModelWordAfterByteStore =
  some (BitVec.ofNat 64 0x080706050403aa01)
#guard memoryModelByteAfter32Store = some (BitVec.ofNat 64 0x44)
#guard memoryModelLastByteAfter32Store = some (BitVec.ofNat 64 0x11)
#guard memoryModelUnalignedRead = none
#guard memoryModelOutOfDomainRead = none
#guard memoryModelGenericByteProgram = some (BitVec.ofNat 64 0xaa)
#guard memoryModelGeneric32Program = some (BitVec.ofNat 64 0x11223344)
#guard memoryModelSteppedByteProgram = some (BitVec.ofNat 64 0xaa, 7)
#guard memoryModelSteppedShared16Program = some (BitVec.ofNat 64 0xbeef, 9)
#guard memoryModelPanValuesByteProgram = some (BitVec.ofNat 64 0xaa)
#guard memoryModelControlByteProgram = some (BitVec.ofNat 64 0xaa)
#guard memoryModelPrimitiveControlByteProgram = some (BitVec.ofNat 64 0xaa)
#guard memoryModelPublicProgram = some (BitVec.ofNat 64 0xaa)

end Flapjack
