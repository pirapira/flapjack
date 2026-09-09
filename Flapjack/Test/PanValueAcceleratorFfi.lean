import Flapjack.PanSteppedSemantics

/-! The accelerator-style ExtCall handler is independent of the CakeML
stateful FFI. In particular, it must still run when a byte-granular
memoryAccess model is installed. -/

namespace Flapjack

def acceleratorTestMemoryAccess : PanValueMemoryAccess Nat :=
  { domain := fun _ => true
    wordOp := fun _ _ => some 0
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => some 0
    readWord := fun _ _ _ _ => none
    readByte := fun _ _ _ _ => none
    read16 := fun _ _ _ _ => none
    read32 := fun _ _ _ _ => none
    storeWord := fun _ _ _ _ _ => none
    storeByte := fun _ _ _ _ _ => none
    store16 := fun _ _ _ _ _ => none
    store32 := fun _ _ _ _ _ => none
    sharedRead := fun _ _ _ _ => none
    sharedStore := fun _ _ _ _ _ => none }

def acceleratorTestHandler : PanValueAcceleratorFfiHandler Nat :=
  fun function configuration _ array _ locals memory =>
    if function == "accelerator" then
      some (locals, updatePanValueMemory memory array (.word (configuration + 1)))
    else none

def acceleratorTestProgram : Prog Nat :=
  .seq
    (.extCall "accelerator" (.const 7) (.const 0) (.const 200) (.const 1))
    (.return (.const 0))

def acceleratorTestResult :=
  evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
    [] [] 0 1000 1 20 (fun _ => none) (fun _ => none) (fun _ => none)
    acceleratorTestProgram
    (memoryAccess := some acceleratorTestMemoryAccess)
    (memoryHandler := some acceleratorTestHandler)

#guard
  acceleratorTestResult.map (fun (result, _) => match result with
    | .returned _ _ memory [PanValue.word 0] =>
        match memory 200 with
        | some (.word 8) => true
        | _ => false
    | _ => false) = some true

#guard
  (evalPanValueProgWithPrimitiveCallsAndFfi
    (fun _ _ => none) (fun _ _ _ _ _ locals => some locals) [] [] 0 1000 1 20
    (fun _ => none) (fun _ => none) (fun _ => none) acceleratorTestProgram
    (memoryAccess := some acceleratorTestMemoryAccess)
    (memoryHandler := some acceleratorTestHandler)).map (fun result => match result with
      | .normal _ _ memory =>
          match memory 200 with
          | some (.word 8) => true
          | _ => false
      | .returned _ _ memory [_] =>
          match memory 200 with
          | some (.word 8) => true
          | _ => false
      | _ => false) = some true

end Flapjack
