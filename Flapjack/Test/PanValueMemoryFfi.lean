import Flapjack.PanValueFfiSemantics

/-! Regression for the bare-metal accelerator FFI boundary.  Unlike the
    CakeML byte-array FFI, the handler receives the source memory map and can
    replace it, which models an accelerator writing through a pointer. -/

namespace Flapjack

def memoryFfiTestContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun _ _ => []
    wordOfBytes := fun _ _ => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun value => value.toNat
    valueToNat := id }

def memoryFfiTestState : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

def memoryFfiTestHandler : PanValueStatefulFfiHandler Nat Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def memoryFfiAccelerator : PanValueMemoryFfiHandler Nat Unit :=
  fun function configuration _ array _ locals memory ffi =>
    if function == "accelerator" then
      some (locals, updatePanValueMemory memory array (.word (configuration + 1)), ffi)
    else none

def memoryFfiInitial : PanValueFfiProgramState Nat Unit :=
  { source :=
      { structs := []
        globals := fun _ => none
        functions := []
        returnShapes := []
        exceptions := []
        memory := fun _ => none
        baseAddress := 0
        topAddress := 1000
        bytesInWord := 1 }
    ffi := memoryFfiTestState }

def memoryFfiMain : Prog Nat :=
  .seq
    (.extCall "accelerator" (.const 7) (.const 0) (.const 200) (.const 1))
    (.return (.load .one (.const 200)))

def memoryFfiDeclarations : List (Decl Nat) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := memoryFfiMain, returnShape := .one }]

def memoryFfiSteppedResult :=
  evalPanValueFfiProgramStepped memoryFfiTestContext memoryFfiInitial
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryHandler := some memoryFfiAccelerator)

def memoryFfiResultHasWrite : Bool :=
  match memoryFfiSteppedResult with
  | some (.returned _ _ memory _ [.word value], _) =>
      value == 8 && match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard memoryFfiResultHasWrite

theorem memoryFfiStepped_projects_to_nonstepped :
    memoryFfiSteppedResult.map Prod.fst =
      evalPanValueFfiProgram memoryFfiTestContext memoryFfiInitial
        (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
        (memoryHandler := some memoryFfiAccelerator) := by
  exact evalPanValueFfiProgramStepped_fst memoryFfiTestContext memoryFfiInitial
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryHandler := some memoryFfiAccelerator)

end Flapjack
