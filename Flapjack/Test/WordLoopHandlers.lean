import Flapjack.WordSemantics

/-!
Regression coverage for handler-aware Word loop execution.  These examples
exercise the two effects that were previously unavailable inside a Word loop:
an FFI action and a returning call followed by loop control.
-/

namespace Flapjack

def wordLoopHandlerTestState : RiscV.State 64 := RiscV.zeroState 64

def wordLoopHandlerTestFfi :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      RiscV.State 64 → Option (RiscV.State 64) :=
  fun _ _ _ _ _ state => some (RiscV.writeRegister state 7 (BitVec.ofNat 64 9))

example :
    RiscV.evalWordLoopProgWithHandlersAndFfi [] wordLoopHandlerTestFfi 4
        wordLoopHandlerTestState
        (.loop []
          (.seq
            (.ffi "bump" 2 3 4 5 ([], []))
            (.break 0)) []) =
      some (RiscV.WordLoopControlResult.normal
        (RiscV.writeRegister wordLoopHandlerTestState 7 (BitVec.ofNat 64 9))) := by
  have h2 : RiscV.registerOfNat 2 = some (2 : Fin 32) := by decide
  have h3 : RiscV.registerOfNat 3 = some (3 : Fin 32) := by decide
  have h4 : RiscV.registerOfNat 4 = some (4 : Fin 32) := by decide
  have h5 : RiscV.registerOfNat 5 = some (5 : Fin 32) := by decide
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopRepeatWithHandlersAndFfi, wordLoopHandlerTestFfi,
    h2, h3, h4, h5]

def wordLoopCallBody : WordProg (RiscV.Word 64) := .return 0 []

example :
    RiscV.evalWordLoopCallWithHandlersAndFfi
        [(1, [], wordLoopCallBody)] (fun _ _ _ _ _ state => some state) 3
        wordLoopHandlerTestState
          (some ([], ([], []), .skip, 0, 0)) (some 1) [] none =
      some (RiscV.WordLoopControlResult.normal wordLoopHandlerTestState) := by
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopCallWithHandlersAndFfi, RiscV.lookupWordFunction,
    RiscV.readWordRegisters, RiscV.bindWordRegisters,
    RiscV.assignWordRegisters, RiscV.clearWordRegisters, wordLoopCallBody]

example :
    RiscV.evalWordLoopProgWithHandlersAndFfi
        [(1, [], wordLoopCallBody)] (fun _ _ _ _ _ state => some state) 8
        wordLoopHandlerTestState
        (.loop []
          (.seq
            (.call (some ([], ([], []), .skip, 0, 0)) (some 1) [] none)
            (.break 0)) []) =
      some (RiscV.WordLoopControlResult.normal wordLoopHandlerTestState) := by
  simp [RiscV.evalWordLoopProgWithHandlersAndFfi,
    RiscV.evalWordLoopRepeatWithHandlersAndFfi,
    RiscV.evalWordLoopCallWithHandlersAndFfi,
    RiscV.lookupWordFunction, RiscV.readWordRegisters,
    RiscV.bindWordRegisters, RiscV.assignWordRegisters,
    RiscV.clearWordRegisters,
    wordLoopCallBody]

def wordLoopCallReturnBody : WordProg (RiscV.Word 64) := .return 0 [2]

example :
    RiscV.evalWordLoopCallWithHandlersAndFfi
        [(1, [2], wordLoopCallReturnBody)] (fun _ _ _ _ _ state => some state) 5
        wordLoopHandlerTestState
        (some ([3], ([], []), .skip, 0, 0)) (some 1) [2] none =
      some (RiscV.WordLoopControlResult.normal
        (RiscV.writeRegister wordLoopHandlerTestState 3 (BitVec.ofNat 64 0))) := by
  apply RiscV.evalWordLoopCallWithHandlersAndFfi_normal_of_eval
    (functions := [(1, [2], wordLoopCallReturnBody)])
    (ffiHandler := fun _ _ _ _ _ state => some state) (fuel := 4)
    (state := wordLoopHandlerTestState)
    (calleeState :=
      RiscV.writeRegister
        (RiscV.clearWordRegisters wordLoopHandlerTestState)
        2 (BitVec.ofNat 64 0))
    (bodyState :=
      RiscV.writeRegister
        (RiscV.clearWordRegisters wordLoopHandlerTestState)
        2 (BitVec.ofNat 64 0))
    (callerState :=
      RiscV.writeRegister wordLoopHandlerTestState 3 (BitVec.ofNat 64 0))
    (target := 1) (parameters := [2]) (arguments := [2]) (names := [3])
    (returnInfo := (([], []), .skip, 0, 0))
    (body := wordLoopCallReturnBody) (values := [BitVec.ofNat 64 0])
    (returnValues := [BitVec.ofNat 64 0])
  · rfl
  · simp [RiscV.readWordRegisters, RiscV.registerOfNat,
      RiscV.readRegister, RiscV.zeroState,
      wordLoopHandlerTestState]
  · simp [RiscV.bindWordRegisters, RiscV.clearWordRegisters,
      RiscV.registerOfNat, RiscV.writeRegister, wordLoopHandlerTestState]
  · simp [wordLoopCallReturnBody, RiscV.evalWordLoopProgWithHandlersAndFfi,
      RiscV.registerOfNat, RiscV.readRegister,
      RiscV.writeRegister]
  · simp [RiscV.assignWordRegisters, RiscV.registerOfNat,
      RiscV.writeRegister, RiscV.clearWordRegisters, RiscV.zeroState,
      wordLoopHandlerTestState]

def wordLoopCallRaiseBody : WordProg (RiscV.Word 64) := .raise 2

def wordLoopCallRaiseCalleeState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.clearWordRegisters
      (RiscV.writeRegister wordLoopHandlerTestState 2 (BitVec.ofNat 64 9)))
    2 (BitVec.ofNat 64 9)

def wordLoopCallRaiseResultState : RiscV.State 64 :=
  { (RiscV.writeRegister wordLoopHandlerTestState 2 (BitVec.ofNat 64 9)) with
    memory := wordLoopCallRaiseCalleeState.memory
    privilege := wordLoopCallRaiseCalleeState.privilege
    mode := wordLoopCallRaiseCalleeState.mode }

example :
    RiscV.evalWordLoopCallWithHandlersAndFfi
        [(1, [2], wordLoopCallRaiseBody)] (fun _ _ _ _ _ state => some state) 5
        (RiscV.writeRegister wordLoopHandlerTestState 2 (BitVec.ofNat 64 9))
        none (some 1) [2] none =
      some (RiscV.WordLoopControlResult.raised wordLoopCallRaiseResultState
        (BitVec.ofNat 64 9)) := by
  have hresult :=
    RiscV.evalWordLoopCallWithHandlersAndFfi_raise_none_of_eval
      (functions := [(1, [2], wordLoopCallRaiseBody)])
      (ffiHandler := fun _ _ _ _ _ state => some state) (fuel := 4)
      (state := RiscV.writeRegister wordLoopHandlerTestState 2
        (BitVec.ofNat 64 9))
      (calleeState :=
        RiscV.writeRegister
          (RiscV.clearWordRegisters
            (RiscV.writeRegister wordLoopHandlerTestState 2 (BitVec.ofNat 64 9)))
          2 (BitVec.ofNat 64 9))
      (bodyState := wordLoopCallRaiseCalleeState)
      (target := 1) (parameters := [2]) (arguments := [2])
      (body := wordLoopCallRaiseBody) (values := [BitVec.ofNat 64 9])
      (exceptionValue := 9)
      (by rfl)
      (by simp [RiscV.readWordRegisters, RiscV.registerOfNat,
        RiscV.readRegister, RiscV.writeRegister, wordLoopHandlerTestState])
      (by simp [RiscV.bindWordRegisters, RiscV.clearWordRegisters,
        RiscV.registerOfNat, RiscV.writeRegister, wordLoopHandlerTestState])
      (by simp [wordLoopCallRaiseBody,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.registerOfNat,
        RiscV.readRegister, RiscV.writeRegister, wordLoopCallRaiseCalleeState])
  simpa [wordLoopCallRaiseResultState] using hresult

end Flapjack
