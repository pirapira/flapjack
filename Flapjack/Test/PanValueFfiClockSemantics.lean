import Flapjack.PanValueFfiClockSemantics
import Flapjack.PanValueFfiClockProjection
import Flapjack.Test.PanValueFfiSemantics

/-! Executable regressions for the CakeML clock boundary. -/

namespace Flapjack

open RiscV

def clockedCallFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("returnOne", [], .return (.const (BitVec.ofNat 64 1)))]

def clockedBreakProgram : Prog (Word 64) :=
  .while (.const (BitVec.ofNat 64 1)) .break

def clockedTickAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 0 .tick

def clockedTickAtOne :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 1 .tick

def clockedBreak :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 1 clockedBreakProgram

def clockedCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    none "returnOne" []

def clockedProgramCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "returnOne" [])

def clockedProgramCallDestination :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun name => if name == "x" then some (.word (BitVec.ofNat 64 0)) else none)
    (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call (some (some (.local, "x"), none)) "returnOne" [])

def clockedCallAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 0
    none "returnOne" []

def clockedTimeoutFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("timeoutLoop", [], .while (.const (BitVec.ofNat 64 1)) .skip)]

def clockedCallBodyTimeout : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedTimeoutFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    none "timeoutLoop" []

def clockedProgramBodyTimeout : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedTimeoutFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "timeoutLoop" [])

def clockedDecCallAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 0
    (.decCall "x" .one "returnOne" [] .skip)

def clockedDecCallReturned : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.decCall "x" .one "returnOne" []
      (.return (.var .local "x")))

def clockedRaiseFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("raiseOne", [], .raise "E" (.const (BitVec.ofNat 64 1)))]

def clockedProgramRaisedCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "raiseOne" [])

def clockedDecCallRaised : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.decCall "x" .one "raiseOne" [] .skip)

def clockedCaughtCall : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (some (none, some ("E", "exceptionValue",
      .return (.var .local "exceptionValue")))) "raiseOne" []

def clockedProgramCaughtCall : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call (some (none, some ("E", "exceptionValue",
      .return (.var .local "exceptionValue")))) "raiseOne" [])

def clockedInvalidCallTerminal :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skip", [], .skip)] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "skip" []

def clockedBreakCallRejected : Bool :=
  match evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("break", [], .break)] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "break" [] with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

def clockedContinueCallRejected : Bool :=
  match evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("continue", [], .continue)] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "continue" [] with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

def clockedMissingCallRejected : Bool :=
  match evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "missing" [] with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

#guard clockedBreakCallRejected
#guard clockedContinueCallRejected
#guard clockedMissingCallRejected

def clockedIsWordLocal (expected : Word 64) : Option (PanValue (Word 64)) → Bool
  | some (.word value) => value == expected
  | _ => false

def clockedErrorPreservesCalleeLocal (expected : Word 64) :
    Option (PanValueFfiClockResult (Word 64) Unit) → Bool
  | some (.control (.error locals _ _ _), _) => clockedIsWordLocal expected (locals "p")
  | _ => false

def clockedErrorEmptiesLocals :
    Option (PanValueFfiClockResult (Word 64) Unit) → Bool
  | some (.control (.error locals _ _ _), _) => clockedIsWordLocal 9 (locals "p") == false
  | _ => false

def clockedBreakParamPreservesLocal : Bool :=
  clockedErrorPreservesCalleeLocal 9
    (evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [("breakp", ["p"], .break)] 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
      none "breakp" [.const (BitVec.ofNat 64 9)])

def clockedContinueParamPreservesLocal : Bool :=
  clockedErrorPreservesCalleeLocal 9
    (evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [("contp", ["p"], .continue)] 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
      none "contp" [.const (BitVec.ofNat 64 9)])

def clockedFallThroughParamPreservesLocal : Bool :=
  clockedErrorPreservesCalleeLocal 9
    (evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [("skipp", ["p"], .skip)] 0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
      none "skipp" [.const (BitVec.ofNat 64 9)])

def clockedCalleeErrorEmptiesLocals : Bool :=
  clockedErrorEmptiesLocals
    (evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler []
      [("errp", ["p"], .assign .local "q" (.const (BitVec.ofNat 64 7)))]
      0 100 8 20
      (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
      none "errp" [.const (BitVec.ofNat 64 9)])

#guard clockedBreakParamPreservesLocal
#guard clockedContinueParamPreservesLocal
#guard clockedFallThroughParamPreservesLocal
#guard clockedCalleeErrorEmptiesLocals

def clockedFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFinalState 10
    ((.dec "x" .one (.const (BitVec.ofNat 64 0))
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))) : Prog (Word 64))

def clockedDirectExtCallFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] []
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState 10
    (.extCall "final" (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)))
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def clockedCallFinalFfiFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("finalExt", [],
    .extCall "final" (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)))]

def clockedCallFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState 10 (.call none "finalExt" [])
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def clockedCallFinalFfiSteps : Option (PanValueFfiSteppedResult (Word 64) Unit) :=
  evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState none "finalExt" []
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

/- CakeML's `panSem.evaluate_def` handles `If` by evaluating a word-valued
   condition and selecting the nonzero branch (panSemScript.sml:618-621).
   This exact structured evaluator guard also exercises the ordinary memory
   load used by that equation; the removed compact evaluator had no source
   semantics or shape checks. -/
def exactMemoryBranch : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    statefulTestMemory statefulTestFfiState 1
    (.ite (.cmp .equal (.load .one (.const (BitVec.ofNat 64 8)))
      (.const (BitVec.ofNat 64 0x42)))
      (.return (.const (BitVec.ofNat 64 1)))
      (.return (.const (BitVec.ofNat 64 0))))
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

#guard
  match exactMemoryBranch with
  | some (.control (.returned _ _ _ _ [PanValue.word value]), 1) =>
      value == BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCallFinalFfi with
  | some (.control (.finalFfi locals _ _ _ event), 9) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedCallFinalFfiSteps with
  | some (.finalFfi locals _ _ _ event, _) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedTickAtOne with
  | some (.control (.normal _ _ _ _), 0) => true
  | _ => false

#guard
  match clockedBreak with
  | some (.control (.normal _ _ _ _), 0) => true
  | _ => false

#guard
  match clockedCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCallDestination with
  | some (.control (.normal locals _ _ _), 0) =>
      match locals "x" with
      | some (.word value) => value == BitVec.ofNat 64 1
      | _ => false
  | _ => false

#guard
  match clockedProgramRaisedCall with
  | some (.control (.raised locals _ _ _ "E" (PanValue.word value)), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedDecCallRaised with
  | some (.control (.raised locals _ _ _ "E" (PanValue.word value)), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCallAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedCallBodyTimeout with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedProgramBodyTimeout with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedDecCallAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedDecCallReturned with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCaughtCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "exceptionValue" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCaughtCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "exceptionValue" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedInvalidCallTerminal with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

/- The named result projection keeps the exact source state and remaining
   clock while making timeout and terminal FFI outcomes distinct. -/
#guard
  match clockedTickAtZero.map panValueFfiClockResultProjection with
  | some (.timeout locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedTickAtOne.map panValueFfiClockResultProjection with
  | some (.normal locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedFinalFfi.map panValueFfiClockResultProjection with
  | some (.finalFfi locals globals memory ffi event 10) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = () && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedDirectExtCallFinalFfi with
  | some (.control (.finalFfi locals _ _ _ event), 10) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false


end Flapjack
