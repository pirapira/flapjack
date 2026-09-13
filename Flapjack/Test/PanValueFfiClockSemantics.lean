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

def clockedCallAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 0
    none "returnOne" []

def clockedRaiseFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("raiseOne", [], .raise "E" (.const (BitVec.ofNat 64 1)))]

def clockedCaughtCall : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (some (none, some ("E", "exceptionValue",
      .return (.var .local "exceptionValue")))) "raiseOne" []

def clockedInvalidCallTerminal :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skip", [], .skip)] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "skip" []

def clockedFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFinalState 10
    ((.dec "x" .one (.const (BitVec.ofNat 64 0))
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))) : Prog (Word 64))

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
  match clockedCallAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedCaughtCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "exceptionValue" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard clockedInvalidCallTerminal.isNone

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

end Flapjack
