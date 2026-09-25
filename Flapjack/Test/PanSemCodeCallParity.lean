import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-! Production source-state Call/DecCall parity over `PanSemState.code`.

The expected values are direct Cake/HOL EVAL rows from
`scripts/hol-probes/pan_sem_e2e_probe.out` (`call_clause_ok_none` and
`deccall_clause_ok`). Unlike the exact one-step clause fixtures, these cases
run the production recursive evaluator: function lookup comes from the
state-owned code map and the canonical fuel is derived from that same state.
-/

namespace Flapjack.Test.PanSemCodeCallParity

open Flapjack

private abbrev W8 := RiscV.Word 8

private def sourceContext : PanValueFfiContext W8 :=
  { sharedDomain := fun _ => false
    byteAlign := id
    bigEndian := false
    wordToBytes := fun _ _ => []
    wordOfBytes := fun _ _ => 0
    wordToByte := fun value => UInt8.ofNat value.toNat
    byteToWord := fun value => BitVec.ofNat 8 value.toNat
    valueToNat := fun value => value.toNat }

private def sourcePrimitive : PanPrimitiveHandler W8 := fun _ _ => none

private def sourceHandler : PanValueStatefulFfiHandler W8 Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

private def sourceCode : PanSemCodeMap W8 :=
  [("f", ([ ("a", Shape.one) ],
    Prog.return (.var .local "a"), Shape.one))]

private def sourceState (clock : Nat) : PanSemState W8 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := sourceCode
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 0 }

private def sourceCall : Prog W8 :=
  .call none "f" [.const (BitVec.ofNat 8 3)]

private def sourceDecCall : Prog W8 :=
  .decCall "r" Shape.one "f" [.const (BitVec.ofNat 8 3)]
    (.return (.var .local "r"))

private def returnedWord : Option (PanValueFfiClockResult W8 Unit) → Option Nat
  | some (.control (.returned _ _ _ _ [.word value]), _) => some value.toNat
  | _ => none

private def callResult :=
  panSemEvaluateCodeStateWithPostState sourceContext sourcePrimitive
    sourceHandler (BitVec.ofNat 8 8) (sourceState 5) sourceCall

private def decCallResult :=
  panSemEvaluateCodeStateWithPostState sourceContext sourcePrimitive
    sourceHandler (BitVec.ofNat 8 8) (sourceState 5) sourceDecCall

def callUsesStateCode : Bool :=
  match callResult with
  | some (result, _) => returnedWord result == some 3
  | none => false

def decCallUsesStateCode : Bool :=
  match decCallResult with
  | some (result, _) => returnedWord result == some 3
  | none => false

theorem callPreservesStateCode (result : PanValueFfiClockResult W8 Unit)
    (postState : PanSemState W8 (FfiState Unit))
    (heval : callResult = some (result, postState)) :
    postState.code = (sourceState 5).code :=
  panSemEvaluateCodeStateWithPostState_preserves_code sourceContext
    sourcePrimitive sourceHandler (BitVec.ofNat 8 8) (sourceState 5) sourceCall
    result postState heval

theorem decCallPreservesStateCode (result : PanValueFfiClockResult W8 Unit)
    (postState : PanSemState W8 (FfiState Unit))
    (heval : decCallResult = some (result, postState)) :
    postState.code = (sourceState 5).code :=
  panSemEvaluateCodeStateWithPostState_preserves_code sourceContext
    sourcePrimitive sourceHandler (BitVec.ofNat 8 8) (sourceState 5) sourceDecCall
    result postState heval

#guard callUsesStateCode
#guard decCallUsesStateCode

def runChecks : IO Bool := do
  if callUsesStateCode && decCallUsesStateCode then
    IO.println "PASS recursive source-state Call/DecCall match direct HOL rows"
    pure true
  else
    IO.println "FAIL recursive source-state Call/DecCall direct HOL parity"
    pure false

end Flapjack.Test.PanSemCodeCallParity
