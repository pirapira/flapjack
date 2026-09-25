/-
Parity fixtures for the exact `ExtCall` clause step
(`Flapjack/Pancake/Semantics/PanSem/ExtCallExact.lean`).

The three guards replay the direct original-HOL rows
`extcall_clause_returned`, `extcall_clause_bad_read`, and
`extcall_clause_final` in `scripts/hol-probes/pan_sem_e2e_probe.out`.
-/
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact

namespace Flapjack.Test.PanSemExtCallExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL)

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

/-- Memory with one byte `0xAB` at address zero and zeros elsewhere. -/
def memory8 : Word8 → HolWordLab 8 := fun address => if address = 0 then .word 0xAB else .word 0

abbrev domain8 : Word8 → Prop := fun address => address = 0 ∨ address = 1

/-- Oracle that echoes a same-length list of `0x42` bytes. -/
def returningFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ bytes => .ret () (bytes.map (fun _ => 0x42)),
    ffiState := (),
    ioEvents := [] }

/-- Oracle that immediately returns a terminal (failed) result. -/
def finalFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

abbrev baseState (ffi : HolFfiState Unit) (memory : Word8 → HolWordLab 8)
    (domain : Word8 → Prop) : PanSemStateExact 8 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := memory
    memaddrs := domain
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := ffi
    baseAddr := 0
    topAddr := 100 }

def evalExpressionFixture (state : PanSemStateExact 8 Unit) (expression : ExpHOL 8) :
    Option (ValueHOL 8) :=
  match expression with
  | .const value => some (.val (.word value))
  | .var .local name => state.locals name
  | _ => none

def isNoneResult : Option (PanSemResultExact 8) → Bool
  | none => true
  | _ => false

def isErrorResult : Option (PanSemResultExact 8) → Bool
  | some .error => true
  | _ => false

def isFinalFfiResult : Option (PanSemResultExact 8) → Bool
  | some (.finalFfi _) => true
  | _ => false

def localsWord (state : PanSemStateExact 8 Unit) (name : Flapjack.Pancake.PanLang.MlS) :
    Option Nat :=
  match state.locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

def memoryWord (state : PanSemStateExact 8 Unit) (address : Word8) : Option Nat :=
  match state.memory address with
  | .word value => some value.toNat

private abbrev returnedState : PanSemStateExact 8 Unit := baseState returningFfi memory8 domain8

private abbrev badReadState : PanSemStateExact 8 Unit :=
  baseState returningFfi memory8 (fun _ => False)

private abbrev finalState : PanSemStateExact 8 Unit :=
  { (baseState finalFfi memory8 domain8) with
      locals := fun name => if name = ml "v" then some (.val (.word 7)) else none }

/-- `ExtCall` returning bytes writes them back through `write_bytearray`. -/
def extCallReturnedGuard : Bool :=
  let result := extCallStepHOLExact returnedState
    evalExpressionFixture (ml "x") (.const 0) (.const 2) (.const 0) (.const 2)
  isNoneResult result.1 && memoryWord result.2 0 == some 0x42

/-- A failed byte-array read returns `Error` and keeps the state. -/
def extCallBadReadGuard : Bool :=
  let result := extCallStepHOLExact badReadState
    evalExpressionFixture (ml "x") (.const 0) (.const 2) (.const 0) (.const 2)
  isErrorResult result.1 && memoryWord result.2 0 == some 0xAB

/-- A terminal FFI result returns `FinalFFI` and clears the locals. -/
def extCallFinalGuard : Bool :=
  let result := extCallStepHOLExact finalState
    evalExpressionFixture (ml "x") (.const 0) (.const 2) (.const 0) (.const 2)
  isFinalFfiResult result.1 && (localsWord result.2 (ml "v")).isNone

def extCallExactGuard : Bool :=
  extCallReturnedGuard && extCallBadReadGuard && extCallFinalGuard

#eval extCallReturnedGuard
#eval extCallBadReadGuard
#eval extCallFinalGuard
#guard extCallReturnedGuard
#guard extCallBadReadGuard
#guard extCallFinalGuard
#guard extCallExactGuard

def runChecks : IO Bool := do
  if extCallExactGuard then
    IO.println "PASS exact panSem ExtCall clause step (3 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem ExtCall clause step (3 HOL rows)"
    pure false

end Flapjack.Test.PanSemExtCallExactParity
