import Flapjack.Pancake.Semantics.PanSem.TickShMemExact

/-! # Parity for the exact panSem `Tick` and `ShMemLoad`/`ShMemStore` clause steps

Replays the direct original-HOL rows `tick_clock_zero` / `tick_clock_positive`
from `scripts/hol-probes/pan_sem_e2e_probe.out` and checks the evaluate-level
argument checks of the shared-memory clauses (missing/non-word destination,
address/value failures) plus the `nb_op` size mapping. The exact
`sh_mem_load`/`sh_mem_store` bodies are delegated to callbacks; the
`shmemload_missing_local` / `shmemload_out_of_domain` / `shmemstore_out_of_domain`
outcomes follow from those callbacks being the exact definitions. -/

namespace Flapjack.Test.PanSemTickShMemExactParity

open Flapjack
open Flapjack.Pancake.PanLang (ExpHOL)

abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

abbrev baseState (clock : Nat) : PanSemStateExact 8 Unit :=
  { locals := fun name => if name = ml "v" then some (.val (.word 7)) else none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 0 }

abbrev stateNoLocal (clock : Nat) : PanSemStateExact 8 Unit :=
  { baseState clock with locals := fun _ => none }

abbrev stateNonWordLocal : PanSemStateExact 8 Unit :=
  { baseState 0 with
      locals := fun name => if name = ml "v" then some (.rStruct []) else none }

def evalExpressionFixture (state : PanSemStateExact 8 Unit) : ExpHOL 8 → Option (ValueHOL 8)
  | .const value => some (.val (.word value))
  | .var .local name => state.locals name
  | .var .global name => state.globals name
  | _ => none

def runShMemLoadStub (_kind : VarKind) (_name : MlS) (_addr : RiscV.Word 8) (nb : Nat)
    (state : PanSemStateExact 8 Unit) :
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  (none, { state with clock := nb })

def runShMemStoreStub (bytes addr : RiscV.Word 8) (nb : Nat)
    (state : PanSemStateExact 8 Unit) :
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  (none, { state with clock := nb + bytes.toNat + addr.toNat })

def isNoneResult : Option (PanSemResultExact 8) → Bool
  | none => true
  | some _ => false

def isErrorResult : Option (PanSemResultExact 8) → Bool
  | some .error => true
  | _ => false

def isTimeOutResult : Option (PanSemResultExact 8) → Bool
  | some .timeOut => true
  | _ => false

def localsWord (locals : Flapjack.Pancake.PanLang.MlS → Option (ValueHOL 8))
    (name : Flapjack.Pancake.PanLang.MlS) : Option Nat :=
  match locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

/-- Direct HOL row `tick_clock_zero=(SOME TimeOut, NONE, 0)`. -/
def tickZeroGuard : Bool :=
  let result := tickStepHOLExact (baseState 0)
  isTimeOutResult result.1 && (localsWord result.2.locals (ml "v")).isNone
    && result.2.clock == 0

/-- Direct HOL row `tick_clock_positive=(NONE, SOME (ValWord 7w), 4)`. -/
def tickPosGuard : Bool :=
  let result := tickStepHOLExact (baseState 5)
  isNoneResult result.1 && localsWord result.2.locals (ml "v") == some 7
    && result.2.clock == 4

/-- `nb_op`: `OpW`/`Op8`/`Op16`/`Op32` give byte counts `0`/`1`/`2`/`4`. -/
def shMemLoadNbGuard : Bool :=
  let wide := shMemLoadStepHOLExact (baseState 0) .opW .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub
  let byte := shMemLoadStepHOLExact (baseState 0) .op8 .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub
  let half := shMemLoadStepHOLExact (baseState 0) .op16 .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub
  let word := shMemLoadStepHOLExact (baseState 0) .op32 .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub
  wide.2.clock == 0 && byte.2.clock == 1 && half.2.clock == 2 && word.2.clock == 4

/-- HOL `ShMemLoad` with a missing destination binding is `SOME Error`
(`shmemload_missing_local`). -/
def shMemLoadMissingGuard : Bool :=
  isErrorResult (shMemLoadStepHOLExact (stateNoLocal 0) .opW .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub).1

/-- HOL `ShMemLoad` with a non-word destination binding is `SOME Error`. -/
def shMemLoadNonWordGuard : Bool :=
  isErrorResult (shMemLoadStepHOLExact stateNonWordLocal .opW .local (ml "v") (.const 8)
    evalExpressionFixture runShMemLoadStub).1

/-- HOL `ShMemLoad` with a failing address expression is `SOME Error`. -/
def shMemLoadAddressErrorGuard : Bool :=
  isErrorResult (shMemLoadStepHOLExact (baseState 0) .opW .local (ml "v")
    (.var .local (ml "missing")) evalExpressionFixture runShMemLoadStub).1

/-- HOL `ShMemStore` passes the value first, then the address, then `nb_op op`. -/
def shMemStoreOkGuard : Bool :=
  let wide := shMemStoreStepHOLExact (baseState 0) .opW (.const 8) (.const 0xAB)
    evalExpressionFixture runShMemStoreStub
  let half := shMemStoreStepHOLExact (baseState 0) .op16 (.const 8) (.const 0xAB)
    evalExpressionFixture runShMemStoreStub
  wide.2.clock == 179 && half.2.clock == 181

/-- HOL `ShMemStore` with a failing address expression is `SOME Error`. -/
def shMemStoreAddressErrorGuard : Bool :=
  isErrorResult (shMemStoreStepHOLExact (baseState 0) .opW (.var .local (ml "missing"))
    (.const 0xAB) evalExpressionFixture runShMemStoreStub).1

/-- HOL `ShMemStore` with a non-word value is `SOME Error`. -/
def shMemStoreValueErrorGuard : Bool :=
  isErrorResult (shMemStoreStepHOLExact (baseState 0) .opW (.const 8)
    (.rstruct []) evalExpressionFixture runShMemStoreStub).1

abbrev returningFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ bytes => .ret () (bytes.map (fun _ => 0x42))
    ffiState := ()
    ioEvents := [] }

abbrev returningState : PanSemStateExact 8 Unit :=
  { baseState 0 with shMemaddrs := fun address => address = 8, ffi := returningFfi }

/-- Direct HOL row `shmemload_returned=(NONE, SOME (ValWord 0x42w))` end-to-end
through the exact clause and the exact `sh_mem_load` body. -/
def shMemLoadReturnedGuard : Bool :=
  let result := shMemLoadClauseHOLExact returningState .opW .local (ml "v") (.const 8)
    evalExpressionFixture
  isNoneResult result.1 && localsWord result.2.locals (ml "v") == some 0x42

/-- Direct HOL row `shmemload_missing_local=SOME Error`. -/
def shMemLoadClauseMissingGuard : Bool :=
  isErrorResult (shMemLoadClauseHOLExact (stateNoLocal 0) .opW .local (ml "v") (.const 8)
    evalExpressionFixture).1

/-- Direct HOL row `shmemload_out_of_domain=SOME Error`. -/
def shMemLoadClauseOutOfDomainGuard : Bool :=
  isErrorResult (shMemLoadClauseHOLExact (baseState 0) .opW .local (ml "v") (.const 8)
    evalExpressionFixture).1

/-- Direct HOL row `shmemstore_out_of_domain=SOME Error`. -/
def shMemStoreClauseOutOfDomainGuard : Bool :=
  isErrorResult (shMemStoreClauseHOLExact (baseState 0) .opW (.const 8) (.const 0xAB)
    evalExpressionFixture).1

def tickShMemGuard : Bool :=
  tickZeroGuard && tickPosGuard && shMemLoadNbGuard && shMemLoadMissingGuard
    && shMemLoadNonWordGuard && shMemLoadAddressErrorGuard && shMemStoreOkGuard
    && shMemStoreAddressErrorGuard && shMemStoreValueErrorGuard
    && shMemLoadReturnedGuard && shMemLoadClauseMissingGuard
    && shMemLoadClauseOutOfDomainGuard && shMemStoreClauseOutOfDomainGuard

example : (tickStepHOLExact (baseState 0)).2.clock = 0 := by
  rw [tickStepHOLExact_clock_zero _ rfl]
  simp [emptyLocalsHOLExact]

example : (tickStepHOLExact (baseState 5)).2.clock = 4 := by
  rw [tickStepHOLExact_clock_pos _ (by decide)]
  simp [decClockHOLExact]

example :
    shMemLoadStepHOLExact (baseState 0) .op8 .local (ml "v") (.const 8)
        evalExpressionFixture runShMemLoadStub =
      runShMemLoadStub .local (ml "v") 8 (nbOpHOL .op8) (baseState 0) :=
  shMemLoadStepHOLExact_ok _ _ _ _ _ _ _ 8 7 rfl (by simp [lookupKvarHOLExact])

example :
    shMemStoreStepHOLExact (baseState 0) .op16 (.const 8) (.const 0xAB)
        evalExpressionFixture runShMemStoreStub =
      runShMemStoreStub 0xAB 8 (nbOpHOL .op16) (baseState 0) :=
  shMemStoreStepHOLExact_ok _ _ _ _ _ _ 8 0xAB rfl rfl

#guard tickZeroGuard
#guard tickPosGuard
#guard shMemLoadNbGuard
#guard shMemLoadMissingGuard
#guard shMemLoadNonWordGuard
#guard shMemLoadAddressErrorGuard
#guard shMemStoreOkGuard
#guard shMemStoreAddressErrorGuard
#guard shMemStoreValueErrorGuard
#guard shMemLoadReturnedGuard
#guard shMemLoadClauseMissingGuard
#guard shMemLoadClauseOutOfDomainGuard
#guard shMemStoreClauseOutOfDomainGuard
#guard tickShMemGuard

def runChecks : IO Bool := do
  if tickShMemGuard then
    IO.println "PASS exact panSem Tick/ShMemLoad/ShMemStore clause steps (2 HOL tick rows + argument checks)"
    pure true
  else
    IO.println "FAIL exact panSem Tick/ShMemLoad/ShMemStore clause steps"
    pure false

end Flapjack.Test.PanSemTickShMemExactParity
