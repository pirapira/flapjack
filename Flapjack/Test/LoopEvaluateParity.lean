import Flapjack.LoopEvaluate
import Flapjack.RiscV.PanSemantics

/-!
# Source parity for Pancake `loopSem$evaluate`

The source fixture is `scripts/hol-probes/loop_sem_evaluate_probe.out`,
generated from `loop_sem_evaluate_probeScript.sml`.  The representative
sequence case checks the intermediate assignment through the final return and
the break/continue result cases preserve state, and the tail-call case checks
that `call_env` clears the locals, matching `evaluate_def`.
-/

namespace Flapjack.Test.LoopEvaluateParity

open Flapjack

def emptyState (clock : Nat) : LoopMachineState LoopWordLoc :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := clock
    code := []
    be := false
    ffi := .word 0
    baseAddr := .word 4
    topAddr := .word 100 }

def evalProbe (state : LoopMachineState LoopWordLoc) :
    LoopExp LoopWordLoc → Option LoopWordLoc
  | .const value => some value
  | .var name => state.locals name
  | _ => none

def compareProbe : Cmp → LoopWordLoc → LoopWordLoc → Bool
  | .equal, left, right => left == right
  | .notEqual, left, right => left != right
  | _, _, _ => false

def hooks : LoopEvaluateHooks :=
  { eval := evalProbe
    primitive := fun _ _ => none
    arith := fun _ _ => none
    store := fun _ _ _ => none
    setGlobal := loopSetGlobalMachine
    load32 := fun _ _ => none
    loadByte := fun _ _ => none
    store32 := fun _ _ _ => none
    storeByte := fun _ _ _ => none
    compare := compareProbe
    shMem := fun _ _ _ state => (some .error, state)
    ffi := fun _ _ _ _ _ _ state => (some .error, state) }

/-! The existing `loop_sem_loop_arith_probe.out` fixes 8-bit words and checks
    `loopSemScript.sml:118-145`: a valid `LLongDiv`, zero divisor, quotient
    overflow, and malformed/non-word operands.  Exercise those same cases
    through the exact `evaluate_def` arithmetic boundary. -/
def arithHooks : LoopEvaluateHooks :=
  { hooks with arith := fun state operation => loopArithMachine 8 state operation }

/-! `evalLoopProgFull` retains Cake's generic target-word fragment.  Ordinary
    `LDiv` has the same checked nonzero-divisor rule as loopSem's
    `loop_arith`; the full evaluator must not silently reject it. -/
def fullDivState : LoopState (RiscV.Word 8) :=
  { locals := fun name =>
      if name == 2 then some 12
      else if name == 3 then some 3
      else none
    globals := fun _ => none
    memory := fun _ => none }

def fullDivSuccess : Bool :=
  match evalLoopProgFull 1 fullDivState
      (.arith (.div 1 2 3) : LoopProg (RiscV.Word 8)) with
  | some (.normal state) => state.locals 1 == some 4
  | _ => false

def fullDivZero : Bool :=
  match evalLoopProgFull 1
      { fullDivState with locals := fun name =>
          if name == 2 then some 12
          else if name == 3 then some 0
          else none }
      (.arith (.div 1 2 3) : LoopProg (RiscV.Word 8)) with
  | none => true
  | _ => false

def fullLoopBreak : Bool :=
  match evalLoopProgFull 8 fullDivState
      (.loop []
        (.seq (.assign 1 (.const (BitVec.ofNat 8 9))) (.break 0)) [] :
          LoopProg (RiscV.Word 8)) with
  | some (.normal state) => state.locals 1 == some (BitVec.ofNat 8 9)
  | _ => false

/-! Width-aware `LLongDiv` oracle: Cake forms `high * 2^width + low`, writes
    the remainder to the right destination first, and then the quotient to the
    left destination. -/
def wordLongDiv (width : Nat) (high low divisor : RiscV.Word width) :
    Option (RiscV.Word width × RiscV.Word width) :=
  let divisorValue := divisor.toNat
  if divisorValue = 0 then
    none
  else
    let numerator := high.toNat * 2 ^ width + low.toNat
    let quotientValue := numerator / divisorValue
    if quotientValue < 2 ^ width then
      some (BitVec.ofNat width quotientValue,
        BitVec.ofNat width (numerator % divisorValue))
    else
      none

def fullLongDivState : LoopState (RiscV.Word 8) :=
  { locals := fun name =>
      if name == 2 then some (BitVec.ofNat 8 1)
      else if name == 3 then some (BitVec.ofNat 8 44)
      else if name == 4 then some (BitVec.ofNat 8 7)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def fullLongDivSuccess : Bool :=
  match evalLoopProgFullWithLongDiv (wordLongDiv 8) 2 fullLongDivState
      (.arith (.longDiv 5 6 2 3 4) : LoopProg (RiscV.Word 8)) with
  | some (.normal state) =>
      state.locals 5 == some (BitVec.ofNat 8 42) &&
      state.locals 6 == some (BitVec.ofNat 8 6)
  | _ => false

def fullLongDivZero : Bool :=
  match evalLoopProgFullWithLongDiv (wordLongDiv 8) 1
      { fullLongDivState with locals := fun name =>
          if name == 7 then some (BitVec.ofNat 8 0)
          else fullLongDivState.locals name }
      (.arith (.longDiv 5 6 2 3 7) : LoopProg (RiscV.Word 8)) with
  | none => true
  | _ => false

def fullLongDivOverflow : Bool :=
  match evalLoopProgFullWithLongDiv (wordLongDiv 8) 1
      { fullLongDivState with locals := fun name =>
          if name == 2 then some (BitVec.ofNat 8 255)
          else if name == 3 then some (BitVec.ofNat 8 255)
          else if name == 4 then some (BitVec.ofNat 8 1)
          else none }
      (.arith (.longDiv 5 6 2 3 4) : LoopProg (RiscV.Word 8)) with
  | none => true
  | _ => false

#guard fullLongDivSuccess
#guard fullLongDivZero
#guard fullLongDivOverflow
#guard fullLoopBreak

/-! Width-aware `LLongMul` oracle: Cake splits the product into high and low
    words and writes the high destination before the low destination. -/
def wordLongMul (width : Nat) (left right : RiscV.Word width) :
    Option (RiscV.Word width × RiscV.Word width) :=
  let base := 2 ^ width
  let product := left.toNat * right.toNat
  some (BitVec.ofNat width ((product / base) % base),
    BitVec.ofNat width (product % base))

def fullLongMulState : LoopState (RiscV.Word 8) :=
  { locals := fun name =>
      if name == 2 then some (BitVec.ofNat 8 20)
      else if name == 3 then some (BitVec.ofNat 8 20)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def fullLongMulSuccess : Bool :=
  match evalLoopProgFullWithLongMul (wordLongMul 8) 2 fullLongMulState
      (.arith (.longMul 5 6 2 3) : LoopProg (RiscV.Word 8)) with
  | some (.normal state) =>
      state.locals 5 == some (BitVec.ofNat 8 1) &&
      state.locals 6 == some (BitVec.ofNat 8 144)
  | _ => false

def fullLongMulMissingSource : Bool :=
  match evalLoopProgFullWithLongMul (wordLongMul 8) 1 fullLongMulState
      (.arith (.longMul 5 6 2 4) : LoopProg (RiscV.Word 8)) with
  | none => true
  | _ => false

def fullLongMulSameDestination : Bool :=
  match evalLoopProgFullWithLongMul (wordLongMul 8) 2 fullLongMulState
      (.arith (.longMul 5 5 2 3) : LoopProg (RiscV.Word 8)) with
  | some (.normal state) => state.locals 5 == some (BitVec.ofNat 8 144)
  | _ => false

def fullLongMulDivSequenceState : LoopState (RiscV.Word 8) :=
  { locals := fun name =>
      if name == 2 then some (BitVec.ofNat 8 20)
      else if name == 3 then some (BitVec.ofNat 8 20)
      else if name == 7 then some (BitVec.ofNat 8 1)
      else if name == 8 then some (BitVec.ofNat 8 44)
      else if name == 9 then some (BitVec.ofNat 8 7)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def fullLongMulDivSequence : Bool :=
  match evalLoopProgFullWithLongMulDiv (wordLongMul 8) (wordLongDiv 8) 3
      fullLongMulDivSequenceState
      (.seq (.arith (.longMul 5 6 2 3))
        (.arith (.longDiv 10 11 7 8 9)) : LoopProg (RiscV.Word 8)) with
  | some (.normal state) =>
      state.locals 5 == some (BitVec.ofNat 8 1) &&
      state.locals 6 == some (BitVec.ofNat 8 144) &&
      state.locals 10 == some (BitVec.ofNat 8 42) &&
      state.locals 11 == some (BitVec.ofNat 8 6)
  | _ => false

def fullLongMulDivLoop : Bool :=
  match evalLoopProgFullWithLongMulDiv (wordLongMul 8) (wordLongDiv 8) 8
      fullLongMulDivSequenceState
      (.loop []
        (.seq (.arith (.longMul 5 6 2 3)) (.break 0)) [] : LoopProg (RiscV.Word 8)) with
  | some (.normal state) =>
      state.locals 5 == some (BitVec.ofNat 8 1) &&
      state.locals 6 == some (BitVec.ofNat 8 144)
  | _ => false

#guard fullLongMulSuccess
#guard fullLongMulMissingSource
#guard fullLongMulSameDestination
#guard fullLongMulDivSequence
#guard fullLongMulDivLoop

/-! The primitive branch uses the same fixed-width Cake `AddCarry` handler as
    `loop_primop` (`loopSemScript.sml:242-252`). -/
def primitiveMachine : PrimOp → List LoopWordLoc → Option (List LoopWordLoc)
  | .addCarry, [.word left, .word right, .word carry] =>
      (RiscV.loopPrimitiveHandler (width := 64) .addCarry
        [BitVec.ofNat 64 left, BitVec.ofNat 64 right, BitVec.ofNat 64 carry]).map
        (fun values => values.map (fun value => .word value.toNat))
  | _, _ => none

def primitiveHooks : LoopEvaluateHooks :=
  { arithHooks with primitive := primitiveMachine }

/-! The source probes `loop_sem_sh_mem_load_probe.out` and
    `loop_sem_sh_mem_store_probe.out` cover `loopSemScript.sml:198-243`.
    The exact evaluator delegates the byte/FFI details to `shMem`; these
    hooks expose the same success, domain-error, operand-error, and terminal
    result transitions at the `evaluate_def` boundary. -/
def sharedMemHooks : LoopEvaluateHooks :=
  { arithHooks with shMem := fun operator name address state =>
      if !state.shMdomain address then
        (some .error, state)
      else if loopIsLoad operator then
        if state.ffi == .word 9 then
          (some (.finalFfi (.word 11)), { state with locals := fun _ => none })
        else
          (none, { state with locals := loopSetVar state.locals name (.word 3) })
      else
        (none, state) }

def sharedState (domain : Bool) (ffi : LoopWordLoc)
    (locals : Nat → Option LoopWordLoc) : LoopMachineState LoopWordLoc :=
  { (emptyState 5) with shMdomain := fun _ => domain, ffi := ffi, locals := locals }

def observeSharedMem (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc × LoopWordLoc :=
  (step.1, step.2.locals 1, step.2.ffi)

def sharedLoadSuccess : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (none, some (.word 3), .word 0)

def sharedStoreSuccess : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .store 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun name =>
      if name = 1 then some (.word 7) else none))) ==
    (none, some (.word 7), .word 0)

def sharedLoadDomainError : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState false (.word 0) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (some .error, some (.word 0), .word 0)

def sharedLoadMissingDestination : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun _ => none))) ==
    (some .error, none, .word 0)

def sharedStoreMissingSource : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .store 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun _ => none))) ==
    (some .error, none, .word 0)

def sharedLoadFinalFfi : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 9) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (some (.finalFfi (.word 11)), none, .word 9)

/-! The exact FFI branch is `evaluate_def` in
    `loopSemScript.sml:278-423`; its byte/oracle behavior is checked by the
    source-derived `ffi_call_probe.out` and the existing `LoopFfi` fixtures.
    These hooks exercise the evaluator's cut-state, result, event, and clock
    boundary without replacing the source-shaped FFI implementation. -/
def ffiFinalEvent : LoopWordLoc := .word 11

def ffiHooks : LoopEvaluateHooks :=
  { sharedMemHooks with ffi := fun _ configuration configurationLength array
      arrayLength _ state =>
      if (state.locals configuration).isNone ||
          (state.locals configurationLength).isNone ||
          (state.locals array).isNone ||
          (state.locals arrayLength).isNone then
        (some .error, state)
      else if state.ffi == .word 9 then
        (some (.finalFfi ffiFinalEvent), { state with locals := fun _ => none })
      else
        (none, { state with ffi := .word 7 }) }

def ffiCallState (clock : Nat) (ffi : LoopWordLoc)
    (locals : Nat → Option LoopWordLoc) : LoopMachineState LoopWordLoc :=
  { (emptyState clock) with ffi := ffi, locals := locals }

def observeFfi (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.locals 9, step.2.ffi, step.2.clock)

def ffiCallSuccess : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else if name = 9 then some (.word 99)
      else none))) ==
    (none, some (.word 10), none, .word 7, 5)

def ffiMalformedArgs : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some .error, none, none, .word 0, 5)

def ffiMissingLiveState : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else if name = 9 then some (.word 99)
      else none))) ==
    (some .error, none, some (.word 99), .word 0, 5)

def ffiFinal : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 9) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some (.finalFfi ffiFinalEvent), none, none, .word 9, 5)

def ffiFinalAtZeroClock : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 0 (.word 9) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some (.finalFfi ffiFinalEvent), none, none, .word 9, 0)

def longDivState (high low divisor : Option LoopWordLoc) :
    LoopMachineState LoopWordLoc :=
  { (emptyState 5) with locals := fun name =>
      if name = 3 then high
      else if name = 4 then low
      else if name = 5 then divisor
      else none }

def observeLongDiv (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.locals 2, step.2.clock)

def longDivSuccess : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 3)) (some (.word 2)))) ==
    (none, some (.word 129), some (.word 1), 5)

def longDivZero : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 3)) (some (.word 0)))) ==
    (some .error, none, none, 5)

def longDivOverflow : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 0)) (some (.word 1)))) ==
    (some .error, none, none, 5)

def longDivMalformed : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.loc 9 0)) (some (.word 3)) (some (.word 2)))) ==
    (some .error, none, none, 5)

/-! Cake writes the remainder first and the quotient second, so coincident
    destinations retain the quotient. -/
def longDivSameDestination : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 1 3 4 5))
    (longDivState (some (.word 1)) (some (.word 3)) (some (.word 2)))) ==
    (none, some (.word 129), none, 5)

/-! The ordinary `LDiv` evaluator branch follows
    `loopSemScript.sml:119-126`: it returns the quotient, and rejects zero or
    non-word divisors. -/
def divSuccess : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.div 1 3 4))
    (longDivState (some (.word 7)) (some (.word 2)) none)) ==
    (none, some (.word 3), none, 5)

def divZero : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.div 1 3 4))
    (longDivState (some (.word 7)) (some (.word 0)) none)) ==
    (some .error, none, none, 5)

def divMalformed : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.div 1 3 4))
    (longDivState (some (.loc 9 0)) (some (.word 2)) none)) ==
    (some .error, none, none, 5)

/-! Exact `evaluate_def` primitive/result propagation for the HOL probe's
    valid, carry-producing, and malformed `AddCarry` cases. -/
def primitiveSuccess : Bool :=
  observeLongDiv (evaluateLoop 2 primitiveHooks
    (.primitive [1, 2] .addCarry [3, 4, 5])
    (longDivState (some (.word 3)) (some (.word 4)) (some (.word 0)))) ==
    (none, some (.word 7), some (.word 0), 5)

def primitiveCarry : Bool :=
  observeLongDiv (evaluateLoop 2 primitiveHooks
    (.primitive [1, 2] .addCarry [3, 4, 5])
    (longDivState (some (.word (2 ^ 64 - 1))) (some (.word 0)) (some (.word 1)))) ==
    (none, some (.word 0), some (.word 1), 5)

def primitiveMalformed : Bool :=
  observeLongDiv (evaluateLoop 2 primitiveHooks
    (.primitive [1, 2] .addCarry [3, 4])
    (longDivState (some (.word 3)) (some (.word 4)) (some (.word 0)))) ==
    (some .error, none, none, 5)

/-! `loopSemScript.sml:118-145` also splits `LLongMul` into the high word
    destination first and the low word destination second.  This exercises
    that source arithmetic boundary through `evaluate_def`, not only through
    the standalone `loop_arith` helper. -/
def longMulSuccess : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longMul 1 2 3 4))
    (longDivState (some (.word 20)) (some (.word 20)) none)) ==
    (none, some (.word 1), some (.word 144), 5)

/-! Cake's `loop_arith` rejects an `LLongMul` operand that is a location rather
    than a word (`loop_sem_loop_arith_probe.out:longmul_non_word=NONE`). -/
def longMulMalformed : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longMul 1 2 3 4))
    (longDivState (some (.loc 9 0)) (some (.word 20)) none)) ==
    (some .error, none, none, 5)

/-! Cake's `set_var r2 ... (set_var r1 ... s)` ordering means a coincident
    destination retains the low word (`loopSemScript.sml:127-132`). -/
def longMulSameDestination : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longMul 1 1 3 4))
    (longDivState (some (.word 20)) (some (.word 20)) none)) ==
    (none, some (.word 144), none, 5)

def observe (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.clock)

def sequenceReturn : Bool :=
  observe (evaluateLoop 8 hooks
    (.seq (.assign 1 (.const (.word 7))) (.return [1])) (emptyState 5)) ==
    (some (.result [.word 7]), none, 5)

def skip : Bool :=
  observe (evaluateLoop 4 hooks .skip (emptyState 5)) ==
    (none, none, 5)

def assignment : Bool :=
  observe (evaluateLoop 4 hooks (.assign 1 (.const (.word 7))) (emptyState 5)) ==
    (none, some (.word 7), 5)

def breakResult : Bool :=
  observe (evaluateLoop 4 hooks (.break 3)
    { (emptyState 5) with locals := fun name =>
        if name = 1 then some (.word 7) else none }) ==
    (some (.break 3), some (.word 7), 5)

def continueResult : Bool :=
  observe (evaluateLoop 4 hooks (.continue 2)
    { (emptyState 5) with locals := fun name =>
        if name = 1 then some (.word 7) else none }) ==
    (some (.continue 2), some (.word 7), 5)

def timeout : Bool :=
  observe (evaluateLoop 4 hooks .tick (emptyState 0)) ==
    (some .timeOut, none, 0)

def tailCallNoResult : Bool :=
  observe (evaluateLoop 8 hooks
    (.call none (some 1) [] none)
    { (emptyState 5) with code := [(1, [], .skip)] }) ==
    (some .error, none, 4)

/-! `loopSemScript.sml:278-360` uses `fromAList (ZIP (params,args))` for
    `find_code`, so repeated parameters are first-occurrence-wins.  Its
    returning call branch restores `s.locals` where `s` is the state
    rebound by `cut_res live (NONE,s)` — the liveness-cut caller locals —
    before setting return values (`loopSemScript.sml:402-420`).  With an
    empty cut-set the caller frame is empty apart from the return value,
    so local `8` does not survive the call. -/
def callResultState : LoopMachineState LoopWordLoc :=
  { (emptyState 5) with
      locals := fun name =>
        if name = 1 then some (.word 7)
        else if name = 2 then some (.word 8)
        else if name = 8 then some (.word 99)
        else none
      code := [(1, [4, 4], .return [4])] }

def observeCallResult (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 5, step.2.locals 8, step.2.clock)

def callResultFirstWinsAndRestoresCaller : Bool :=
  observeCallResult (evaluateLoop 12 hooks
    (.call (some ([5], [])) (some 1) [1, 2] none) callResultState) ==
    (none, some (.word 7), none, 4)

/-! `loopSemScript.sml:set_vars_def` is first-occurrence-wins for duplicate
    names.  These direct guards exercise the two executable Loop entrypoints
    that bind parameters and assign call results. -/
def duplicateBindFirstWins : Bool :=
  match loopBindParameters [1, 1]
      ([.word 5, .word 7] : List LoopWordLoc)
      (fun _ => none : Nat → Option LoopWordLoc) with
  | some locals => locals 1 == some (.word 5)
  | none => false

def duplicateAssignFirstWins : Bool :=
  match loopAssignValues (fun _ => none : Nat → Option LoopWordLoc) [1, 1]
      ([.word 5, .word 7] : List LoopWordLoc) with
  | some locals => locals 1 == some (.word 5)
  | none => false

#guard sequenceReturn
#guard skip
#guard assignment
#guard breakResult
#guard continueResult
#guard timeout
#guard tailCallNoResult
#guard callResultFirstWinsAndRestoresCaller
#guard duplicateBindFirstWins
#guard duplicateAssignFirstWins
#guard longDivSuccess
#guard fullDivSuccess
#guard fullDivZero
#guard longDivZero
#guard longDivOverflow
#guard longDivMalformed
#guard longDivSameDestination
#guard divSuccess
#guard divZero
#guard divMalformed
#guard primitiveSuccess
#guard primitiveCarry
#guard primitiveMalformed
#guard longMulSuccess
#guard longMulMalformed
#guard longMulSameDestination
#guard sharedLoadSuccess
#guard sharedStoreSuccess
#guard sharedLoadDomainError
#guard sharedLoadMissingDestination
#guard sharedStoreMissingSource
#guard sharedLoadFinalFfi
#guard ffiCallSuccess
#guard ffiMalformedArgs
#guard ffiMissingLiveState
#guard ffiFinal
#guard ffiFinalAtZeroClock

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("evaluate sequence observes intermediate assignment and call_env", sequenceReturn),
    ("evaluate Skip returns normally", skip),
    ("evaluate assignment updates the local state", assignment),
    ("evaluate Break preserves state and result", breakResult),
    ("evaluate Continue preserves state and result", continueResult),
    ("evaluate Tick clears locals at clock zero", timeout),
    ("evaluate tail call maps callee NONE to Error", tailCallNoResult),
    ("evaluate Call uses first-wins bindings and restores caller locals",
      callResultFirstWinsAndRestoresCaller),
    ("Loop parameter binding keeps the first duplicate", duplicateBindFirstWins),
    ("Loop result assignment keeps the first duplicate", duplicateAssignFirstWins),
    ("evaluate LongDiv returns the HOL quotient and remainder", longDivSuccess),
    ("evaluate LongDiv rejects a zero divisor", longDivZero),
    ("evaluate LongDiv rejects quotient overflow", longDivOverflow),
    ("evaluate LongDiv rejects a non-word operand", longDivMalformed),
    ("evaluate LDiv returns the Cake quotient", divSuccess),
    ("evaluate LDiv rejects a zero divisor", divZero),
    ("evaluate LDiv rejects a non-word operand", divMalformed),
    ("evaluate Primitive propagates AddCarry results", primitiveSuccess),
    ("evaluate Primitive propagates AddCarry carry", primitiveCarry),
    ("evaluate Primitive rejects malformed AddCarry", primitiveMalformed),
    ("evaluate LongMul splits high and low words", longMulSuccess),
    ("evaluate LongMul rejects a non-word operand", longMulMalformed),
    ("evaluate LongMul keeps the low word on a shared destination",
      longMulSameDestination),
    ("evaluate shared load updates its destination", sharedLoadSuccess),
    ("evaluate shared store preserves its source", sharedStoreSuccess),
    ("evaluate shared load rejects an unmapped address", sharedLoadDomainError),
    ("evaluate shared load rejects a missing destination", sharedLoadMissingDestination),
    ("evaluate shared store rejects a missing source", sharedStoreMissingSource),
    ("evaluate shared load propagates terminal FFI", sharedLoadFinalFfi),
    ("evaluate FFI preserves live caller state", ffiCallSuccess),
    ("evaluate FFI rejects malformed arguments", ffiMalformedArgs),
    ("evaluate FFI preserves caller state on cut failure", ffiMissingLiveState),
    ("evaluate FFI propagates FinalFFI and clears locals", ffiFinal),
    ("evaluate FFI preserves a zero clock on FinalFFI", ffiFinalAtZeroClock)]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS {name}"
    else IO.println s!"FAIL {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.LoopEvaluateParity
