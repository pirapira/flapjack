import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for Pancake `evaluate_def`

The source oracle is `scripts/hol-probes/pan_sem_e2e_probe.out`, generated
from `panSemScript.sml:556-736`.  Its `return_41`, `return_mul_42`, and
`return_if_13` observations are direct HOL evaluations of
`FST (panSem$evaluate ...)`; the call, memory, and FFI fixtures use the same
source boundary. State-owned Call and DecCall fixtures exercise nonempty code
maps, nested calls, recursive calls, return shapes, and source-clock timeout.
The direct HOL probe also records `(result, final clock)` for a simple Call,
a recursive Call that invokes DecCall, and a DecCall; the guards below check
the corresponding clocks in the state-owned evaluator.

The fixed-width memory oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_load_probe.out`, generated from
`panSemScript.sml:247-265` and the referenced `mem_load_byte_def` /
`mem_load_32_def` equations. It pins aligned success, domain failure,
little-endian reconstruction, and alignment failure.

The explicit-memory store oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_store_probe.out`, generated from
`panSemScript.sml:300-390` and `evaluate_def` at :589-608. It checks ordinary
word stores, `Store32`, and `StoreByte` through the source memory domain,
including domain/alignment failures and preservation of the other state
components.
-/

namespace Flapjack.Test.PanEvaluateParity

open Flapjack
open Flapjack.RiscV

def emptyPanState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { structs := []
    functions := []
    locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8 }

def evaluateSkip :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.skip : Prog (Word 64))

def evaluateReturn41 :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.return (.const (BitVec.ofNat 64 41)) : Prog (Word 64))

def evaluateSequence :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 1)
    ((.seq .tick (.return (.const (BitVec.ofNat 64 13)))) : Prog (Word 64))

def evaluateTickAtZero :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 0) (.tick : Prog (Word 64))

def idFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def idContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("id", .one)] [] [("id", [("x", .one)])]

def evaluateCall :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    ({ emptyPanState 10 with
        functions := idFunctions
        contracts := some idContracts }
      : PanSemEvaluateState (Word 64) Unit)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog (Word 64))

/-! The non-clocked Call evaluator receives declaration-derived returnShapes
through PanValueCallContracts. A malformed callee return must produce Error
with the callee post-state, matching the direct HOL malformed-return oracle. -/
def nonClockedBadReturnFunctions :
    List (FunName × List VarName × Prog (Word 64)) :=
  [("badret", ["x"], .return (.const (BitVec.ofNat 64 7)))]

def nonClockedBadReturnContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("badret", .comb [.one, .one])] []
    [("badret", [("x", .one)])]

def evaluateNonClockedCallBadReturnShape :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] nonClockedBadReturnFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 8
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState
    (.call none "badret" [.const (BitVec.ofNat 64 4)] : Prog (Word 64))
    (contracts := some nonClockedBadReturnContracts)

def observeNonClockedCallBadReturnShape : Bool :=
  match evaluateNonClockedCallBadReturnShape with
  | some (.error locals _ _ _, _) =>
      (locals "x").isNone
  | _ => false

private abbrev Word64 := Word 64

def emptyPanSourceState (clock : Nat)
    (code : PanSemCodeMap Word64) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := code
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def sourceIdCode : PanSemCodeMap Word64 :=
  [("id", ([ ("x", .one) ], .return (.var .local "x"), .one))]

def sourcePairCode : PanSemCodeMap Word64 :=
  [("pair", ([ ("p", .comb [.one, .one]) ], .return (.var .local "p"),
    .comb [.one, .one]))]

def sourceCallMiddlePairCode : PanSemCodeMap Word64 :=
  [("pair", ([ ("p", .comb [.one, .one]) ], .return (.var .local "p"),
    .comb [.one, .one]))]

def sourceNestedPairCode : PanSemCodeMap Word64 :=
  [("nestedPair", ([ ("p", .comb [.comb [.one], .one]) ],
    .return (.var .local "p"), .comb [.comb [.one], .one]))]

def sourceRecursiveCode : PanSemCodeMap Word64 :=
  [("f", ([], .decCall "nested" .one "g" []
      (.return (.var .local "nested")), .one)),
    ("g", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceNestedCallCode : PanSemCodeMap Word64 :=
  [("f", ([], .call none "g" [], .one)),
    ("g", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceCallSelfCode : PanSemCodeMap Word64 :=
  [("loop", ([], .call none "loop" [], .one))]

def sourceDecCallSelfCode : PanSemCodeMap Word64 :=
  [("loop", ([], .decCall "nested" .one "loop" [] .skip, .one))]

def sourceCalleeControlCode : PanSemCodeMap Word64 :=
  [("skip", ([], .skip, .one)),
    ("break", ([], .break, .one)),
    ("continue", ([], .continue, .one))]

def sourceZeroClockCallCode : PanSemCodeMap Word64 :=
  [("callee", ([], .skip, .one))]

def sourceConstReturnCallCode : PanSemCodeMap Word64 :=
  [("constant", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceBadReturnShapeCallCode : PanSemCodeMap Word64 :=
  [("badret", ([], .return (.const (BitVec.ofNat 64 7)), .comb [.one, .one]))]

def sourceBadDecCallShapeCode : PanSemCodeMap Word64 :=
  [("badret", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceRaiseExceptionCallCode : PanSemCodeMap Word64 :=
  [("raiseE", ([], .raise "E" (.const (BitVec.ofNat 64 7)), .one))]

def sourceRaisePairExceptionCallCode : PanSemCodeMap Word64 :=
  [("raisePair", ([], .raise "E"
    (.rStruct [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 8)]), .one))]

def evaluateSourceCallId :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceIdCode)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog Word64)

/-! The original code-map Call oracle's return shape comes from the entry in
`state.code`. The generic Lean evaluator also accepts optional compatibility
contracts, but those are not a HOL state field and must not override that
source return shape. -/
def sourceConflictingReturnContracts : PanValueCallContracts :=
  { returnShapes := [("id", .comb [.one, .one])]
    exceptionShapes := []
    parameterShapes := [("id", [("x", .one)])] }

def evaluateSourceCallWithConflictingReturnContract :=
  panSemEvaluateCodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8)
    (emptyPanSourceState 10 sourceIdCode)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog Word64)
    (contracts := some sourceConflictingReturnContracts)

def evaluateSourceCallStructArgument :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourcePairCode)
    (.call none "pair" [.rStruct [.const (BitVec.ofNat 64 7),
      .const (BitVec.ofNat 64 8)]] : Prog Word64)

def evaluateSourceCallFirstRecordField :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceIdCode with
        locals := fun name =>
          if name == "pair" then
            some (.rStruct [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 8)])
          else none })
    (.call none "id" [.rField 0 (.var .local "pair")] : Prog Word64)

def evaluateSourceCallMiddlePairField :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceCallMiddlePairCode with
        locals := fun name =>
          if name == "record" then
            some (.rStruct [.word (BitVec.ofNat 64 3),
              .rStruct [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 8)],
              .word (BitVec.ofNat 64 10)])
          else none })
    (.call none "pair" [.rField 1 (.var .local "record")] : Prog Word64)

def evaluateSourceCallConstructedMiddlePairField :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceCallMiddlePairCode)
    (.call none "pair"
      [.rField 1 (.rStruct [.const (BitVec.ofNat 64 3),
        .rStruct [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 8)],
        .const (BitVec.ofNat 64 10)])] : Prog Word64)

def evaluateSourceCallStructFieldRField :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceCallMiddlePairCode)
    (.call none "pair"
      [.rStruct [.rField 0 (.rStruct [.const (BitVec.ofNat 64 7),
        .const (BitVec.ofNat 64 9)]), .const (BitVec.ofNat 64 8)]] : Prog Word64)

def evaluateSourceCallNestedStructFieldRField :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceNestedPairCode)
    (.call none "nestedPair"
      [.rStruct [.rStruct [.rField 0 (.rStruct [.const (BitVec.ofNat 64 7),
        .const (BitVec.ofNat 64 9)])], .const (BitVec.ofNat 64 8)]] : Prog Word64)

def evaluateSourceCallAssigned :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceIdCode with
        locals := fun name =>
          if name == "answer" then some (.word (BitVec.ofNat 64 3)) else none })
    (.call (some (some (.local, "answer"), none)) "id"
      [.const (BitVec.ofNat 64 7)] : Prog Word64)

def evaluateSourceCallRaisesException :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceRaiseExceptionCallCode with
        exceptionShapes := fun exception =>
          if exception == "E" then some .one else none })
    (.call none "raiseE" [] : Prog Word64)

def evaluateSourceCallHandlesException :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceRaiseExceptionCallCode with
        locals := fun name =>
          if name == "caught" then some (.word (BitVec.ofNat 64 0)) else none
        exceptionShapes := fun exception =>
          if exception == "E" then some .one else none })
    (.call (some (none, some ("E", "caught",
      .return (.var .local "caught")))) "raiseE" [] : Prog Word64)

def evaluateSourceCallHandlesPairException :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceRaisePairExceptionCallCode with
        locals := fun name =>
          if name == "caught" then
            some (.rStruct [.word (BitVec.ofNat 64 0), .word (BitVec.ofNat 64 0)])
          else none
        exceptionShapes := fun exception =>
          if exception == "E" then some (.comb [.one, .one]) else none })
    (.call (some (none, some ("E", "caught",
      .return (.var .local "caught")))) "raisePair" [] : Prog Word64)

def evaluateSourceDecCallId :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceIdCode)
    (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)]
      (.return (.var .local "answer")) : Prog Word64)

def evaluateSourceDecCallWithConflictingReturnContract :=
  panSemEvaluateCodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8)
    (emptyPanSourceState 10 sourceIdCode)
    (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)]
      (.return (.var .local "answer")) : Prog Word64)
    (contracts := some sourceConflictingReturnContracts)

/-- Direct HOL row `deccall_tick_restores_existing_local`: the source code-map
DecCall returns from `id`, runs a non-Skip Tick continuation, decrements the
clock twice, and restores the caller's previous `answer` binding. -/
def evaluateSourceDecCallTick :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceIdCode with
        locals := fun name =>
          if name == "answer" then some (.word (BitVec.ofNat 64 3)) else none })
    (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)] .tick : Prog Word64)

def evaluateSourceNestedDecCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceRecursiveCode)
    (.decCall "answer" .one "f" []
      (.return (.var .local "answer")) : Prog Word64)

def evaluateSourceNestedCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceRecursiveCode)
    (.call none "f" [] : Prog Word64)

def evaluateSourceNestedOrdinaryCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceNestedCallCode)
    (.call none "f" [] : Prog Word64)

def evaluateSourceNestedCallWithPostState :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8)
    (emptyPanSourceState 10 sourceRecursiveCode)
    (.call none "f" [] : Prog Word64)

def evaluateSourceRecursiveCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 2 sourceCallSelfCode)
    (.call none "loop" [] : Prog Word64)

def evaluateSourceRecursiveDecCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 2 sourceDecCallSelfCode)
    (.decCall "answer" .one "loop" [] .skip : Prog Word64)

def sourceCalleeControlState : PanSemState Word64 (FfiState Unit) :=
  { emptyPanSourceState 10 sourceCalleeControlCode with
      locals := updatePanValueMap (fun _ => none) "keep"
        (.word (BitVec.ofNat 64 42)) }

def evaluateSourceCallCalleeSkip :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.call none "skip" [] : Prog Word64)

def evaluateSourceCallCalleeBreak :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.call none "break" [] : Prog Word64)

def evaluateSourceCallCalleeContinue :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.call none "continue" [] : Prog Word64)

def evaluateSourceDecCallCalleeSkip :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.decCall "answer" .one "skip" [] .skip : Prog Word64)

def evaluateSourceDecCallCalleeBreak :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.decCall "answer" .one "break" [] .skip : Prog Word64)

def evaluateSourceDecCallCalleeContinue :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceCalleeControlState
    (.decCall "answer" .one "continue" [] .skip : Prog Word64)

def evaluateSourceZeroClockCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 0 sourceZeroClockCallCode with
        locals := fun name =>
          if name == "x" then some (.word (BitVec.ofNat 64 9)) else none })
    (.call none "callee" [] : Prog Word64)

def evaluateSourceConstReturnCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceConstReturnCallCode)
    (.call none "constant" [] : Prog Word64)

def sourceBadReturnShapeState :=
  { emptyPanSourceState 10 sourceBadReturnShapeCallCode with
      locals := updatePanValueMap (fun _ => none) "caller" (.word (BitVec.ofNat 64 3)) }

def evaluateSourceCallBadReturnShape :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceBadReturnShapeState
    (.call none "badret" [] : Prog Word64)

def evaluateSourceDecCallBadReturnShape :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8)
    ({ emptyPanSourceState 10 sourceBadDecCallShapeCode with
        locals := updatePanValueMap (fun _ => none) "keep"
          (.word (BitVec.ofNat 64 42)) })
    (.decCall "answer" (.comb []) "badret" [] .skip : Prog Word64)

/-! The original HOL probe rows `recursive_call_missing_function`,
    `recursive_deccall_missing_function`, `recursive_call_bad_argument`, and
    `recursive_deccall_bad_argument` all observe `(Error, clock, x)`. These
    assertions pin the untouched source state as well as the result, so the
    Call/DecCall lookup and argument-failure branches cannot pass vacuously. -/
def sourceMissingCallState : PanSemState Word64 (FfiState Unit) :=
  { emptyPanSourceState 5 [] with
      locals := updatePanValueMap (fun _ => none) "x" (.word (BitVec.ofNat 64 7)) }

def evaluateSourceCallMissingFunction :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceMissingCallState
    (.call none "missing" [] : Prog Word64)

def evaluateSourceDecCallMissingFunction :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceMissingCallState
    (.decCall "answer" .one "missing" [] .skip : Prog Word64)

def sourceBadCallArgumentCode : PanSemCodeMap Word64 :=
  [("id", ([], .skip, .one))]

def sourceBadCallArgumentState : PanSemState Word64 (FfiState Unit) :=
  { emptyPanSourceState 10 sourceBadCallArgumentCode with
      locals := updatePanValueMap (fun _ => none) "x" (.word (BitVec.ofNat 64 7)) }

def evaluateSourceCallBadArgument :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceBadCallArgumentState
    (.call none "id" [.var .local "absent"] : Prog Word64)

def evaluateSourceDecCallBadArgument :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler sourceBadCallArgumentState
    (.decCall "answer" .one "id" [.var .local "absent"] .skip : Prog Word64)

def sourceBadCallDestinationState : PanSemState Word64 (FfiState Unit) :=
  { emptyPanSourceState 10 sourceIdCode with
      locals := updatePanValueMap (fun _ => none) "answer"
        (.rStruct [.word (BitVec.ofNat 64 0), .word (BitVec.ofNat 64 0)]) }

def evaluateSourceCallBadDestination :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) sourceBadCallDestinationState
    (.call (some (some (.local, "answer"), none)) "id"
      [.const (BitVec.ofNat 64 7)] : Prog Word64)

private def isSourceReturnedWord
    (result : Option (PanValueFfiClockResult Word64 Unit))
    (expected : Word64) (expectedClock : Nat) : Bool :=
  match result with
  | some (.control (.returned _ _ _ _ [(.word value)]), clock) =>
      value == expected && clock == expectedClock
  | _ => false

private def isSourceTimeoutAt
    (result : Option (PanValueFfiClockResult Word64 Unit))
    (expectedClock : Nat) : Bool :=
  match result with
  | some (.timeout _ _ _ _, clock) => clock == expectedClock
  | _ => false

def observeSourceCodeCall := isSourceReturnedWord evaluateSourceCallId
  (BitVec.ofNat 64 7) 9

def observeSourceCallUsesCodeReturnShape := isSourceReturnedWord
  evaluateSourceCallWithConflictingReturnContract (BitVec.ofNat 64 7) 9

def observeSourceCallStructArgument : Bool :=
  match evaluateSourceCallStructArgument with
  | some (.control (.returned _ _ _ _ [.rStruct [.word left, .word right]]), 9) =>
      left == BitVec.ofNat 64 7 && right == BitVec.ofNat 64 8
  | _ => false

def observeSourceCallFirstRecordField := isSourceReturnedWord
  evaluateSourceCallFirstRecordField (BitVec.ofNat 64 7) 9

def observeSourceCallMiddlePairField : Bool :=
  match evaluateSourceCallMiddlePairField with
  | some (.control (.returned _ _ _ _ [.rStruct [.word first, .word second]]), 9) =>
      first == BitVec.ofNat 64 7 && second == BitVec.ofNat 64 8
  | _ => false

def observeSourceCallConstructedMiddlePairField : Bool :=
  match evaluateSourceCallConstructedMiddlePairField with
  | some (.control (.returned _ _ _ _ [.rStruct [.word first, .word second]]), 9) =>
      first == BitVec.ofNat 64 7 && second == BitVec.ofNat 64 8
  | _ => false

def observeSourceCallStructFieldRField : Bool :=
  match evaluateSourceCallStructFieldRField with
  | some (.control (.returned _ _ _ _ [.rStruct [.word first, .word second]]), 9) =>
      first == BitVec.ofNat 64 7 && second == BitVec.ofNat 64 8
  | _ => false

def observeSourceCallNestedStructFieldRField : Bool :=
  match evaluateSourceCallNestedStructFieldRField with
  | some (.control (.returned _ _ _ _
      [.rStruct [.rStruct [.word first], .word second]]), 9) =>
      first == BitVec.ofNat 64 7 && second == BitVec.ofNat 64 8
  | _ => false

def observeSourceCallAssigned : Bool :=
  match evaluateSourceCallAssigned with
  | some (.control (.normal locals _globals _memory _ffi), 9) =>
      match locals "answer" with
      | some (.word value) => value == BitVec.ofNat 64 7
      | _ => false
  | _ => false

def observeSourceCallBadDestination : Bool :=
  match evaluateSourceCallBadDestination with
  | some ((.control (.error locals _ _ _), clock), postState) =>
      clock == 9 && (locals "answer").isNone && postState.clock == 9 &&
        (postState.locals "answer").isNone
  | _ => false

def observeSourceCallRaisesException : Bool :=
  match evaluateSourceCallRaisesException with
  | some (.control (.raised _ _ _ _ "E" (.word value)), 9) =>
      value == BitVec.ofNat 64 7
  | _ => false

def observeSourceCallHandlesException : Bool :=
  isSourceReturnedWord evaluateSourceCallHandlesException
    (BitVec.ofNat 64 7) 9

def observeSourceCallHandlesPairException : Bool :=
  match evaluateSourceCallHandlesPairException with
  | some (.control (.returned _ _ _ _
      [.rStruct [.word first, .word second]]), 9) =>
      first == BitVec.ofNat 64 7 && second == BitVec.ofNat 64 8
  | _ => false

def observeSourceCodeDecCall := isSourceReturnedWord evaluateSourceDecCallId
  (BitVec.ofNat 64 7) 9

def observeSourceDecCallUsesCodeReturnShape := isSourceReturnedWord
  evaluateSourceDecCallWithConflictingReturnContract (BitVec.ofNat 64 7) 9

def observeSourceDecCallTick : Bool :=
  match evaluateSourceDecCallTick with
  | some (.control (.normal locals _ _ _), 8) =>
      match locals "answer" with
      | some (.word value) => value == BitVec.ofNat 64 3
      | _ => false
  | _ => false

def observeSourceNestedDecCall := isSourceReturnedWord evaluateSourceNestedDecCall
  (BitVec.ofNat 64 7) 8

def observeSourceNestedCodeCall := isSourceReturnedWord evaluateSourceNestedCall
  (BitVec.ofNat 64 7) 8

def observeSourceNestedOrdinaryCall := isSourceReturnedWord
  evaluateSourceNestedOrdinaryCall (BitVec.ofNat 64 7) 8

def observeSourceCodePreservedAfterRecursion : Bool :=
  match evaluateSourceNestedCallWithPostState with
  | some (_, postState) =>
      match panSemCodeLookup postState.code "f", panSemCodeLookup postState.code "g" with
      | some (_, .decCall "nested" .one "g" [] _, .one),
          some ([], .return (.const value), .one) =>
          value == BitVec.ofNat 64 7
      | _, _ => false
  | none => false

/-- The generic state-owned code invariant applies to the original HOL-backed
    nested Call/DecCall case, independently of its returned result. -/
theorem sourceNestedCallPreservesCode
    (result : PanValueFfiClockResult Word64 Unit)
    (postState : PanSemState Word64 (FfiState Unit))
    (heval : evaluateSourceNestedCallWithPostState = some (result, postState)) :
    postState.code = (emptyPanSourceState 10 sourceRecursiveCode).code := by
  exact panSemEvaluateCodeStateWithPostState_preserves_code
    statefulTestContext statefulTestPrimitive statefulTestHandler
    (BitVec.ofNat 64 8) (emptyPanSourceState 10 sourceRecursiveCode)
    (.call none "f" []) result postState heval

def observeSourceRecursiveCallTimeout :=
  isSourceTimeoutAt evaluateSourceRecursiveCallTimeout 0

def observeSourceRecursiveDecCallTimeout :=
  isSourceTimeoutAt evaluateSourceRecursiveDecCallTimeout 0

/-! Direct original-HOL rows `recursive_call_callee_{skip,break,continue}` and
`recursive_deccall_callee_{skip,break,continue}` evaluate the state-owned code
entries and expect `(SOME Error, 9, NONE)`. -/
private def isSourceCalleeControlErrorAtNine
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control (.error locals _ _ _), 9) => (locals "keep").isNone
  | _ => false

def observeSourceCallCalleeControlErrors : Bool :=
  isSourceCalleeControlErrorAtNine evaluateSourceCallCalleeSkip &&
    isSourceCalleeControlErrorAtNine evaluateSourceCallCalleeBreak &&
    isSourceCalleeControlErrorAtNine evaluateSourceCallCalleeContinue

def observeSourceDecCallCalleeControlErrors : Bool :=
  isSourceCalleeControlErrorAtNine evaluateSourceDecCallCalleeSkip &&
    isSourceCalleeControlErrorAtNine evaluateSourceDecCallCalleeBreak &&
    isSourceCalleeControlErrorAtNine evaluateSourceDecCallCalleeContinue

def observeSourceZeroClockCallTimeout : Bool :=
  match evaluateSourceZeroClockCallTimeout with
  | some (.timeout locals _ _ _, 0) =>
      match locals "x" with
      | none => true
      | some _ => false
  | _ => false

def observeSourceConstReturnCall := isSourceReturnedWord
  evaluateSourceConstReturnCall (BitVec.ofNat 64 7) 9

def observeSourceCallBadReturnShape : Bool :=
  match evaluateSourceCallBadReturnShape with
  | some (.control (.error locals _ _ _), clock) =>
      match locals "caller" with
      | none => clock == 9
      | some _ => false
  | _ => false

/-- Full post-state guard for `recursive_deccall_bad_declared_shape` in the
    direct `pan_sem_e2e_probe.out` HOL oracle. -/
def observeSourceDecCallBadReturnShape : Bool :=
  match evaluateSourceDecCallBadReturnShape with
  | some ((.control (.error resultLocals resultGlobals resultMemory resultFfi), clock),
      postState) =>
      let zero := BitVec.ofNat 64 0
      let emptyStructs := match postState.structs with | [] => true | _ => false
      let unchangedCode := match postState.code with
        | [("badret", ([], .return (.const value), .one))] =>
            value == BitVec.ofNat 64 7
        | _ => false
      clock == 9 && postState.clock == 9 &&
        (resultLocals "keep").isNone && (postState.locals "keep").isNone &&
        (resultGlobals "global").isNone && (postState.globals "global").isNone &&
        (resultMemory zero).isNone && (postState.memory zero).isNone &&
        resultFfi.state == () && resultFfi.ioEvents.isEmpty &&
        postState.ffi.state == () && postState.ffi.ioEvents.isEmpty &&
        emptyStructs && unchangedCode &&
        (postState.exceptionShapes "E").isNone &&
        !(postState.memaddrs zero) && !(postState.sharedMemaddrs zero) &&
        !postState.be && postState.baseAddress == BitVec.ofNat 64 0 &&
        postState.topAddress == BitVec.ofNat 64 100
  | _ => false

def isSourceErrorPreservingX
    (result : Option (PanValueFfiClockResult Word64 Unit))
    (expectedClock : Nat) : Bool :=
  match result with
  | some (.control (.error locals _ _ _), clock) =>
      clock == expectedClock &&
        match locals "x" with
        | some (.word value) => value == BitVec.ofNat 64 7
        | _ => false
  | _ => false

def observeSourceCallMissingFunction :=
  isSourceErrorPreservingX evaluateSourceCallMissingFunction 5

def observeSourceDecCallMissingFunction :=
  isSourceErrorPreservingX evaluateSourceDecCallMissingFunction 5

def observeSourceCallBadArgument :=
  isSourceErrorPreservingX evaluateSourceCallBadArgument 10

def observeSourceDecCallBadArgument :=
  isSourceErrorPreservingX evaluateSourceDecCallBadArgument 10

#guard observeSourceCodeCall
#guard observeSourceCallUsesCodeReturnShape
#guard observeSourceCallStructArgument
#guard observeSourceCallFirstRecordField
#guard observeSourceCallAssigned
#guard observeSourceCallBadDestination
#guard observeSourceCallRaisesException
#guard observeSourceCallHandlesException
#guard observeSourceCallHandlesPairException
#guard observeSourceCallStructFieldRField
#guard observeSourceCallNestedStructFieldRField
#guard observeSourceCodeDecCall
#guard observeSourceDecCallUsesCodeReturnShape
#guard observeSourceDecCallTick
#guard observeSourceNestedCodeCall
#guard observeSourceNestedOrdinaryCall
#guard observeSourceCodePreservedAfterRecursion
#guard observeSourceRecursiveCallTimeout
#guard observeSourceRecursiveDecCallTimeout
#guard observeSourceCallCalleeControlErrors
#guard observeSourceDecCallCalleeControlErrors
#guard observeSourceZeroClockCallTimeout
#guard observeSourceConstReturnCall
#guard observeSourceCallBadReturnShape
#guard observeSourceDecCallBadReturnShape
#guard observeSourceCallMissingFunction
#guard observeSourceDecCallMissingFunction
#guard observeSourceCallBadArgument
#guard observeSourceDecCallBadArgument

/-! The fixed-width branches must go through the explicit source memory model.
    This is the stateful evaluator path corresponding to
    `panSemScript.sml:247-265`, not the legacy whole-cell fallback. -/
def fixedLoadDomain : PanMemoryDomain (Word 64) :=
  fun address => address == BitVec.ofNat 64 8

def fixedLoadMemory : Word 64 → Option (PanValue (Word 64)) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x0807060504030201))
    else none

def fixedLoadAccess : PanValueMemoryAccess (Word 64) :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel fixedLoadDomain

def evaluateExactProgramWord32 :=
  evalPanValueProgExact [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none) fixedLoadMemory fixedLoadAccess
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

def evaluateExactProgramByteDomainFailure :=
  evalPanValueProgExact [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none) fixedLoadMemory fixedLoadAccess
    (.return (.loadByte (.const (BitVec.ofNat 64 16))) : Prog (Word 64))

def fixedLoadState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { emptyPanState clock with
      memory := fixedLoadMemory
      memoryAccess := some fixedLoadAccess }

def fixedLoadStateWithoutAccess (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { fixedLoadState clock with memoryAccess := none }

def fixedExactState : PanSemExactState (Word 64) Unit :=
  { legacy := fixedLoadStateWithoutAccess 4
    memoryAccess := fixedLoadAccess }

def nestedRaiseExpression : Exp (Word 64) :=
  .rStruct [.const (BitVec.ofNat 64 3),
    .rStruct [.const (BitVec.ofNat 64 4), .const (BitVec.ofNat 64 5)]]

def evaluateNestedRaise :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler fixedExactState
    (.raise "E" nestedRaiseExpression : Prog (Word 64))

def fixedStoreLocals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "kept" then some (.word (BitVec.ofNat 64 55)) else none

def fixedStoreGlobals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "keptGlobal" then some (.word (BitVec.ofNat 64 66)) else none

def fixedStoreState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { fixedLoadState clock with
      locals := fixedStoreLocals
      globals := fixedStoreGlobals }

def evaluateFixedByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 9))) : Prog (Word 64))

def evaluateFixedWord32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

example :
    panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
        fixedLoadAccess (fixedLoadStateWithoutAccess 4)
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) =
      panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
        { fixedLoadStateWithoutAccess 4 with memoryAccess := some fixedLoadAccess }
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) := by
  exact panSemEvaluateExact_uses_memory_access
    statefulTestContext statefulTestPrimitive statefulTestHandler fixedLoadAccess
    (fixedLoadStateWithoutAccess 4)
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive
        statefulTestHandler fixedExactState
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) =
      panSemEvaluateExact statefulTestContext statefulTestPrimitive
        statefulTestHandler fixedLoadAccess (fixedLoadStateWithoutAccess 4)
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) := by
  rfl

def evaluateFixedByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 16))) : Prog (Word 64))

def evaluateFixedStore :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStoreDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStore32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStore32Unaligned :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStoreByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def evaluateFixedStoreByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def emptySharedContext : PanValueFfiContext (Word 64) :=
  { statefulTestContext with sharedDomain := fun _ => false }

def evaluateIfBadCondition :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.ite (.var .local "missing") .skip .skip : Prog (Word 64))

def evaluateIfOk :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.ite (.const (BitVec.ofNat 64 1)) .skip .skip : Prog (Word 64))

def evaluateShMemLoadUnbound :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemLoad .op8 .local "missing" (.const (BitVec.ofNat 64 8)) : Prog (Word 64))

def evaluateShMemLoadDomainFailure :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemLoad .op8 .local "kept" (.const (BitVec.ofNat 64 8)) : Prog (Word 64))

def evaluateShMemStoreDomainFailure :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemStore .op8 (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 7)) : Prog (Word 64))

def isWord (expected : Nat) : PanValue (Word 64) → Bool
  | .word value => value == BitVec.ofNat 64 expected
  | _ => false

def observeSkip : Bool :=
  match evaluateSkip with
  | some (.control (.normal locals _ _ _), 4) => locals "x" = none
  | _ => false

def observeReturn41 : Bool :=
  match evaluateReturn41 with
  | some (.control (.returned locals _ _ _ [value]), 4) =>
      locals "x" = none && isWord 41 value
  | _ => false

def observeSequence : Bool :=
  match evaluateSequence with
  | some (.control (.returned _ _ _ _ [value]), 0) => isWord 13 value
  | _ => false

def observeTickAtZero : Bool :=
  match evaluateTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

def observeCall : Bool :=
  match evaluateCall with
  | some (.control (.returned locals _ _ _ [value]), 9) =>
      locals "x" = none && isWord 7 value
  | _ => false

def observeNestedRaise : Bool :=
  match evaluateNestedRaise with
  | some (.control (.raised locals _ _ _ "E"
      (.rStruct [.word first, .rStruct [.word second, .word third]])), 4) =>
      locals "x" = none &&
        first == BitVec.ofNat 64 3 &&
        second == BitVec.ofNat 64 4 &&
        third == BitVec.ofNat 64 5
  | _ => false

def isErrorResult {α σ : Type} : Option (PanValueFfiClockResult α σ) → Bool
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

def observeFixedLoads : Bool :=
  match evaluateFixedByte, evaluateFixedWord32 with
  | some (.control (.returned _ _ _ _ [(.word byte)]), 4),
      some (.control (.returned _ _ _ _ [(.word word32)]), 4) =>
      byte == BitVec.ofNat 64 2 && word32 == BitVec.ofNat 64 0x04030201
  | _, _ => false

def observeFixedLoadDomainFailure : Bool :=
  isErrorResult evaluateFixedByteDomainFailure

def observeExactProgramMemoryAccess : Bool :=
  match evaluateExactProgramWord32 with
  | some (_, _, _, [(.word value)]) =>
      value == BitVec.ofNat 64 0x04030201
  | _ => false

def observeExactProgramDomainFailure : Bool :=
  evaluateExactProgramByteDomainFailure.isNone

def isWordOption (expected : Nat) : Option (PanValue (Word 64)) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

def isNoneOption : Option (PanValue (Word 64)) → Bool
  | none => true
  | _ => false

def observeFixedStore : Bool :=
  match evaluateFixedStore with
  | some (.control (.normal locals globals memory ffi), 4) =>
      isWordOption 55 (locals "kept") &&
      isWordOption 66 (globals "keptGlobal") &&
      isWordOption 0x1122334455667788 (memory (BitVec.ofNat 64 8)) &&
      isNoneOption (memory (BitVec.ofNat 64 16)) &&
      decide (ffi.ioEvents = statefulTestFfiState.ioEvents)
  | _ => false

def observeFixedStore32 : Bool :=
  match evaluateFixedStore32 with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x0807060511223344 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreByte : Bool :=
  match evaluateFixedStoreByte with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x080706050403aa01 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreFailures : Bool :=
  isErrorResult evaluateFixedStoreDomainFailure &&
    isErrorResult evaluateFixedStore32Unaligned &&
    isErrorResult evaluateFixedStoreByteDomainFailure

def errorPreservingKeptAt (clock localValue : Nat) :
    Option (PanValueFfiClockResult (Word 64) Unit) → Bool
  | some (.control (.error locals _ _ _), n) =>
      n == clock && isWordOption localValue (locals "kept")
  | _ => false

def observeIfBadCondition : Bool :=
  errorPreservingKeptAt 5 55 evaluateIfBadCondition

def observeIfOk : Bool :=
  match evaluateIfOk with
  | some (.control (.normal locals _ _ _), 5) => isWordOption 55 (locals "kept")
  | _ => false

def observeShMemLoadUnbound : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemLoadUnbound

def observeShMemLoadDomainFailure : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemLoadDomainFailure

def observeShMemStoreDomainFailure : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemStoreDomainFailure

#guard observeSkip
#guard observeReturn41
#guard observeSequence
#guard observeTickAtZero
#guard observeCall
#guard observeNestedRaise
#guard observeFixedLoads
#guard observeFixedLoadDomainFailure
#guard observeExactProgramMemoryAccess
#guard observeExactProgramDomainFailure
#guard observeFixedStore
#guard observeFixedStore32
#guard observeFixedStoreByte
#guard observeFixedStoreFailures
#guard observeIfBadCondition
#guard observeIfOk
#guard observeShMemLoadUnbound
#guard observeShMemLoadDomainFailure
#guard observeShMemStoreDomainFailure
#guard observeNonClockedCallBadReturnShape

def runChecks : IO Bool := do
  if observeSkip then IO.println "PASS evaluate skip" else IO.println "FAIL evaluate skip"
  if observeReturn41 then IO.println "PASS evaluate return_41" else IO.println "FAIL evaluate return_41"
  if observeSequence then IO.println "PASS evaluate sequence" else IO.println "FAIL evaluate sequence"
  if observeTickAtZero then IO.println "PASS evaluate timeout" else IO.println "FAIL evaluate timeout"
  if observeCall then IO.println "PASS evaluate call_id_7" else IO.println "FAIL evaluate call_id_7"
  if observeSourceCodeCall then IO.println "PASS state-owned code Call matches HOL call_code_map_7" else
    IO.println "FAIL state-owned code Call matches HOL call_code_map_7"
  if observeSourceCallUsesCodeReturnShape then
    IO.println "PASS source Call return validation follows the state code entry"
  else IO.println "FAIL source Call return validation follows the state code entry"
  if observeSourceCallStructArgument then
    IO.println "PASS state-owned Call binds and returns a structured argument like HOL"
  else IO.println "FAIL state-owned Call binds and returns a structured argument like HOL"
  if observeSourceCallFirstRecordField then
    IO.println "PASS state-owned Call evaluates first field of a local record like HOL"
  else IO.println "FAIL state-owned Call evaluates first field of a local record like HOL"
  if observeSourceCallAssigned then IO.println "PASS state-owned Call writes the existing local destination" else
    IO.println "FAIL state-owned Call writes the existing local destination"
  if observeSourceCallBadDestination then
    IO.println "PASS state-owned Call maps rejected destination assignment to HOL Error"
  else IO.println "FAIL state-owned Call maps rejected destination assignment to HOL Error"
  if observeSourceCallRaisesException then IO.println "PASS state-owned Call propagates the callee exception payload" else
    IO.println "FAIL state-owned Call propagates the callee exception payload"
  if observeSourceCallHandlesException then IO.println "PASS state-owned Call handler catches and binds the exception payload" else
    IO.println "FAIL state-owned Call handler catches and binds the exception payload"
  if observeSourceCallHandlesPairException then
    IO.println "PASS state-owned Call handler returns a two-word exception payload like HOL"
  else IO.println "FAIL state-owned Call handler returns a two-word exception payload like HOL"
  if observeSourceCallMiddlePairField then
    IO.println "PASS state-owned Call evaluates a middle RField pair like original HOL"
  else IO.println "FAIL state-owned Call evaluates a middle RField pair like original HOL"
  if observeSourceCallConstructedMiddlePairField then
    IO.println "PASS state-owned Call selects a nested pair from a constructed RStruct like original HOL"
  else IO.println "FAIL state-owned Call selects a nested pair from a constructed RStruct like original HOL"
  if observeSourceCallStructFieldRField then
    IO.println "PASS state-owned Call constructs a record with an RField field like original HOL"
  else IO.println "FAIL state-owned Call constructs a record with an RField field like original HOL"
  if observeSourceCallNestedStructFieldRField then
    IO.println "PASS state-owned Call recursively compiles nested records with an RField field like original HOL"
  else IO.println "FAIL state-owned Call recursively compiles nested records with an RField field like original HOL"
  if observeSourceCodeDecCall then IO.println "PASS state-owned code DecCall matches HOL deccall_code_map_7" else
    IO.println "FAIL state-owned code DecCall matches HOL deccall_code_map_7"
  if observeSourceDecCallUsesCodeReturnShape then
    IO.println "PASS source DecCall return validation follows the state code entry"
  else IO.println "FAIL source DecCall return validation follows the state code entry"
  if observeSourceDecCallTick then
    IO.println "PASS state-owned DecCall Tick continuation matches direct HOL clock/local row"
  else IO.println "FAIL state-owned DecCall Tick continuation matches direct HOL clock/local row"
  if observeSourceNestedDecCall then IO.println "PASS nested state-owned DecCall returns 7 and decrements the HOL clock twice" else
    IO.println "FAIL nested state-owned DecCall returns 7 and decrements the HOL clock twice"
  if observeSourceNestedCodeCall then IO.println "PASS state-owned nested Call and DecCall match HOL recursive oracle" else
    IO.println "FAIL state-owned nested Call and DecCall match HOL recursive oracle"
  if observeSourceNestedOrdinaryCall then IO.println "PASS state-owned ordinary Call recursively resolves nested code entry" else
    IO.println "FAIL state-owned ordinary Call recursively resolves nested code entry"
  if observeSourceCodePreservedAfterRecursion then IO.println "PASS recursive code-map evaluation preserves source code" else
    IO.println "FAIL recursive code-map evaluation preserves source code"
  if observeSourceRecursiveCallTimeout then IO.println "PASS recursive state-owned Call times out at source clock zero" else
    IO.println "FAIL recursive state-owned Call times out at source clock zero"
  if observeSourceRecursiveDecCallTimeout then IO.println "PASS recursive state-owned DecCall times out at source clock zero" else
    IO.println "FAIL recursive state-owned DecCall times out at source clock zero"
  if observeSourceCallCalleeControlErrors then
    IO.println "PASS state-owned Call Skip/Break/Continue callee rows match direct HOL Error states"
  else IO.println "FAIL state-owned Call Skip/Break/Continue callee rows match direct HOL Error states"
  if observeSourceDecCallCalleeControlErrors then
    IO.println "PASS state-owned DecCall Skip/Break/Continue callee rows match direct HOL Error states"
  else IO.println "FAIL state-owned DecCall Skip/Break/Continue callee rows match direct HOL Error states"
  if observeSourceZeroClockCallTimeout then IO.println "PASS state-owned Call with a nonempty code map times out at zero clock and clears locals" else
    IO.println "FAIL state-owned Call with a nonempty code map times out at zero clock and clears locals"
  if observeSourceConstReturnCall then IO.println "PASS zero-argument state-owned Call returns its code-map word constant" else
    IO.println "FAIL zero-argument state-owned Call returns its code-map word constant"
  if observeSourceCallBadReturnShape then
    IO.println "PASS state-owned Call returns HOL Error and callee state on return-shape mismatch"
  else IO.println "FAIL state-owned Call returns HOL Error and callee state on return-shape mismatch"
  if observeSourceDecCallBadReturnShape then
    IO.println "PASS state-owned DecCall returns HOL Error and callee state on return-shape mismatch"
  else IO.println "FAIL state-owned DecCall returns HOL Error and callee state on return-shape mismatch"
  if observeSourceCallMissingFunction then
    IO.println "PASS state-owned Call missing-function branch preserves the HOL source state"
  else IO.println "FAIL state-owned Call missing-function branch preserves the HOL source state"
  if observeSourceDecCallMissingFunction then
    IO.println "PASS state-owned DecCall missing-function branch preserves the HOL source state"
  else IO.println "FAIL state-owned DecCall missing-function branch preserves the HOL source state"
  if observeSourceCallBadArgument then
    IO.println "PASS state-owned Call argument-evaluation failure matches the HOL source state"
  else IO.println "FAIL state-owned Call argument-evaluation failure matches the HOL source state"
  if observeSourceDecCallBadArgument then
    IO.println "PASS state-owned DecCall argument-evaluation failure matches the HOL source state"
  else IO.println "FAIL state-owned DecCall argument-evaluation failure matches the HOL source state"
  if observeNonClockedCallBadReturnShape then
    IO.println "PASS non-clocked Call returns Error with callee post-state on return-shape mismatch"
  else IO.println "FAIL non-clocked Call returns Error with callee post-state on return-shape mismatch"
  if observeNestedRaise then IO.println "PASS evaluate nested structured raise" else
    IO.println "FAIL evaluate nested structured raise"
  if observeFixedLoads then IO.println "PASS evaluate fixed-width loads" else
    IO.println "FAIL evaluate fixed-width loads"
  if observeFixedLoadDomainFailure then IO.println "PASS evaluate fixed-width domain failure" else
    IO.println "FAIL evaluate fixed-width domain failure"
  if observeExactProgramMemoryAccess then IO.println "PASS exact structured program memory access" else
    IO.println "FAIL exact structured program memory access"
  if observeExactProgramDomainFailure then IO.println "PASS exact structured program domain failure" else
    IO.println "FAIL exact structured program domain failure"
  if observeFixedStore then IO.println "PASS evaluate explicit word store" else
    IO.println "FAIL evaluate explicit word store"
  if observeFixedStore32 then IO.println "PASS evaluate explicit Store32" else
    IO.println "FAIL evaluate explicit Store32"
  if observeFixedStoreByte then IO.println "PASS evaluate explicit StoreByte" else
    IO.println "FAIL evaluate explicit StoreByte"
  if observeFixedStoreFailures then IO.println "PASS evaluate explicit store failures" else
    IO.println "FAIL evaluate explicit store failures"
  if observeIfBadCondition then IO.println "PASS evaluate If rejects non-word condition with Error" else
    IO.println "FAIL evaluate If rejects non-word condition with Error"
  if observeIfOk then IO.println "PASS evaluate If word condition keeps clock" else
    IO.println "FAIL evaluate If word condition keeps clock"
  if observeShMemLoadUnbound then IO.println "PASS evaluate ShMemLoad rejects unbound local with Error" else
    IO.println "FAIL evaluate ShMemLoad rejects unbound local with Error"
  if observeShMemLoadDomainFailure then IO.println "PASS evaluate ShMemLoad rejects shared-domain miss with Error" else
    IO.println "FAIL evaluate ShMemLoad rejects shared-domain miss with Error"
  if observeShMemStoreDomainFailure then IO.println "PASS evaluate ShMemStore rejects shared-domain miss with Error" else
    IO.println "FAIL evaluate ShMemStore rejects shared-domain miss with Error"
  pure (observeSkip && observeReturn41 && observeSequence && observeTickAtZero && observeCall &&
    observeSourceCodeCall && observeSourceCallUsesCodeReturnShape &&
    observeSourceCallStructArgument && observeSourceCallFirstRecordField &&
    observeSourceCallMiddlePairField &&
    observeSourceCallConstructedMiddlePairField &&
    observeSourceCodeDecCall && observeSourceDecCallUsesCodeReturnShape &&
    observeSourceNestedDecCall &&
    observeSourceNestedCodeCall &&
    observeSourceNestedOrdinaryCall &&
    observeSourceCodePreservedAfterRecursion &&
    observeSourceRecursiveCallTimeout && observeSourceRecursiveDecCallTimeout &&
    observeSourceCallCalleeControlErrors && observeSourceDecCallCalleeControlErrors &&
    observeSourceZeroClockCallTimeout && observeSourceConstReturnCall &&
    observeSourceCallBadDestination && observeSourceCallBadReturnShape &&
    observeSourceDecCallBadReturnShape && observeSourceCallMissingFunction &&
    observeSourceDecCallMissingFunction && observeSourceCallBadArgument &&
    observeSourceDecCallBadArgument &&
    observeNestedRaise &&
    observeFixedLoads && observeFixedLoadDomainFailure &&
    observeExactProgramMemoryAccess && observeExactProgramDomainFailure &&
    observeFixedStore &&
    observeFixedStore32 && observeFixedStoreByte && observeFixedStoreFailures &&
    observeIfBadCondition && observeIfOk && observeShMemLoadUnbound &&
    observeShMemLoadDomainFailure && observeShMemStoreDomainFailure)

end Flapjack.Test.PanEvaluateParity
