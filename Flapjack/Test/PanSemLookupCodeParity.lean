import Flapjack.Pancake.Semantics.PanSem.LookupCode

/-!
# Parity for Pancake `lookup_code_def`

The direct HOL observations live in `scripts/hol-probes/pan_sem_lookup_code_probe.out`.
The Lean fixtures call the tagged lookup through the source state's finite
`code` map, covering success and the four rejection boundaries from that
oracle.
-/

namespace Flapjack.Test.PanSemLookupCodeParity

open Flapjack

private abbrev Word64 := BitVec 64

def lookupState (code : PanSemCodeMap Word64) : PanSemState Word64 Unit where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := code
  exceptionShapes := fun _ => none
  memory := fun _ => none
  memaddrs := fun _ => false
  sharedMemaddrs := fun _ => false
  clock := 20
  be := false
  ffi := ()
  baseAddress := 0
  topAddress := 0

def singleParameterCode : PanSemCodeMap Word64 :=
  [("id", ([("x", Shape.one)], .skip, Shape.one))]

def observesSuccessfulLookup : Bool :=
  match panSemLookupStateCodeHOL (lookupState singleParameterCode) "id"
      [.word (7 : Word64)] with
  | some (.skip, locals, .one) =>
      match locals "x" with
      | some (.val (.word value)) => value == 7
      | _ => false
  | _ => false

def observesMissingFunction : Bool :=
  match panSemLookupStateCodeHOL (lookupState singleParameterCode) "missing" [] with
  | none => true
  | some _ => false

def observesWrongArity : Bool :=
  match panSemLookupStateCodeHOL (lookupState singleParameterCode) "id" [] with
  | none => true
  | some _ => false

def observesWrongShape : Bool :=
  match panSemLookupStateCodeHOL (lookupState singleParameterCode) "id" [.rStruct []] with
  | none => true
  | some _ => false

def duplicateFormalCode : PanSemCodeMap Word64 :=
  [("dup", ([("x", .one), ("x", .one)], .skip, .one))]

def observesDuplicateFormals : Bool :=
  match panSemLookupStateCodeHOL (lookupState duplicateFormalCode) "dup"
      [.word (7 : Word64), .word (8 : Word64)] with
  | none => true
  | some _ => false

#guard observesSuccessfulLookup
#guard observesMissingFunction
#guard observesWrongArity
#guard observesWrongShape
#guard observesDuplicateFormals

/-- The successful HOL lookup and the evaluator's production lookup agree on
    the complete entry result, including fresh local bindings. -/
example : ∃ holLocals productionLocals,
    panSemLookupStateCodeHOL (lookupState singleParameterCode) "id"
      [.word (7 : Word64)] = some (.skip, holLocals, .one) ∧
    lookupPanSemCodeCall [] singleParameterCode "id" [.word (7 : Word64)] =
      some (.skip, .one, productionLocals) ∧
    ∀ name, productionLocals name =
      (FLOOKUP holLocals name).map HolValue.toPanValue := by
  exact panSemLookupStateCodeHOL_matches_production_entry
    (lookupState singleParameterCode) "id" [.word (7 : Word64)]
    [("x", Shape.one)] .skip Shape.one
    (by simp [lookupState, singleParameterCode, panSemCodeLookup, lookupInfo])
    (by decide)
    (by simp [panSemCodeArgumentsMatch, panValueShape, panShapeMatches])

def runChecks : IO Bool := do
  if observesSuccessfulLookup then IO.println "PASS lookup_code binds a word argument from state-owned code"
    else IO.println "FAIL lookup_code binds a word argument from state-owned code"
  if observesMissingFunction then IO.println "PASS lookup_code rejects a missing function"
    else IO.println "FAIL lookup_code rejects a missing function"
  if observesWrongArity then IO.println "PASS lookup_code rejects wrong arity"
    else IO.println "FAIL lookup_code rejects wrong arity"
  if observesWrongShape then IO.println "PASS lookup_code rejects wrong shape"
    else IO.println "FAIL lookup_code rejects wrong shape"
  if observesDuplicateFormals then IO.println "PASS lookup_code rejects duplicate formals"
    else IO.println "FAIL lookup_code rejects duplicate formals"
  pure (observesSuccessfulLookup && observesMissingFunction && observesWrongArity &&
    observesWrongShape && observesDuplicateFormals)

end Flapjack.Test.PanSemLookupCodeParity
