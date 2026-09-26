import Flapjack.Pancake.Semantics.PanSem.LookupCode
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

/-!
# Parity for Pancake `lookup_code_def`

The direct HOL observations live in `scripts/hol-probes/pan_sem_lookup_code_probe.out`.
The Lean fixtures call the tagged lookup through the source state's finite
`code` map, covering success and the four rejection boundaries from that
oracle.
-/

namespace Flapjack.Test.PanSemLookupCodeParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanPropsEvalStateFiniteExact

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

private def exactName : MlS := Flapjack.Basis.Pure.MlString.ofString "x"

private def exactFunction : MlS := Flapjack.Basis.Pure.MlString.ofString "id"

private def exactArgument : ValueHOL 8 := .val (.word (7 : BitVec 8))

private def exactArgumentExpression : ExpHOL 8 := .const (7 : BitVec 8)

private def exactNewLocals : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty.updateList [(exactName, exactArgument)]

/-- The exact finite-map state for HOL's successful word-argument lookup row. -/
private def exactLookupState : PanPropsEvalStateFiniteExact 8 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty.update
    (exactFunction, ([(exactName, ShapeHOL.one)], ProgHOL.skip, ShapeHOL.one))
  eshapes := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => True
  shMemaddrs := fun _ => True
  clock := 20
  be := false
  ffi := {
    oracle := fun _ state _ bytes => HolOracleResult.ret state bytes
    ffiState := ()
    ioEvents := [] }
  baseAddr := 0
  topAddr := 0

local instance : DecidablePred exactLookupState.memaddrs := fun _ => isTrue trivial

private theorem exactLookupArguments :
    exactLookupState.evalListHOL [exactArgumentExpression] = some [exactArgument] := by
  simp [PanPropsEvalStateFiniteExact.evalListHOL, evalListHOLExact, evalHOLExact,
    exactLookupState, exactArgumentExpression, exactArgument]

private theorem exactLookupEntry :
    lookupCodeHOLFinite exactLookupState exactFunction [exactArgument] =
      some (ProgHOL.skip, exactNewLocals, ShapeHOL.one) := by
  simp [lookupCodeHOLFinite, exactLookupState,
    exactFunction, exactName, exactArgument, exactNewLocals,
    HolFiniteMapExact.update, HolFiniteMapExact.updateList, FUPDATE_LIST, FUPDATE,
    shapeEqHOL, shapeOfHOLExact]

/-- The four hypotheses from the exact HOL lookup-step invariant hold in the
    success fixture, and the tagged theorem proves the installed argument is
    well formed. HOL's direct oracle row is
    `lookup_code_wf_shape_invariant_step_success=T`. -/
theorem exactLookupInvariantFixture :
    ∀ name value, exactNewLocals.lookup name = some value →
      isWfShapeValueHOLExact ([] : StructContextExact) value = true := by
  letI : DecidablePred exactLookupState.memaddrs := fun _ => isTrue trivial
  have hlocals : ∀ name value, exactLookupState.locals.lookup name = some value →
      isWfShapeValueHOLExact exactLookupState.structs value = true := by
    intro name value h
    simp [exactLookupState, HolFiniteMapExact.empty] at h
  have hglobals : ∀ name value, exactLookupState.globals.lookup name = some value →
      isWfShapeValueHOLExact exactLookupState.structs value = true := by
    intro name value h
    simp [exactLookupState, HolFiniteMapExact.empty] at h
  have hresult := lookupCodeWfShapeInvariantStep exactLookupState
    [exactArgumentExpression] [exactArgument] exactFunction ProgHOL.skip
    exactNewLocals ShapeHOL.one
  have hproperty := hresult ⟨exactLookupArguments, exactLookupEntry, hlocals, hglobals⟩
  simpa [exactLookupState] using hproperty

def exactLookupInvariantGuard : Bool :=
  isWfShapeValueHOLExact ([] : StructContextExact) exactArgument

#guard exactLookupInvariantGuard

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

/-- A successful lookup made by the production Call path recovers the exact
    HOL `lookup_code` locals without separate shape or duplicate-name inputs. -/
example : ∃ holLocals,
    panSemLookupStateCodeHOL (lookupState singleParameterCode) "id"
      [.word (7 : Word64)] = some (.skip, holLocals, .one) ∧
    ∀ name,
      (lookupPanSemCodeCall [] singleParameterCode "id" [.word (7 : Word64)]
        |>.map (fun entry => entry.2.2 name)) =
      some ((FLOOKUP holLocals name).map HolValue.toPanValue) := by
  have hentry : panSemCodeLookup singleParameterCode "id" =
      some ([ ("x", Shape.one) ], .skip, Shape.one) := by
    simp [singleParameterCode, panSemCodeLookup, lookupInfo]
  have hproduction : lookupPanSemCodeCall [] singleParameterCode "id"
      [.word (7 : Word64)] =
      some (.skip, Shape.one,
        updatePanValueMap (fun _ => none) "x" (.word (7 : Word64))) := by
    simp [lookupPanSemCodeCall, singleParameterCode, panSemCodeLookup, lookupInfo,
      panSemCodeArgumentsMatch, panValueShape, panShapeMatches,
      bindPanValueParameters]
  obtain ⟨holLocals, hhol, hlocals⟩ :=
    panSemLookupStateCodeHOL_of_production_success
      (lookupState singleParameterCode) "id" [.word (7 : Word64)]
      [("x", Shape.one)] .skip Shape.one
      (fun name => if name == "x" then some (.word (7 : Word64)) else none)
      hentry hproduction
  refine ⟨holLocals, hhol, ?_⟩
  intro name
  rw [hproduction]
  simp only [Option.map_some]
  congr 1
  simpa [updatePanValueMap] using hlocals name

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
  if exactLookupInvariantGuard then
    IO.println "PASS exact finite-map lookup installs a well-formed argument"
    else IO.println "FAIL exact finite-map lookup installs a well-formed argument"
  pure (observesSuccessfulLookup && observesMissingFunction && observesWrongArity &&
    observesWrongShape && observesDuplicateFormals && exactLookupInvariantGuard)

end Flapjack.Test.PanSemLookupCodeParity
