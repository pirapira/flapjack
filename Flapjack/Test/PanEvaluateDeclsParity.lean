import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Proofs.PanGlobals.ShapeInfrastructure

/-!
# `panSem$evaluate_decls` parity

Expected branch results are recorded by the direct HOL-EVAL probe
`scripts/hol-probes/pan_evaluate_decls_probeScript.sml`, which evaluates
`cakeml/pancake/semantics/panSemScript.sml:814-835`. The Lean fixtures exercise
each declaration constructor, sequential state updates, and the source failure
cases. -/

namespace Flapjack.Test.PanEvaluateDeclsParity

open Flapjack

def inertAccess : PanValueMemoryAccess Nat :=
  { domain := fun _ => false
    wordOp := fun _ _ => none
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => none
    readWord := fun _ _ _ _ => none
    readByte := fun _ _ _ _ => none
    read16 := fun _ _ _ _ => none
    read32 := fun _ _ _ _ => none
    storeWord := fun _ _ _ _ _ => none
    storeByte := fun _ _ _ _ _ => none
    store16 := fun _ _ _ _ _ => none
    store32 := fun _ _ _ _ _ => none
    sharedRead := fun _ _ _ _ => none
    sharedStore := fun _ _ _ _ _ => none }

def wordReadAccess : PanValueMemoryAccess Nat :=
  { inertAccess with
    domain := fun address => address == 0
    readWord := fun domain memory _ address =>
      match domain address, memory address with
      | true, some (.word value) => some value
      | _, _ => none }

def noFfi : FfiState Unit :=
  { oracle := fun _ _ _ _ => .returned () []
    state := ()
    ioEvents := [] }

def initialRuntime : PanSemEvaluateState Nat Unit :=
  { structs := []
    functions := []
    locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    ffi := noFfi
    clock := 5
    baseAddress := 0
    topAddress := 100
    bytesInWord := 4
    memoryAccess := some inertAccess
    contracts := none
    memoryHandler := none }

def initialState : PanSemDeclarationState Nat Unit :=
  { runtime := initialRuntime, code := [], eshapes := [], memoryAccess := inertAccess }

def withLocalX : PanSemDeclarationState Nat Unit :=
  { initialState with runtime :=
      { initialRuntime with locals := fun name =>
          if name == "x" then some (.word 3) else none } }

def withWordMemory : PanSemDeclarationState Nat Unit :=
  { initialState with
    runtime := { initialRuntime with memory := fun address =>
      if address == 0 then (some (PanValue.word 9)) else none }
    memoryAccess := wordReadAccess }

def sampleFunction (returnShape : Shape := .one) : FunDecl Nat :=
  { name := "f"
    inline := false
    exported := false
    params := [("x", .one)]
    body := .skip
    returnShape := returnShape }

def withOldFunction : PanSemDeclarationState Nat Unit :=
  { initialState with code :=
      [("f", { params := [], body := .tick, returnShape := .one })] }

example : evaluateDecls initialState [] = some initialState := by
  simp [evaluateDecls]

example : evaluateDecls initialState [.name "S" []] = some initialState := by
  simp [evaluateDecls]

example :
    (evaluateDecls initialState [.decl .one "g" (.const 7)]).map
      (fun state => state.runtime.globals "g") = some (some (.word 7)) := by
  simp [evaluateDecls, evalPanValueExp, panSemDeclUpdateGlobal,
    panShapeMatches, panValueShape, initialState, initialRuntime]

example :
    (evaluateDecls withWordMemory
      [.decl .one "g" (.load .one (.const 0))]).map
      (fun state => state.runtime.globals "g") = some (some (.word 9)) := by
  simp [evaluateDecls, evalPanValueExp, panSemDeclUpdateGlobal, withWordMemory,
    wordReadAccess, initialState, initialRuntime, panShapeMatches, panValueShape,
    panValueFlatLoad, panValueFlatLoadFuel, panValueFlatReadWord, isWfShape]

example :
    evaluateDecls withWordMemory
      [.decl .one "g" (.load (.named "Missing") (.const 0))] = none := by
  simp [evaluateDecls, evalPanValueExp, withWordMemory, wordReadAccess,
    initialState, initialRuntime, panValueFlatLoad, isWfShape, lookupInfo]

example :
    (evaluateDecls withLocalX [.decl .one "g" (.const 7)]).map
      (fun state => state.runtime.locals "x") = some (some (.word 3)) := by
  simp [evaluateDecls, evalPanValueExp,
    panShapeMatches, panValueShape, withLocalX, initialState, initialRuntime]

example :
    (evaluateDecls initialState
      [.decl .one "g" (.const 7), .decl .one "h" (.var .global "g")]).map
      (fun state => (state.runtime.globals "g", state.runtime.globals "h")) =
        some (some (.word 7), some (.word 7)) := by
  simp [evaluateDecls, evalPanValueExp, panSemDeclUpdateGlobal,
    panShapeMatches, panValueShape, initialState, initialRuntime]

example :
    evaluateDecls withLocalX [.decl .one "g" (.var .local "x")] = none := by
  simp [evaluateDecls, evalPanValueExp, withLocalX, initialState, initialRuntime]

example :
    evaluateDecls initialState [.decl (.named "Missing") "g" (.const 7)] = none := by
  simp [evaluateDecls, evalPanValueExp, panShapeMatches, panValueShape,
    initialState, initialRuntime]

example :
    (evaluateDecls initialState [.function (sampleFunction)]).map
      (fun state => (lookupInfo "f" state.code).map
        (fun entry => (entry.params, entry.body, entry.returnShape))) =
      some (some ([("x", .one)], .skip, .one)) := by
  simp [evaluateDecls, sampleFunction, panSemDeclUpdateInfo, lookupInfo,
    initialState, initialRuntime, isWfShape]

example :
    (evaluateDecls withOldFunction [.function (sampleFunction)]).map
      (fun state => (lookupInfo "f" state.code).map
        (fun entry => (entry.params, entry.body, entry.returnShape))) =
      some (some ([ ("x", .one) ], .skip, .one)) := by
  simp [evaluateDecls, sampleFunction, withOldFunction, panSemDeclUpdateInfo,
    lookupInfo, initialState, initialRuntime, isWfShape]

example :
    evaluateDecls initialState
      [.function { (sampleFunction) with params := [("x", .named "Missing")] }] = none := by
  simp [evaluateDecls, sampleFunction, initialState, initialRuntime, isWfShape,
    lookupInfo]

example :
    evaluateDecls initialState
      [.function (sampleFunction (.named "Missing"))] = none := by
  simp [evaluateDecls, sampleFunction, initialState, initialRuntime, isWfShape,
    lookupInfo]

example :
    (evaluateDecls initialState [.exnDecl "E" .one]).map
      (fun state => lookupInfo "E" state.eshapes) = some (some .one) := by
  simp [evaluateDecls, panSemDeclUpdateInfo, lookupInfo,
    initialState, initialRuntime, isWfShape]

example :
    evaluateDecls
      { initialState with eshapes := [("E", .one)] } [.exnDecl "E" .one] = none := by
  simp [evaluateDecls, initialState, initialRuntime, lookupInfo]

example :
    evaluateDecls initialState [.exnDecl "E" (.named "Missing")] = none := by
  simp [evaluateDecls, initialState, initialRuntime, isWfShape, lookupInfo]

/-! Non-vacuity witness for the tagged HOL
    `evaluate_decls_functions_wf` port (`evaluateDeclsFunctionsWf`): the
    installed sample function's parameter and return shapes are well formed in
    the source struct context. -/
example : (sampleFunction).params.all
      (fun parameter => isWfShape initialRuntime.structs parameter.2) = true ∧
    isWfShape initialRuntime.structs (sampleFunction).returnShape = true := by
  cases h : evaluateDecls initialState [.function (sampleFunction)] with
  | none => simp [evaluateDecls, sampleFunction, initialState, initialRuntime,
      isWfShape] at h
  | some state' =>
      exact evaluateDeclsFunctionsWf initialState [.function (sampleFunction)]
        state' h (by simp)
        (by decide)

/-! Finite-map bridge for the declaration updates: `panSemDeclUpdateGlobal` is
    the repo `FUPDATE` and `panSemDeclUpdateInfo` agrees with `FUPDATE` on the
    finite-map view of the association list. -/
example : panSemDeclUpdateGlobal (fun _ => (none : Option (PanValue Nat)))
      "g" (.word 7) = FUPDATE (fun _ => none) ("g", .word 7) :=
  panSemDeclUpdateGlobal_eq_FUPDATE _ _ _

example :
    lookupInfo "h" (panSemDeclUpdateInfo [("g", (1 : Nat))] "g" 2) =
      FLOOKUP (FUPDATE (fun k => lookupInfo k [("g", (1 : Nat))]) ("g", 2)) "h" :=
  lookupInfo_panSemDeclUpdateInfo _ _ _ _

end Flapjack.Test.PanEvaluateDeclsParity
