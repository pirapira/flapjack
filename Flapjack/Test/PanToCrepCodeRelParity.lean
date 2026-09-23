import Flapjack.Pancake.Proofs.PanToCrep

/-! Nonvacuous checks for HOL `code_rel_def`, paired with the direct
CakeML/HOL oracle in `scripts/hol-probes/code_rel_probe.out`. The source map
contains a real function entry; the target map must carry its exact generated
parameter slots and compiled body. -/

namespace Flapjack.Test.PanToCrepCodeRelParity

open Flapjack

def parameterShapes : List (VarName × Shape) := [("x", .one)]
def sourceBody : Prog Nat := .return (.var .local "x")

def compilerFunctions : FiniteMap String (List (String × Shape) × Shape) :=
  FUPDATE FEMPTY ("f", (parameterShapes, .one))

def proofContext : PanToCrepProofContext Nat :=
  ctxtFc compilerFunctions FEMPTY ["x"] [.one] [0]

def sourceCode : FiniteMap String (List (String × Shape) × Prog Nat × Shape) :=
  FUPDATE FEMPTY ("f", (parameterShapes, sourceBody, .one))

def matchingTargetCode : FiniteMap String (List Nat × CrepProg Nat) :=
  FUPDATE FEMPTY ("f", ([0], .return [.var 0]))

def wrongBodyTargetCode : FiniteMap String (List Nat × CrepProg Nat) :=
  FUPDATE FEMPTY ("f", ([0], .skip))

def missingSignatureContext : PanToCrepProofContext Nat :=
  ctxtFc FEMPTY FEMPTY ["x"] [.one] [0]

def wrongSignatureContext : PanToCrepProofContext Nat :=
  ctxtFc (FUPDATE FEMPTY ("f", (parameterShapes, .comb [])))
    FEMPTY ["x"] [.one] [0]

def unlocalisedSourceCode : FiniteMap String
    (List (String × Shape) × Prog Nat × Shape) :=
  FUPDATE FEMPTY ("f", (parameterShapes,
    .assign .global "x" (.var .local "x"), .one))

def matchingTargetGuard : Bool :=
  match FLOOKUP matchingTargetCode "f" with
  | some ([0], .return [.var 0]) => true
  | _ => false

def wrongBodyTargetGuard : Bool :=
  match FLOOKUP wrongBodyTargetCode "f" with
  | some ([0], .skip) => true
  | _ => false

def compiledReturnGuard : Bool :=
  match compileCodeRelProg proofContext sourceBody with
  | .return [.var 0] => true
  | _ => false

/-! The direct HOL `global_dest` probe in `compile_prog_probe.out` emits
    `Call (SOME ([0; 1], NONE))`. `freeVarIds` omits the Global destination,
    so this fixture guards the proof adapter's additional lookup projection.
    `localisedProg` still excludes this source from `codeRel` itself. -/
def globalDestinationProofContext : PanToCrepProofContext Nat :=
  { vars := FUPDATE FEMPTY ("pair", (.comb [.one, .one], [0, 1]))
    funcs := FUPDATE FEMPTY ("f", ([], .comb [.one, .one]))
    eids := FEMPTY
    vmax := 1 }

def globalDestinationBody : Prog Nat :=
  .call (some (some (.global, "pair"), none)) "f" []

def compiledGlobalDestinationMatchesHolOracle : Bool :=
  match compileCodeRelProg globalDestinationProofContext globalDestinationBody with
  | .call (some ([0, 1], none)) "f" [] => true
  | _ => false

def compilerContext : PanToCrepCompileContext Nat :=
  compileCodeRelContext proofContext sourceBody

theorem sourceBodyFreeVariables : freeVarIds sourceBody = ["x"] := by
  simp [freeVarIds, expLocalVars, sourceBody]

theorem parameterVariableProjection :
    projectFiniteMapToInfoMap ["x"] proofContext.vars = [("x", (.one, [0]))] := by
  simp [proofContext, compilerFunctions, ctxtFc, projectFiniteMapToInfoMap,
    FUPDATE, FUPDATE_LIST, FEMPTY, FLOOKUP, withShape]

theorem compilerContextVariables :
    compilerContext.vars = [("x", (.one, [0]))] := by
  have hcalls : callVarsUsedByProg sourceBody = [] := by
    simp [sourceBody, callVarsUsedByProg]
  simp [compilerContext, compileCodeRelContext, sourceBodyFreeVariables, hcalls,
    parameterVariableProjection]

theorem compiledReturnMatchesHolOracle :
    compileCodeRelProg proofContext sourceBody = .return [.var 0] := by
  rw [compileCodeRelProg, compileProgFixed, sourceBody, compileProg_return]
  change CrepProg.return
    (compileExp ((compileCodeRelContext proofContext
      (.return (.var .local "x"))).toExecutable) (.var .local "x")).1 =
      .return [.var 0]
  have hvars :
      (compileCodeRelContext proofContext (.return (.var .local "x"))).toExecutable.vars =
        [("x", (.one, [0]))] := by
    simpa [compilerContext, sourceBody, PanToCrepCompileContext.toExecutable] using
      compilerContextVariables
  simp only [compileExp]
  rw [hvars]
  simp [lookupInfo]

theorem matchingCodeRel : codeRel proofContext sourceCode matchingTargetCode := by
  intro function variableShapes program returnShape hsource
  have hentry : "f" = function ∧ parameterShapes = variableShapes ∧
      sourceBody = program ∧ Shape.one = returnShape := by
    simpa [sourceCode, FLOOKUP, FUPDATE, FEMPTY] using hsource
  rcases hentry with ⟨rfl, rfl, rfl, rfl⟩
  have hlocal : localisedProg sourceBody := by
    simp [localisedProg, localisedExp, expGlobalVars, sourceBody]
  have hsignature :
      FLOOKUP proofContext.funcs "f" = some (parameterShapes, Shape.one) := by
    simp [proofContext, compilerFunctions, ctxtFc, FLOOKUP, FUPDATE]
  refine ⟨hlocal, hsignature, ?_⟩
  dsimp only [parameterShapes]
  simp only [List.map_cons, List.map_nil]
  have hslots : List.range (Shape.shapeSize (.comb [Shape.one])) = [0] := by
    simp [Shape.shapeSize]
  rw [hslots]
  have hnext :
      ctxtFc proofContext.funcs proofContext.eids ["x"] [.one] [0] = proofContext := by
    rfl
  rw [hnext, compiledReturnMatchesHolOracle]
  simp [matchingTargetCode, FLOOKUP, FUPDATE]

theorem rejectsWrongCompiledBody :
    ¬ codeRel proofContext sourceCode wrongBodyTargetCode := by
  intro hrel
  have hsource : FLOOKUP sourceCode "f" =
      some (parameterShapes, sourceBody, .one) := by
    simp [sourceCode, FLOOKUP, FUPDATE]
  have hcompiled := (hrel "f" parameterShapes sourceBody .one hsource).2.2
  simp [wrongBodyTargetCode, FLOOKUP, FUPDATE, proofContext, ctxtFc,
    compileCodeRelProg, compileProgFixed, sourceBody, parameterShapes,
    compilerFunctions, compileProg, compileExp] at hcompiled

theorem rejectsMissingFunctionSignature :
    ¬ codeRel missingSignatureContext sourceCode matchingTargetCode := by
  intro hrel
  have hsource : FLOOKUP sourceCode "f" =
      some (parameterShapes, sourceBody, .one) := by
    simp [sourceCode, FLOOKUP, FUPDATE]
  have hsignature := (hrel "f" parameterShapes sourceBody .one hsource).2.1
  simp [missingSignatureContext, ctxtFc, FLOOKUP, FEMPTY]
    at hsignature

theorem rejectsMismatchedReturnShape :
    ¬ codeRel wrongSignatureContext sourceCode matchingTargetCode := by
  intro hrel
  have hsource : FLOOKUP sourceCode "f" =
      some (parameterShapes, sourceBody, .one) := by
    simp [sourceCode, FLOOKUP, FUPDATE]
  have hsignature := (hrel "f" parameterShapes sourceBody .one hsource).2.1
  simp [wrongSignatureContext, ctxtFc, FLOOKUP, FUPDATE,
    parameterShapes] at hsignature

theorem rejectsUnlocalisedSource :
    ¬ codeRel proofContext unlocalisedSourceCode wrongBodyTargetCode := by
  intro hrel
  have hsource : FLOOKUP unlocalisedSourceCode "f" =
      some (parameterShapes, .assign .global "x" (.var .local "x"), .one) := by
    simp [unlocalisedSourceCode, FLOOKUP, FUPDATE]
  have hlocal := (hrel "f" parameterShapes
    (.assign .global "x" (.var .local "x")) .one hsource).1
  simp [localisedProg] at hlocal

#guard matchingTargetGuard
#guard wrongBodyTargetGuard
#guard compiledReturnGuard
#guard compiledGlobalDestinationMatchesHolOracle

def runChecks : IO Bool := do
  let checks := [
    ("HOL code_rel matching source and target entries", matchingTargetGuard),
    ("HOL code_rel wrong-body target fixture", wrongBodyTargetGuard),
    ("HOL code_rel compiled parameter return", compiledReturnGuard),
    ("HOL global call destination adapter", compiledGlobalDestinationMatchesHolOracle)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepCodeRelParity
