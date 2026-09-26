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

theorem compiledReturnMatchesHolOracle :
    compileCodeRelProg proofContext sourceBody = .return [.var 0] := by
  simp [compileCodeRelProg, compileProgHOL, compileExpHOL, sourceBody,
    proofContext, ctxtFc, FUPDATE_LIST, FUPDATE, FLOOKUP, withShape]

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
  simp [wrongBodyTargetCode, FLOOKUP, FUPDATE, parameterShapes] at hcompiled
  change [0] = List.range (Shape.shapeSize (.comb [Shape.one])) ∧
    CrepProg.skip = compileCodeRelProg
      (ctxtFc proofContext.funcs proofContext.eids ["x"] [.one]
        (List.range (Shape.shapeSize (.comb [Shape.one])))) sourceBody at hcompiled
  have hslots : List.range (Shape.shapeSize (.comb [Shape.one])) = [0] := by
    simp [Shape.shapeSize]
  have hnext : ctxtFc proofContext.funcs proofContext.eids ["x"] [.one] [0] =
      proofContext := by rfl
  rcases hcompiled with ⟨_hnames, hbody⟩
  rw [hslots, hnext, compiledReturnMatchesHolOracle] at hbody
  cases hbody

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

/-! Direct executable check for HOL `alookup_compile_prog_code`: a function
    declaration with empty parameters is looked up in `compile_to_crep` by the
    same name and yields the `crep_vars [] = []` slot list together with the
    compiled body. -/
def alookupDecls : List (Decl (BitVec 64)) :=
  [Decl.function ⟨"f", false, false, [], Prog.skip, Shape.one⟩,
   Decl.function ⟨"g", false, false, [("x", Shape.one)], Prog.skip, Shape.one⟩]

def alookupGuard : Bool :=
  match List.lookup "f" (compileToCrepHOL alookupDecls) with
  | some ([], _) => true
  | _ => false

example : List.lookup "f" (compileToCrepHOL alookupDecls) =
    some ([], panToCrepCompFuncRiscV
      (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL alookupDecls) 0
        (panToCrepGetEidsFromDeclsHOL alookupDecls)) [] .skip) :=
  alookupCompileToCrepCode alookupDecls "f" .skip .one
    (by decide)
    (by simp [alookupDecls, functionEntries])

/-- Exact-body guard (not just shape): the compiled `f` body is the concrete
    `comp_func ... [] Skip`, which further reduces to `Skip`, matching the HOL
    probe row `alookup_empty_params` (`body = comp_func ... [] Skip`). -/
example : List.lookup "f" (compileToCrepHOL alookupDecls) =
    some ([], CrepProg.skip) := by
  rw [alookupCompileToCrepCode alookupDecls "f" .skip .one
    (by decide)
    (by simp [alookupDecls, functionEntries])]
  simp only [panToCrepCompFuncRiscV, compileProgRiscV, compileProgHOL]

#guard alookupGuard

/-- Exact provenance guard for HOL `el_compile_prog_el_prog_eq`: the compiled
    entry at index 0 is sourced from the `f` declaration (empty params, body
    Skip, shape One), matching the HOL probe rows `source_el_f` and
    `compiled_el_f`. -/
example : (functionEntries alookupDecls)[0]? =
    some ("f", [], Prog.skip, Shape.one) := by
  apply elCompileToCrepElProgEq alookupDecls 0 "f"
    (panToCrepCompFuncRiscV
      (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL alookupDecls) 0
        (panToCrepGetEidsFromDeclsHOL alookupDecls)) [] Prog.skip)
    Prog.skip Shape.one
  · simp [compileToCrepHOL, alookupDecls, functionEntries, panToCrepVars_eq,
      Shape.shapeSize, functionInfosHOL_eq_makeFuncsHOL,
      panToCrepCompFuncRiscV_eq_compFuncHOL, panToCrepMkCtxtHOL]
  · decide
  · decide
  · simp [alookupDecls, functionEntries, lookupFunctionEntry]

def elCompileGuard : Bool :=
  match (functionEntries alookupDecls)[0]? with
  | some ("f", [], Prog.skip, Shape.one) => true
  | _ => false

#guard elCompileGuard

/-- Two-function declaration list used to exercise the exact HOL `make_funcs`
    port: `f` has no parameters, `g` has one. -/
def makeFuncsDecls : List (Decl (BitVec 64)) :=
  [Decl.function ⟨"f", false, false, [], Prog.skip, Shape.one⟩,
   Decl.function ⟨"g", false, false, [("x", Shape.one)], Prog.skip, Shape.one⟩]

example :
    FLOOKUP (makeFuncsHOL (functionEntries makeFuncsDecls)) "f" =
      some ([], Shape.one) := by
  simp [makeFuncsHOL, makeFuncsDecls, functionEntries, FUPDATE_LIST,
    FLOOKUP_update]

example :
    FLOOKUP (makeFuncsHOL (functionEntries makeFuncsDecls)) "g" =
      some ([("x", Shape.one)], Shape.one) := by
  simp [makeFuncsHOL, makeFuncsDecls, functionEntries, FUPDATE_LIST,
    FLOOKUP_update]

example :
    FLOOKUP (makeFuncsHOL (functionEntries makeFuncsDecls)) "h" = none := by
  simp [makeFuncsHOL, makeFuncsDecls, functionEntries, FUPDATE_LIST,
    FLOOKUP_update]

example : functionInfosHOL makeFuncsDecls =
    makeFuncsHOL (functionEntries makeFuncsDecls) :=
  functionInfosHOL_eq_makeFuncsHOL makeFuncsDecls

def makeFuncsGuard : Bool :=
  (FLOOKUP (makeFuncsHOL (functionEntries makeFuncsDecls)) "f").isSome

#guard makeFuncsGuard

/-- Two exception declarations used to exercise the exact HOL
    `get_eids_imp_excp_rel` port (`excp_rel` domain plus code injectivity). -/
def eidsDecls : List (Decl (BitVec 8)) :=
  [Decl.exnDecl "E" Shape.one, Decl.exnDecl "F" Shape.one]

example :
    excpRel (panToCrepGetEidsFromDeclsHOL eidsDecls)
      (panToCrepGetEidsFromDeclsHOL eidsDecls) :=
  getEidsFromDeclsImpExcpRel _ eidsDecls (by simp [sizeOfEids, eidsDecls]; decide) rfl

def getEidsGuard : Bool :=
  (FLOOKUP (panToCrepGetEidsFromDeclsHOL eidsDecls) "E" ==
    some (0 : BitVec 8)) &&
  (FLOOKUP (panToCrepGetEidsFromDeclsHOL eidsDecls) "F" ==
    some (1 : BitVec 8))

#guard getEidsGuard

/-- Parameter list for the `make_vmap` / `ctxt_fc` bridge used by HOL
    `mk_ctxt_code_imp_code_rel`'s context construction. -/
def bridgeParams : List (VarName × Shape) := [("x", .one), ("y", .one)]

example : panToCrepMakeVmapHOL bridgeParams =
    (ctxtFc (FEMPTY : FiniteMap FunName (List (VarName × Shape) × Shape))
      (FEMPTY : FiniteMap ExceptionId Nat) (bridgeParams.map Prod.fst)
      (bridgeParams.map Prod.snd) (panToCrepVars bridgeParams)).vars :=
  panToCrepMakeVmapHOL_eq_ctxtFcVars bridgeParams _ _

def vmapCtxtFCGuard : Bool :=
  match FLOOKUP (panToCrepMakeVmapHOL bridgeParams) "x",
        FLOOKUP (panToCrepMakeVmapHOL bridgeParams) "y" with
  | some (Shape.one, [0]), some (Shape.one, [1]) => true
  | _, _ => false

#eval vmapCtxtFCGuard

/-- makeFuncsHOL lookup link: the `g` entry of the function table is visible
    with its parameter list and return shape. -/
example :
    FLOOKUP (makeFuncsHOL (functionEntries makeFuncsDecls)) "g" =
      some ([("x", Shape.one)], Shape.one) :=
  makeFuncsHOL_lookup_of_lookup (functionEntries makeFuncsDecls) "g"
    [("x", Shape.one)] Prog.skip Shape.one
    (by simp [makeFuncsDecls, functionEntries, List.lookup_cons])

/-- General compiled-entry lookup: `g` compiles with its `crep_vars` slot list
    (`panToCrepVars [("x", one)] = [0]`) and the compiled body. -/
example : List.lookup "g" (compileToCrepHOL alookupDecls) =
    some (panToCrepVars [("x", Shape.one)], panToCrepCompFuncRiscV
      (panToCrepMkCtxtHOL FEMPTY (functionInfosHOL alookupDecls) 0
        (panToCrepGetEidsFromDeclsHOL alookupDecls)) [("x", Shape.one)]
      Prog.skip) :=
  alookupCompileToCrepCodeGeneral alookupDecls "g" [("x", Shape.one)]
    Prog.skip Shape.one
    (by simp [alookupDecls, functionEntries, List.lookup_cons])

def generalAlookupGuard : Bool :=
  match List.lookup "g" (compileToCrepHOL alookupDecls) with
  | some ([0], _) => true
  | _ => false

#guard generalAlookupGuard

/-- `mk_ctxt_code_imp_code_rel` on the two-function table: the compiled target
    table is `code_rel` to the source table under the `mk_ctxt` context. -/
example :
    codeRel
      { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
        funcs := functionInfosHOL alookupDecls
        eids := panToCrepGetEidsFromDeclsHOL alookupDecls
        vmax := 0 }
      (FUPDATE_LIST FEMPTY (functionEntries alookupDecls).reverse)
      (FUPDATE_LIST FEMPTY (compileToCrepHOL alookupDecls).reverse) :=
  mkCtxtCodeImpCodeRel alookupDecls (by decide) (by
    intro entry hmem
    simp only [alookupDecls, functionEntries, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> subst h <;> simp [localisedProg])

def mkCtxtCodeRelGuard : Bool :=
  match FLOOKUP (FUPDATE_LIST FEMPTY (compileToCrepHOL alookupDecls).reverse)
      "g" with
  | some ([0], _) => true
  | _ => false

#guard mkCtxtCodeRelGuard

/-- Exact finite-map `PanToCrepHOLContext` with `vmax = 5` used to check the
    compiler temporary freshness bounds. -/
def freshContext : PanToCrepHOLContext Nat :=
  { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
    funcs := (FEMPTY : FiniteMap String (List (String × Shape) × Shape))
    eids := (FEMPTY : FiniteMap String Nat)
    vmax := 5 }

example : (5 : Nat) ∉ allocatedNamesHOL freshContext Shape.one :=
  not_mem_allocatedNamesHOL freshContext Shape.one (by decide)
example : (5 : Nat) ∉ freshNamesHOL freshContext 4 2 :=
  not_mem_freshNamesHOL freshContext 4 2 (by decide) (by decide)

def freshnessGuard : Bool :=
  (allocatedNamesHOL freshContext Shape.one).all (fun slot => 5 < slot) &&
    (freshNamesHOL freshContext 4 2).all (fun slot => 5 < slot)

#guard freshnessGuard

example : (3 : Nat) ∈ crepAssignedFreeVars
    (CrepProg.assign 3 (CrepExp.const (0 : Nat))) := by
  rw [mem_crepAssignedFreeVars_assign]
example : (3 : Nat) ∉ crepAssignedFreeVars (CrepProg.skip : CrepProg Nat) := by
  simp [crepAssignedFreeVars]
example : (3 : Nat) ∈ crepAssignedFreeVars
    (CrepProg.seq (CrepProg.assign 3 (CrepExp.const (0 : Nat))) CrepProg.skip) := by
  rw [mem_crepAssignedFreeVars_seq]
  left
  rw [mem_crepAssignedFreeVars_assign]
example : (3 : Nat) ∉ crepAssignedFreeVars
    (CrepProg.shMem CrepMemOp.load8 7 (CrepExp.const (0 : Nat))) := by
  rw [mem_crepAssignedFreeVars_shMem]
  decide

/-- The `.var`-form nested-sequence assignment produced by the non-`distinctLists`
    branch of `compileProgHOL` assigns exactly the destination `names`. -/
example :
    crepAssignedFreeVars
        (crepNestedSeq
          ([1, 2].zipWith
            (fun name temporary => CrepProg.assign name (.var temporary : CrepExp Nat))
            [3, 4])) =
      [1, 2] :=
  crepAssignedFreeVars_nestedSeq_assign_var_zipWith (α := Nat) [1, 2] [3, 4] (by decide)

/-- Adding a variable's freshly allocated slots preserves the context
    freshness hypothesis for a slot that was neither used before nor among the
    new slots. -/
example :
    ∀ v sh ns',
      FLOOKUP
          (FUPDATE (freshContext.vars : FiniteMap String (Shape × List Nat))
            ("a", (Shape.one, [1]))) v = some (sh, ns') →
        (0 : Nat) ∉ ns' := by
  refine hfresh_update (context := freshContext) "a" Shape.one [1] 0 ?_ ?_
  · intro v sh ns' hlk
    simp [freshContext] at hlk
  · decide

/-- The exact HOL `not_mem_context_assigned_mem_gt` shape: a slot fresh for a
    `ctxtMax` context and absent from every recorded slot list cannot occur
    among the assigned free variables of any compiled program. -/
example : (5 : Nat) ∉ crepAssignedFreeVars
    (compileProgHOL freshContext
      (Prog.dec "n" Shape.one (.const (0 : Nat)) Prog.skip)) := by
  refine notMemContextAssignedMemGt freshContext
    (Prog.dec "n" Shape.one (.const (0 : Nat)) Prog.skip) 5 ?_ ?_ ?_
  · refine ⟨Nat.zero_le _, ?_⟩
    intro v a xs hlk
    simp [freshContext] at hlk
  · intro v sh ns' hlk
    simp [freshContext] at hlk
  · decide

/-- `distinctLists` is exactly set-disjointness, used by the context-rewrite
    theorem. -/
example : distinctLists [1, 2] [3, 4] = true := by decide

/-- The exact HOL `rewritten_context_unassigned` shape: extending a context with
    a variable's rewritten slot list (kept disjoint from the old list) leaves
    every old slot outside the compiled program's assigned free variables. -/
example (program : Prog Nat) (nctxt ctxt : PanToCrepHOLContext Nat) (v : VarName)
    (ns nvars : List Nat) (sh sh' : Shape)
    (hnctxt : nctxt =
      { ctxt with
        vars := FUPDATE ctxt.vars (v, (sh, nvars))
        vmax := ctxt.vmax + Shape.shapeSize sh })
    (hlookup : FLOOKUP ctxt.vars v = some (sh', ns))
    (hnoOverlap : noOverlap ctxt.vars) (hctxtMax : ctxtMax ctxt.vmax ctxt.vars)
    (hnoOverlapN : noOverlap nctxt.vars)
    (hctxtMaxN : ctxtMax nctxt.vmax nctxt.vars)
    (hdistinct : distinctLists nvars ns = true) :
    distinctLists ns (crepAssignedFreeVars (compileProgHOL nctxt program)) = true :=
  rewrittenContextUnassigned program nctxt ctxt v ns nvars sh sh' hnctxt hlookup
    hnoOverlap hctxtMax hnoOverlapN hctxtMaxN hdistinct

def rewrittenContextGuard : Bool :=
  distinctLists [1, 2] [3, 4]

def runChecks : IO Bool := do
  let checks := [
    ("HOL code_rel matching source and target entries", matchingTargetGuard),
    ("HOL code_rel wrong-body target fixture", wrongBodyTargetGuard),
    ("HOL code_rel compiled parameter return", compiledReturnGuard),
    ("HOL global call destination adapter", compiledGlobalDestinationMatchesHolOracle),
    ("HOL alookup_compile_prog_code empty-parameter entry", alookupGuard),
    ("HOL el_compile_prog_el_prog_eq indexed provenance", elCompileGuard),
    ("HOL make_funcs_def parameter table", makeFuncsGuard),
    ("HOL get_eids_imp_excp_rel exception codes", getEidsGuard),
    ("HOL mk_ctxt_code_imp_code_rel makeFuncsHOL/alookup link", generalAlookupGuard),
    ("HOL mk_ctxt_code_imp_code_rel make_vmap/ctxt_fc bridge", vmapCtxtFCGuard),
    ("HOL mk_ctxt_code_imp_code_rel compiled code_rel", mkCtxtCodeRelGuard),
    ("HOL-context compiler temporary freshness bounds", freshnessGuard),
    ("HOL rewritten_context_unassigned context rewrite", rewrittenContextGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepCodeRelParity
