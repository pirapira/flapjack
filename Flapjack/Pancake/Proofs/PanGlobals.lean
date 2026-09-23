import Flapjack.HolRef
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.ShapeInfrastructure
import Flapjack.Pancake.Semantics.PanSem

namespace Flapjack

/-! Flapjack-specific generalization for the parameterized
    \`globalCompileTopForStart\` analogue. The exact HOL-tagged theorem is
    \`globalCompileTopCake_all_function_or_exception\`, whose subject fixes
    \`bytes_in_word\` and \`n2w\`. -/
theorem globalCompileTopForStart_all_function_or_exception [BEq String]
    [Add α] [Mul α] (bytesInWord : α) (fromNat : Nat → α)
    (declarations : List (Decl α)) (start : FunName) :
    (globalCompileTopForStart bytesInWord fromNat declarations start).all
    (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  unfold globalCompileTopForStart
  cases hfind : globalFindFunction start declarations with
  | none =>
      simp [globalCompileTopForStartSome, hfind]
  | some entry =>
      simp only [globalCompileTopForStartSome, hfind, Option.getD_some]
      exact globalCompileDecs_result_all_function_or_exception _ _ _
        (by simp [globalDeclIsFunction])

@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_only_functions_or_exns"]
theorem globalCompileTopCake_all_function_or_exception {width : Nat}
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    (globalCompileTopCake declarations start).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  simpa [globalCompileTopCake] using
    (globalCompileTopForStart_all_function_or_exception
      (BitVec.ofNat width (width / 8)) (BitVec.ofNat width) declarations start)

/-! Generalized proof behind the exact fixed-word theorem below. -/
theorem globalCompileTopForStart_shapes_wf
    [LawfulBEq String] [Add α] [Mul α]
    [BEq α] [OfNat α 0] [OfNat α 1]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (bytesInWord : α) (fromNat : Nat → α)
    (state : PanSemDeclarationState α σ) (declarations : List (Decl α))
    (start : FunName) (state' : PanSemDeclarationState α σ)
    (heval : evaluateDecls state declarations = some state')
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    ∀ output, output ∈ globalCompileTopForStart bytesInWord fromNat declarations start →
      ∀ function, output = .function function →
        function.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) = true ∧
          isWfShape state.runtime.structs function.returnShape = true := by
  have hsourceShapes : declarations.all
      (panDeclShapesWellFormed state.runtime.structs) = true := by
    apply List.all_eq_true.mpr
    intro declaration hmem
    cases declaration with
    | function function =>
        simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed,
          Bool.and_eq_true] using
          (evaluateDeclsFunctionsWf state declarations state' heval hmem hadmissible)
    | decl shape name expression => simp [panDeclShapesWellFormed]
    | exnDecl exception shape => simp [panDeclShapesWellFormed]
    | name name fields => simp [panDeclShapesWellFormed]
  unfold globalCompileTopForStart
  cases hfind : globalFindFunction start declarations with
  | none =>
      simp [globalCompileTopForStartSome, hfind]
  | some entry =>
      let sorted := globalResortDecls declarations
      let newName := globalNewMainName declarations
      let renamed := globalRenameDecls start newName sorted
      let maxGlobalsSize := bytesInWord * fromNat
        ((globalDeclShapes renamed).map Shape.shapeSize |>.foldl (· + ·) 0)
      let initial : GlobalPassContext α :=
        { globals := []
          globalsSize := fromNat 0
          maxGlobalsSize := maxGlobalsSize
          bytesInWord := bytesInWord
          fromNat := fromNat }
      let compiled := globalCompileDecs initial renamed
      let mainDeclaration : Decl α :=
        .function
          { name := start
            inline := false
            exported := false
            params := entry.params
            body := .seq (nestedSeq compiled.initializers)
              (.call none newName (entry.params.map (fun (name, _) => Exp.var .local name)))
            returnShape := entry.returnShape }
      have hentryMem : (.function entry : Decl α) ∈ declarations := by
        exact globalFindFunction_mem start declarations entry hfind
      have hentryShapes := evaluateDeclsFunctionsWf state declarations state' heval
        hentryMem hadmissible
      have hmainShapes : panDeclShapesWellFormed state.runtime.structs
          mainDeclaration = true := by
        simpa [mainDeclaration, panDeclShapesWellFormed,
          panFunctionShapesWellFormed, Bool.and_eq_true] using hentryShapes
      have hsortedShapes := globalResortDecls_all_shapes state.runtime.structs
        declarations hsourceShapes
      have hotherShapes : sorted.all (fun declaration =>
          globalDeclIsFunction declaration ||
            panDeclShapesWellFormed state.runtime.structs declaration) = true :=
        globalDecls_all_or_of_all_left globalDeclIsFunction
          (panDeclShapesWellFormed state.runtime.structs) sorted hsortedShapes
      have hrenamedFunctionShapes := globalResortDecls_all_of_renamed
        state.runtime.structs start newName declarations hsortedShapes
      have hrenamedShapes : renamed.all
          (panDeclShapesWellFormed state.runtime.structs) = true := by
        change (globalRenameDecls start newName sorted).all
          (panDeclShapesWellFormed state.runtime.structs) = true
        exact globalRenameDecls_all_of_predicate start newName
          (panDeclShapesWellFormed state.runtime.structs) sorted hotherShapes
          hrenamedFunctionShapes
      have hrenamedShapes' : (globalRenameDecls start newName sorted).all
          (panDeclShapesWellFormed state.runtime.structs) = true := by
        change renamed.all (panDeclShapesWellFormed state.runtime.structs) = true
        exact hrenamedShapes
      have hcompiledBodies : renamed.all (fun declaration =>
          match declaration with
          | .function function =>
              panDeclShapesWellFormed state.runtime.structs
                (.function { function with
                  body := globalCompileProg (globalCollect initial renamed) function.body })
          | _ => true) = true := by
        change (globalRenameDecls start newName sorted).all (fun declaration =>
          match declaration with
          | .function function =>
              panDeclShapesWellFormed state.runtime.structs
                (.function { function with
                  body := globalCompileProg (globalCollect initial renamed) function.body })
          | _ => true) = true
        exact globalRenameDecls_all_of_body_compiled state.runtime.structs
          (globalCollect initial renamed) start newName sorted hrenamedShapes'
      have hcompiledShapes := globalCompileDecs_result_shapes_wf
        state.runtime.structs initial renamed mainDeclaration hmainShapes hcompiledBodies
      have hresult : (globalCompileTopForStart bytesInWord fromNat declarations start).all
          (panDeclShapesWellFormed state.runtime.structs) = true := by
        unfold globalCompileTopForStart
        simp only [globalCompileTopForStartSome, hfind, Option.getD_some]
        simpa [sorted, newName, renamed, maxGlobalsSize, initial, compiled,
          mainDeclaration] using hcompiledShapes
      intro output houtput function heq
      have hshape := List.all_eq_true.mp hresult output houtput
      cases output with
      | function actual =>
          have hsame : actual = function := by injection heq
          subst function
          simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed,
            Bool.and_eq_true] using hshape
      | decl shape name expression => cases heq
      | exnDecl exception shape => cases heq
      | name name fields => cases heq

/-! Exact-shaped port of Cake's `compile_top_shape_wf`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2458`). The output
    predicate is stated as a membership property equivalent to HOL `EVERY`;
    successful `evaluateDecls` and the source admissibility condition are the
    only semantic hypotheses. `globalCompileTopCake` fixes the HOL
    `bytes_in_word` and `n2w` choices instead of exposing caller-controlled
    compiler configuration. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf"]
theorem globalCompileTopCake_shapes_wf {width : Nat} [LawfulBEq String]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)]
    (state : PanSemDeclarationState (BitVec width) σ)
    (declarations : List (Decl (BitVec width))) (start : FunName)
    (state' : PanSemDeclarationState (BitVec width) σ)
    (heval : evaluateDecls state declarations = some state')
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    ∀ output, output ∈ globalCompileTopCake declarations start →
      ∀ function, output = .function function →
        function.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) = true ∧
          isWfShape state.runtime.structs function.returnShape = true := by
  simpa [globalCompileTopCake] using
    (globalCompileTopForStart_shapes_wf
      (BitVec.ofNat width (width / 8)) (BitVec.ofNat width)
      state declarations start state' heval hadmissible)

/-! Cake's `is_wf_shape_nil` predicate is the well-formedness test with no
    declared structures. This local spelling keeps the corollary's conclusion
    in the same shape as HOL while reusing the shared Flapjack predicate. -/
def isWfShapeNil : Shape → Bool := isWfShape []

/-- HOL's empty-structure corollary: successful declaration evaluation and
    admissible declarations give well-formed output shapes under `isWfShapeNil`.
    The empty-structure premise is explicit, as in the HOL statement. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf_nil"]
theorem globalCompileTopCake_shapes_wf_nil {width : Nat} [LawfulBEq String]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)]
    (state : PanSemDeclarationState (BitVec width) σ)
    (declarations : List (Decl (BitVec width))) (start : FunName)
    (state' : PanSemDeclarationState (BitVec width) σ)
    (heval : evaluateDecls state declarations = some state')
    (hstructs : state.runtime.structs = [])
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    ∀ output, output ∈ globalCompileTopCake declarations start →
      ∀ function, output = .function function →
        function.params.all (fun parameter =>
          isWfShapeNil parameter.2) = true ∧
          isWfShapeNil function.returnShape = true := by
  have hshapes := globalCompileTopCake_shapes_wf
    state declarations start state' heval hadmissible
  simpa [isWfShapeNil, hstructs] using hshapes

/-! Exact-shaped port of Cake's `exceptions_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2507`). `exceptionEntries`
    is the direct source-shaped counterpart of `panLang$exceptions`; the body is
    the existing production proof `exceptionEntries_append`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_append"]
theorem exceptions_append (declarations rest : List (Decl α)) :
    exceptionEntries (declarations ++ rest) =
      exceptionEntries declarations ++ exceptionEntries rest :=
  exceptionEntries_append declarations rest

/-! Exact-shaped port of Cake's `exceptions_FILTER_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2515`). The five
    conjuncts assemble the production filter lemmas; `globalDeclIsFunction`,
    `globalDeclIsException`, `globalDeclIsName`, and `globalDeclIsGlobal`
    correspond to HOL `is_function`, `is_exn_decl`, `is_name`, and `is_decl`,
    and `globalDeclsFilter` to HOL `FILTER`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_FILTER_is_function"]
theorem exceptions_FILTER_is_function (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) = [] ∧
    exceptionEntries
        (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
          declarations) = exceptionEntries declarations ∧
    exceptionEntries (globalDeclsFilter globalDeclIsException declarations) =
      exceptionEntries declarations ∧
    exceptionEntries (globalDeclsFilter globalDeclIsName declarations) = [] ∧
    exceptionEntries (globalDeclsFilter globalDeclIsGlobal declarations) = [] :=
  ⟨exceptionEntries_filter_function declarations,
    exceptionEntries_filter_not_function declarations,
    exceptionEntries_filter_exception declarations,
    exceptionEntries_filter_name declarations,
    exceptionEntries_filter_global declarations⟩

end Flapjack
