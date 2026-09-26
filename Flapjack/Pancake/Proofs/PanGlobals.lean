import Flapjack.HolRef
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Proofs.PanGlobals.ShapeInfrastructure
import Flapjack.Pancake.Semantics.PanSem

namespace Flapjack

open Flapjack.Pancake.PanLang

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

-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem globalCompileTopCake_all_function_or_exception {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    (globalCompileTopCake declarations start).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  rw [globalCompileTopCake_eq]
  simp only [cakeBytesInWord]
  exact globalCompileTopForStart_all_function_or_exception
    (BitVec.ofNat width (width / 8)) (BitVec.ofNat width) declarations start

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
      have hcompiledBodies : ∀ context, renamed.all (fun declaration =>
          match declaration with
          | .function function =>
              panDeclShapesWellFormed state.runtime.structs
                (.function { function with
                  body := globalCompileProg context function.body })
          | _ => true) = true := by
        intro context
        change (globalRenameDecls start newName sorted).all (fun declaration =>
          match declaration with
          | .function function =>
              panDeclShapesWellFormed state.runtime.structs
                (.function { function with
                  body := globalCompileProg context function.body })
          | _ => true) = true
        exact globalRenameDecls_all_of_body_compiled state.runtime.structs
          context start newName sorted hrenamedShapes'
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

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `compile_top_shape_wf`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2458`). The output
    predicate is stated as a membership property equivalent to HOL `EVERY`;
    successful `evaluateDecls` and the source admissibility condition are the
    only semantic hypotheses. `globalCompileTopCake` fixes the HOL
    `bytes_in_word` and `n2w` choices instead of exposing caller-controlled
    compiler configuration. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`) plus
-- executable-only `[LawfulBEq String]`/`[ShiftLeft]`/`[ShiftRight]` binders, while HOL
-- `pan_globalsProofScript.sml:2458-2492` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a shape-wellformedness predicate over `Decl`/`Shape`, so
-- `names_as_string` cannot authorise those carriers and no `NameRanged` byte witness
-- applies. The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem globalCompileTopCake_shapes_wf {width : Nat} [NeZero width] [LawfulBEq String]
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
  rw [globalCompileTopCake_eq]
  simp only [cakeBytesInWord]
  exact globalCompileTopForStart_shapes_wf
      (BitVec.ofNat width (width / 8)) (BitVec.ofNat width)
      state declarations start state' heval hadmissible

/-! Cake's `is_wf_shape_nil` predicate is the well-formedness test with no
    declared structures. This local spelling keeps the corollary's conclusion
    in the same shape as HOL while reusing the shared Flapjack predicate. -/
def isWfShapeNil : Shape → Bool := isWfShape []

/-- HOL's empty-structure corollary: successful declaration evaluation and
    admissible declarations give well-formed output shapes under `isWfShapeNil`.
    The empty-structure premise is explicit, as in the HOL statement. The
    related HOL theorem at `pan_globalsProofScript.sml:2495` concludes one
    `EVERY` predicate directly over `compile_top code start`; this theorem
    instead uses membership in `globalCompileTopCake` plus an equality test for
    each function output. That pointwise form and the production AST/evaluator
    are not the statement or carriers of the HOL declaration, so it remains
    an untagged Flapjack-specific consequence. No direct HOL oracle fixture for
    this theorem is currently recorded. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`). Even after that carrier lands, a faithful
-- port needs the HOL-shaped `EVERY` conclusion over the reviewed `compile_top`
-- definition and a direct source oracle regression.
theorem globalCompileTopCake_shapes_wf_nil {width : Nat} [NeZero width] [LawfulBEq String]
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

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `exceptions_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2507-2513`):

    ```sml
    Theorem exceptions_append:
      ∀ds ds'. exceptions (ds ++ ds') = exceptions ds ++ exceptions ds'
    ```

    `exceptionEntries` is the direct source-shaped counterpart of
    `panLang$exceptions`; the body is the existing production proof
    `exceptionEntries_append`.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`.
    `names_as_string` cannot authorise the embedded `Shape`/`Decl`/`Prog`
    carriers, and no `NameRanged` byte witness applies because the conclusion is
    an exception-list equation, not a name. The exact MlString identifier
    carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already records this
    hol_name as `documented_mismatch` (reviewer Codex). Evidence: the
    `exceptionEntries_append` regression guards and direct HOL rows in
    `scripts/hol-probes/pan_lang_exceptions_probe.out`, sampled by
    `Flapjack/Test/PanGlobalsExceptionsAppendParity.lean`. Audit bead
    `flapjack-dlc.48`; exact-carrier dependencies `flapjack-6nn.3.1` and
    `flapjack-pxn.18.3.5.8`. -/
theorem exceptions_append (declarations rest : List (Decl α)) :
    exceptionEntries (declarations ++ rest) =
      exceptionEntries declarations ++ exceptionEntries rest :=
  exceptionEntries_append declarations rest

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `exceptions_FILTER_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2515-2524`):

    ```sml
    Theorem exceptions_FILTER_is_function:
      exceptions(FILTER is_function decs) = [] ∧
      exceptions(FILTER ($¬ o is_function) decs) = exceptions decs ∧
      exceptions(FILTER (is_exn_decl) decs) = exceptions decs ∧
      exceptions(FILTER (is_name) decs) = [] ∧
      exceptions(FILTER (is_decl) decs) = []
    ```

    The five conjuncts assemble the production filter lemmas;
    `globalDeclIsFunction`, `globalDeclIsException`, `globalDeclIsName`, and
    `globalDeclIsGlobal` correspond to HOL `is_function`, `is_exn_decl`,
    `is_name`, and `is_decl`, and `globalDeclsFilter` to HOL `FILTER`.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`.
    `names_as_string` cannot authorise the embedded `Shape`/`Decl`/`Prog`
    carriers, and no `NameRanged` byte witness applies because the conclusion is
    a conjunction of exception-list equations, not a name. The exact MlString
    identifier carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already records this
    hol_name as `documented_mismatch` (reviewer Codex). Evidence: the
    `exceptionEntries_filter_*` regression guards and direct HOL rows in
    `scripts/hol-probes/pan_lang_exceptions_probe.out`, sampled by
    `Flapjack/Test/PanGlobalsExceptionsFilterIsFunctionParity.lean`. Audit bead
    `flapjack-dlc.47`; exact-carrier dependencies `flapjack-6nn.3.1` and
    `flapjack-pxn.18.3.5.8`. -/
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

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `not_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2527`). `isName`,
    `isDecl`, and `isExnDecl` are the source-shaped counterparts of HOL
    `is_name`, `is_decl`, and `is_exn_decl`; `globalDeclIsFunction` is the
    pass-facing `is_function`. The production module keeps the three
    per-predicate helper lemmas, assembled here. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`),
-- while HOL `pan_globalsProofScript.sml:2527-2533` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a conjunction of `Decl`-predicate implications, so
-- `names_as_string` cannot authorise the embedded `Decl` carrier and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem not_is_function (declaration : Decl α) :
    (isName declaration = true → globalDeclIsFunction declaration = false) ∧
    (isDecl declaration = true → globalDeclIsFunction declaration = false) ∧
    (isExnDecl declaration = true → globalDeclIsFunction declaration = false) :=
  ⟨isName_not_function declaration, isDecl_not_function declaration,
    isExnDecl_not_function declaration⟩

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `decl_distinct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2535`): a value
    declaration is disjoint from the name, function, and exception
    declaration classes. `a && b = false` is the Bool spelling of HOL
    `a ∧ b ⇔ F`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`),
-- while HOL `pan_globalsProofScript.sml:2535-2541` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a Bool conjunction of `Decl`-predicates, so
-- `names_as_string` cannot authorise the embedded `Decl` carrier and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem decl_distinct (declaration : Decl α) :
    (isDecl declaration && isName declaration) = false ∧
    (isDecl declaration && globalDeclIsFunction declaration) = false ∧
    (isDecl declaration && isExnDecl declaration) = false := by
  cases declaration <;> simp [isDecl, isName, isExnDecl, globalDeclIsFunction]

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `functions_filter_nil`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2967-2971`):
    `!decls. functions (FILTER ($¬ ∘ is_function) decls) = []` — filtering out
    function declarations leaves an empty function table. The Lean statement
    mirrors the shape clause-for-clause: `globalDeclsFilter` is the source-shaped
    `FILTER`, `globalDeclIsFunction` the pass-facing `is_function`, and the
    conclusion is `functions ... = []` on both sides. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`) and
-- runs over the generic `Decl α` / `Prog α` syntax, while HOL `pan_globalsProofScript.sml`
-- keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring` and is indexed by a
-- positive-width `'a word`; `globalDeclsFilter`/`globalDeclIsFunction` are Flapjack
-- mirrors, not the tagged HOL `FILTER`/`is_function`. `names_as_string` cannot
-- authorise the embedded `Shape`/`Prog`/`Decl` carriers, and no `NameRanged` byte
-- witness applies (the conclusion is `functions ... = []`, not a name).
-- `docs/HOL-THEOREM-MAP.json` records this hol_name as `documented_mismatch`.
-- Oracle/regression evidence: `Flapjack/Test/PanGlobalsFunctionsFilterNilParity.lean`
-- (`functionsFilterNilFixture` :19 and `functionsFilterNilGuard` :33 over a mixed
-- `.function`/`.name`/`.exnDecl`/`.decl` list, `#guard` true). The exact MlString
-- identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem functions_filter_nil (declarations : List (Decl α)) :
    functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) = [] :=
  functions_globalDeclsFilter_not_function declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's
    `functions_FILTER_exn_decl`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2042-2046`):
    ```sml
    Theorem functions_FILTER_exn_decl:
      ∀prog. functions (FILTER is_exn_decl prog) = []
    ```
    The Lean statement mirrors the shape clause-for-clause: `globalDeclsFilter`
    is the source-shaped `FILTER`, `isExnDecl` is the source-shaped
    `is_exn_decl`, and the conclusion `functions … = []` matches, with
    `functions` being the source-shaped `functionEntries` table.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`.
    `names_as_string` cannot authorise the embedded `Shape`/`Decl`/`Prog`
    carriers, and no `NameRanged` byte witness applies because the conclusion is
    a membership/emptiness equation over function tables, not a name. The exact
    MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
    (parent `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already
    records this hol_name as `documented_mismatch` (reviewer Codex). Evidence:
    the source-shaped predicate facts in
    `Flapjack/Test/PanGlobalsDeclPredicateParity.lean` over a mixed
    `.function`/`.name`/`.exnDecl`/`.decl` list. -/
theorem functions_FILTER_exn_decl (declarations : List (Decl α)) :
    functions (globalDeclsFilter isExnDecl declarations) = [] :=
  functions_globalDeclsFilter_exnDecl declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `functions_FILTER_is_name`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2049-2053`):

    ```sml
    Theorem functions_FILTER_is_name:
      ∀prog. functions (FILTER is_name prog) = []
    ```

    Keeping only name declarations leaves an empty function table. The Lean
    statement mirrors the HOL shape clause-for-clause: `globalDeclsFilter` is
    the source-shaped `FILTER`, `isName` is the source-shaped `is_name`, and the
    conclusion `functions … = []` matches, with `functions` being the
    source-shaped `functionEntries` table.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`.
    `names_as_string` cannot authorise the embedded `Shape`/`Decl`/`Prog`
    carriers, and no `NameRanged` byte witness applies because the conclusion is
    a membership/emptiness equation over function tables, not a name. The exact
    MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
    (parent `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already
    records this hol_name as `documented_mismatch` (reviewer Codex). Evidence:
    the source-shaped predicate facts in
    `Flapjack/Test/PanGlobalsDeclPredicateParity.lean` over a mixed
    `.function`/`.name`/`.exnDecl`/`.decl` list. -/
theorem functions_FILTER_is_name (declarations : List (Decl α)) :
    functions (globalDeclsFilter isName declarations) = [] :=
  functions_globalDeclsFilter_isName declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `MEM_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2380`): every entry of
    `functions` comes from a `.function` declaration of the source list, with
    the entry being that declaration's name, parameters, body, and return
    shape. Wraps the reviewed production lemma `mem_functions`
    (`Flapjack/Pancake/PanSimp.lean`). -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem MEM_functions {declarations : List (Decl α)}
    {entry : FunName × List (VarName × Shape) × Prog α × Shape}
    (hmem : entry ∈ functions declarations) :
    ∃ declaration : FunDecl α,
      (.function declaration : Decl α) ∈ declarations ∧
        entry = (declaration.name, declaration.params, declaration.body,
          declaration.returnShape) :=
  mem_functions hmem

/-- Exact HOL port of Cake's `MEM_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2380-2387`): every entry
    of `functions decs` comes from a `Function` declaration of `decs`, and is
    that declaration's `(name, params, body, return)`.

    This is the faithful word-indexed port and uses the exact carriers:
    `DeclHOL`/`FunDeclHOL`/`ProgHOL width` with `MlS` names and `ShapeHOL`
    shapes, and the exact `functions` projection `functionsHOL`.  The
    Flapjack-specific production analogue `MEM_functions` above is keyed by
    Lean `String` identifiers and generic `Prog α`, so it is untagged. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "MEM_functions"]
theorem MEM_functionsHOL {width : Nat} [NeZero width]
    {declarations : List (DeclHOL width)}
    {entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL}
    (hmem : entry ∈ functionsHOL declarations) :
    ∃ declaration : FunDeclHOL width,
      (.function declaration : DeclHOL width) ∈ declarations ∧
        entry = (declaration.name, declaration.params, declaration.body,
          declaration.returnShape) := by
  induction declarations with
  | nil => simp [functionsHOL] at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | function funDecl =>
          simp only [functionsHOL, List.mem_cons] at hmem
          rcases hmem with hentry | htail
          · exact ⟨funDecl, by simp, hentry⟩
          · rcases ih htail with ⟨fi, hmem, heq⟩
            exact ⟨fi, by simp [hmem], heq⟩
      | decl shape name value =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩
      | exnDecl exceptionName shape =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩
      | name struct fields =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩

/-- Exact HOL port of Cake's `fperm_name_cancel`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1622-1626`):
    `fperm_name f g (fperm_name f g name) = name`.

    HOL's `fperm_name_cancel` carries no type annotation, so HOL states it
    polymorphically (`!f g name. fperm_name f g (fperm_name f g name) = name`
    at `'a -> 'a -> 'a -> 'a`).  The faithful Lean port is correspondingly
    generic in `α` with `[DecidableEq α]`, and uses the exact polymorphic
    `fpermName` (`Flapjack/Pancake/PanGlobals.lean`).  There is no side
    condition.  The production `String`-specialized `fperm_name_cancel` below
    is only an instance of this polymorphic original and is left untagged.
    Direct HOL/Lean edge-case fixtures:
    `scripts/hol-probes/pan_globals_fperm_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cancel"]
theorem fpermName_cancel {α : Type u} [DecidableEq α] (f g name : α) :
    fpermName f g (fpermName f g name) = name := by
  unfold fpermName
  repeat' split <;> simp_all

/-- Exact HOL port of Cake's `fperm_name_cong`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1629-1632`):
    `fperm_name f g x = fperm_name f g y ⇔ x = y`, i.e. the source/target
    renaming is injective.

    HOL's `fperm_name_cong` carries no type annotation, so HOL states it
    polymorphically; the faithful Lean port is correspondingly generic in `α`
    with `[DecidableEq α]` and uses the exact polymorphic `fpermName`.  There
    is no side condition.  The production `String`-specialized
    `fperm_name_cong` below is only an instance of this polymorphic original
    and is left untagged.  Direct HOL/Lean edge-case fixtures:
    `scripts/hol-probes/pan_globals_fperm_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cong"]
theorem fpermName_cong {α : Type u} [DecidableEq α] (f g left right : α) :
    fpermName f g left = fpermName f g right ↔ left = right := by
  constructor
  · intro h
    have := congrArg (fpermName f g) h
    rw [fpermName_cancel, fpermName_cancel] at this
    exact this
  · intro h
    rw [h]

/-- Production `String`-specialized form of Cake's polymorphic
    `fperm_name_cancel`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.52`): HOL's `fperm_name_cancel` has no
-- type annotation and HOL states it polymorphically, while this theorem
-- instantiates `α := String` (`FunName`).  It is a specialization of the HOL
-- original, not the original itself, so `names_as_string` does not justify the
-- tag.  The exact polymorphic port is `fpermName_cancel` above; this statement
-- is retained as production infrastructure.
theorem fperm_name_cancel [BEq String] [LawfulBEq String]
    (source target name : FunName) :
    globalRenameFunctionName source target
        (globalRenameFunctionName source target name) = name :=
  globalRenameFunctionName_cancel source target name

/-- Production `String`-specialized form of Cake's polymorphic
    `fperm_name_cong`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.53`): HOL's `fperm_name_cong` has no type
-- annotation and HOL states it polymorphically, while this theorem
-- instantiates `α := String` (`FunName`).  It is a specialization of the HOL
-- original, not the original itself, so `names_as_string` does not justify the
-- tag.  The exact polymorphic port is `fpermName_cong` above; this statement is
-- retained as production infrastructure.
theorem fperm_name_cong [BEq String] [LawfulBEq String]
    (source target left right : FunName) :
    globalRenameFunctionName source target left =
        globalRenameFunctionName source target right ↔
      left = right :=
  globalRenameFunctionName_cong source target left right

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `fperm_decs_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1663-1668`):

    ```sml
    Theorem fperm_decs_append:
      ∀f g xs ys. fperm_decs f g (xs ++ ys) = fperm_decs f g xs ++ fperm_decs f g ys
    ```

    The source-shaped `fperm_decs` (production `globalRenameDecls`) distributes
    over declaration list concatenation, matching HOL `++`/`fperm_decs` with Lean
    `++`/`globalRenameDecls`.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`; it also
    carries an executable-only `[BEq String]` argument absent in HOL, and
    `globalRenameDecls` is a Flapjack mirror, not the tagged HOL `fperm_decs`.
    `names_as_string` cannot authorise the embedded `Shape`/`Decl`/`Prog`
    carriers, and no `NameRanged` byte witness applies because the conclusion is
    a declaration-list equation, not a name. The exact MlString identifier
    carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already records this
    hol_name as `documented_mismatch` (reviewer Codex). Evidence: the
    `globalRenameDecls` append regression guards and the source-shaped
    predicate/rename facts in `Flapjack/Test/PanGlobalsDeclPredicateParity.lean`.
    -/
theorem fperm_decs_append [BEq String] (source target : FunName)
    (declarations rest : List (Decl α)) :
    globalRenameDecls source target (declarations ++ rest) =
      globalRenameDecls source target declarations ++
        globalRenameDecls source target rest :=
  globalRenameDecls_append source target declarations rest

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `functions_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1701-1708`):

    ```sml
    Theorem functions_fperm_decs:
      ∀x y code.
      functions (fperm_decs x y code) =
      MAP (λ(a,b,c,d). (fperm_name x y a, b, fperm x y c, d)) (functions code)
    ```

    The function table of a renamed declaration list is the renamed function
    table, matching HOL's `MAP (λ(a,b,c,d). (fperm_name x y a, b, fperm x y c, d))`
    with `globalRenameFunctionName`/`globalRenameProg` for `fperm_name`/`fperm`.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by a generic word `α` in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`; it also
    carries an executable-only `[BEq String]` argument absent in HOL, and the
    body-renaming map `globalRenameProg`/`globalRenameFunctionName` is a
    Flapjack mirror, not the tagged HOL `fperm`/`fperm_name`. `names_as_string`
    cannot authorise the embedded `Shape`/`Decl`/`Prog` carriers, and no
    `NameRanged` byte witness applies because the conclusion is a function-table
    equation (a list of `(name, params, body, shape)` tuples), not a name. The
    exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
    (parent `flapjack-pxn.18.3.5.7.2`). `docs/HOL-THEOREM-MAP.json` already
    records this hol_name as `documented_mismatch` (reviewer Codex). Evidence:
    the source-shaped predicate/rename facts in
    `Flapjack/Test/PanGlobalsDeclPredicateParity.lean` and the
    `globalRenameDecls` regression guards. -/
theorem functions_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    functions (globalRenameDecls source target declarations) =
      (functions declarations).map (fun entry =>
        (globalRenameFunctionName source target entry.1, entry.2.1,
          globalRenameProg source target entry.2.2.1, entry.2.2.2)) :=
  functions_globalRenameDecls source target declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `ALL_DISTINCT_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1711`): renaming
    declarations preserves distinctness of the function-name table. HOL
    `ALL_DISTINCT` is Lean `List.Nodup` and `MAP FST` is `List.map entry.1`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem ALL_DISTINCT_fperm_decs [BEq String] [LawfulBEq String]
    (source target : FunName) (declarations : List (Decl α))
    (hnodup : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions (globalRenameDecls source target declarations)).map
        (fun entry => entry.1)).Nodup :=
  globalRenameDecls_names_nodup source target declarations hnodup

/-! Exact-shaped port of Cake's `map_pick_up_first`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2995`): projecting the
    first component of a quadruple map recovers the mapped first components.
    HOL `MAP` is Lean `List.map` and `FST` is `Prod.fst`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "map_pick_up_first"]
theorem map_pick_up_first {α β γ δ ε ζ η θ : Type}
    (l : List (α × β × γ × δ)) (f1 : α → ε) (f2 : β → ζ) (f3 : γ → η)
    (f4 : δ → θ) :
    ((l.map (fun p => (f1 p.1, f2 p.2.1, f3 p.2.2.1, f4 p.2.2.2))).map Prod.fst) =
      (l.map Prod.fst).map f1 := by
  rw [List.map_map, List.map_map]
  rfl

/-! Exact-shaped port of Cake's `tuple_4_o`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:3003`): composing two
    quadruple projections composes the four component functions pointwise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "tuple_4_o"]
theorem tuple_4_o {α β γ δ ε ζ η θ ι κ ℓ μ : Type}
    (f1 : α → ε) (f2 : β → ζ) (f3 : γ → η) (f4 : δ → θ)
    (g1 : ι → α) (g2 : κ → β) (g3 : ℓ → γ) (g4 : μ → δ) :
    ((fun q : α × β × γ × δ => (f1 q.1, f2 q.2.1, f3 q.2.2.1, f4 q.2.2.2)) ∘
        (fun p : ι × κ × ℓ × μ =>
          (g1 p.1, g2 p.2.1, g3 p.2.2.1, g4 p.2.2.2))) =
      (fun p : ι × κ × ℓ × μ =>
        (f1 (g1 p.1), f2 (g2 p.2.1), f3 (g3 p.2.2.1), f4 (g4 p.2.2.2))) := by
  funext p
  obtain ⟨x, y, z, t⟩ := p
  rfl

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `dec_shapes_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2328`): the collected
    declaration shapes distribute over list append. `dec_shapes` is the
    production `globalDeclShapes`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`),
-- while HOL `pan_globalsProofScript.sml:2328-2331` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a `Shape`-list equation, so `names_as_string` cannot
-- authorise the embedded `Decl`/`Shape` carriers and no `NameRanged` byte witness
-- applies. The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem dec_shapes_append (declarations rest : List (Decl α)) :
    globalDeclShapes (declarations ++ rest) =
      globalDeclShapes declarations ++ globalDeclShapes rest :=
  globalDeclShapes_append declarations rest

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `dec_shapes_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2335`): a declaration
    list all of whose entries are functions collects no shapes. HOL `EVERY
    is_function` is Lean `List.all globalDeclIsFunction = true`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`),
-- while HOL `pan_globalsProofScript.sml:2335-2339` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a `Shape`-list equation, so `names_as_string` cannot
-- authorise the embedded `Decl`/`Shape` carriers and no `NameRanged` byte witness
-- applies. The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem dec_shapes_functions (declarations : List (Decl α))
    (hfunctions : declarations.all globalDeclIsFunction = true) :
    globalDeclShapes declarations = [] :=
  globalDeclShapes_of_functions declarations
    (fun declaration hmem => List.all_eq_true.mp hfunctions declaration hmem)

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `dec_shapes_FILTER`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2343`): filtering out
    function declarations preserves collected shapes, while filtering to names
    or exceptions yields none. HOL `FILTER` is Lean `globalDeclsFilter`,
    `is_decl` is `globalDeclIsGlobal` and `is_exn_decl` is
    `globalDeclIsException`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`),
-- while HOL `pan_globalsProofScript.sml:2343-2351` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a conjunction of `Shape`-list equations, so
-- `names_as_string` cannot authorise the embedded `Decl`/`Shape` carriers and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem dec_shapes_FILTER (declarations : List (Decl α)) :
    globalDeclShapes
        (globalDeclsFilter
          (fun declaration => !globalDeclIsFunction declaration) declarations) =
      globalDeclShapes declarations ∧
    globalDeclShapes (globalDeclsFilter globalDeclIsName declarations) = [] ∧
    globalDeclShapes (globalDeclsFilter globalDeclIsGlobal declarations) =
      globalDeclShapes declarations ∧
    globalDeclShapes (globalDeclsFilter globalDeclIsException declarations) = [] :=
  ⟨globalDeclShapes_globalDeclsFilter_not_function declarations,
    globalDeclShapes_globalDeclsFilter_name declarations,
    globalDeclShapes_globalDeclsFilter_global declarations,
    globalDeclShapes_globalDeclsFilter_exception declarations⟩

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `dec_shapes_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2354`): renaming does not
    change the collected declaration shapes. The source-shaped `fperm_decs` is
    the production `globalRenameDecls`, which only rewrites function entries. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`) plus
-- an executable-only `[BEq String]`, while HOL `pan_globalsProofScript.sml:2354-2357`
-- keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over
-- word-indexed `decl`. The conclusion is a `Shape`-list equation, so
-- `names_as_string` cannot authorise the embedded `Decl`/`Shape` carriers and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem dec_shapes_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalDeclShapes (globalRenameDecls source target declarations) =
      globalDeclShapes declarations := by
  induction declarations with
  | nil => simp [globalRenameDecls, globalDeclShapes_nil]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalRenameDecls, globalDeclShapes_cons, ih]

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `dec_shapes_resort_decls_def`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2361`): resorting
    declarations preserves the collected shapes. `resort_decls` is the
    production `globalResortDecls`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): besides production
-- String names versus HOL mlstring names (`pan_globalsProofScript.sml:2361-2364`),
-- this proof ranges over production `Decl α` and `Shape`; HOL's declarations contain
-- word-valued `ExpHOL width` and return `ShapeHOL`. The `names_as_string` qualifier
-- cannot account for those carrier differences and no `NameRanged` byte witness
-- applies (the conclusion is a `Shape`-list equation). Exact-carrier production
-- replacement is tracked by `flapjack-6nn.3.1`.
theorem dec_shapes_resort_decls_def (declarations : List (Decl α)) :
    globalDeclShapes (globalResortDecls declarations) =
      globalDeclShapes declarations :=
  globalDeclShapes_globalResortDecls declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `resort_decls_preserve_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2055`): resorting
    declarations leaves the function table unchanged. `resort_decls` is the
    production `globalResortDecls`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): besides production String names
-- versus HOL mlstring names, this proof ranges over production `Decl α`; HOL
-- `decl` contains word-valued `ExpHOL width`. The names_as_string qualifier
-- cannot account for this expression-carrier mismatch. Exact-carrier
-- production replacement is tracked by `flapjack-6nn.3.1`.
theorem resort_decls_preserve_functions (declarations : List (Decl α)) :
    functions (globalResortDecls declarations) = functions declarations :=
  functions_globalResortDecls declarations

/-! Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `fperm_decs_FILTER_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2032`): renaming commutes
    with filtering to the function declarations. HOL `fperm_decs` is the
    production `globalRenameDecls` and HOL `FILTER is_function` is Lean
    `globalDeclsFilter globalDeclIsFunction`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): besides the identifier-carrier
-- difference (production `FunName`/`VarName`/`ExceptionId`/`StructName`/`DeclarationName`
-- are `String`, whereas HOL keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`),
-- the statement ranges over production `Decl α`, whose `Const : α` and
-- `Prog α`/`Exp α` payloads generalise HOL's word-indexed `'a decl`
-- (`exp = Const ('a word)`, `panLangScript.sml`). The `names_as_string`
-- qualifier cannot cover that expression/program value-index difference while
-- the compiled functions `globalRenameDecls`/`globalDeclsFilter` keep their
-- production carriers. The exact MlString identifier carrier is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`) and the
-- exact-carrier production transformation by `flapjack-6nn.3.1`.
theorem fperm_decs_FILTER_is_function [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalRenameDecls source target
        (globalDeclsFilter globalDeclIsFunction declarations) =
      globalDeclsFilter globalDeclIsFunction
        (globalRenameDecls source target declarations) :=
  globalRenameDecls_filter_function source target declarations

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `fperm_decs_decls`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2023-2029`):

    ```sml
    Theorem fperm_decs_decls:
      ∀f g xs ys. EVERY ($¬ o is_function) xs ⇒ fperm_decs f g xs = xs
    ```

    The HOL statement carries an unused `ys` binder introduced by `recInduct`,
    reproduced here as `_unused` for statement parity. HOL
    `EVERY ($¬ ∘ is_function)` is Lean
    `declarations.all (fun declaration => !globalDeclIsFunction declaration)` and
    HOL `fperm_decs` is the source-shaped production `globalRenameDecls`.

    The tag stays WITHDRAWN as a documented carrier mismatch. The statement is
    keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/
    `StructName` = `String` (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/
    `exceptionEntries`) and by an arbitrary `α` payload in `Decl α`, whereas HOL
    `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/
    `stcname` = `mlstring` over the positive-width word-indexed `decl`; it also
    carries an executable-only `[BEq String]` argument absent in HOL, and
    `globalRenameDecls`/`globalDeclIsFunction` are Flapjack mirrors, not the
    tagged HOL `fperm_decs`/`is_function`. `names_as_string` cannot authorise the
    embedded `Shape`/`Decl`/`Prog` carriers, and no `NameRanged` byte witness
    applies because the conclusion is a declaration-list equality, not a name.
    The exact MlString identifier carrier is tracked by
    `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
    `docs/HOL-THEOREM-MAP.json` already records this hol_name as
    `documented_mismatch` (reviewer Codex). Evidence: the
    `globalRenameDecls_eq_self_of_no_functions` regression guards and
    `Flapjack/Test/PanGlobalsDeclPredicateParity.lean`. -/
theorem fperm_decs_decls [BEq String] (source target : FunName)
    (declarations _unused : List (Decl α))
    (hnone : declarations.all
      (fun declaration => !globalDeclIsFunction declaration) = true) :
    globalRenameDecls source target declarations = declarations :=
  globalRenameDecls_eq_self_of_no_functions source target declarations hnone

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `new_main_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2073`): the synthesized
    `main` entry-point name is not one of the program's existing function names.
    HOL's `MEM (new_main_name code) (MAP FST (functions code)) ⇒ F` is stated as
    failure of membership in `(functions declarations).map (fun entry => entry.1)`;
    `globalFunctionNames_eq_functions_map` bridges the production
    `globalFunctionNames`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): besides production String names
-- versus HOL mlstring names, the statement ranges over production `Decl α`,
-- whose expressions carry `Const : α`; HOL's `decl` carries word-valued
-- `ExpHOL width` with `Const : 'a word`. The names_as_string qualifier cannot
-- cover that input-carrier difference. The exact-carrier replacement is
-- tracked by `flapjack-6nn.3.1`.
theorem new_main_name_correct [BEq String] [LawfulBEq String]
    (declarations : List (Decl α)) :
    globalNewMainName declarations ∈
        (functions declarations).map (fun entry => entry.1) → False := by
  rw [← globalFunctionNames_eq_functions_map]
  exact globalNewMainName_not_mem declarations

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`): the name produced
    by the fresh-name search is not a member of the input list.  HOL
    `MEM (fresh_name name names) names ⇒ F` is proved here about the production
    fuel-bounded search `globalFreshName` (`globalFreshName_not_mem`), whereas
    the `@[hol]`-tagged source-shaped port of `fresh_name` is the separate
    recursive `freshNameHOL`, whose matching theorem is `freshNameHOL_not_mem_hol`.
    The tag therefore stays withdrawn for this declaration. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): besides production String names
-- versus HOL mlstring names (production identifiers `FunName`/`VarName`/
-- `ExceptionId`/`StructName` = `String` via `Decl`/`FunDecl`/`Shape`/
-- `functionEntries`/`exceptionEntries` versus HOL `funname`/`varname`/`eid`/
-- `stcname` = `mlstring`), this theorem is proved about the production
-- `globalFreshName` (candidate counter plus `names.length` fuel), not the
-- reviewed `freshNameHOL`.  The exact source-shaped counterpart over
-- `freshNameHOL` is `freshNameHOL_not_mem`; unifying the executable path so the
-- production search is the tagged definition is tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).  Direct HOL rows
-- are in `scripts/hol-probes/pan_globals_fresh_name_probe.out`.
theorem fresh_name_correct [BEq String] [LawfulBEq String]
    (name : String) (names : List String) :
    globalFreshName name names ∈ names → False :=
  globalFreshName_not_mem name names

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `fresh_name_correct'`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1003`): if every member
    of `names'` lies in `names`, then a name fresh for `names` is also fresh
    for `names'`.  HOL `set names' ⊆ set names` is stated pointwise, as in the
    production counterpart `globalFreshName_not_mem_of_subset`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- As for `fresh_name_correct`, the proof is over the production `globalFreshName`
-- rather than the reviewed source-shaped `freshNameHOL`; the exact tagged port is
-- the separate `freshNameHOL_not_mem_of_subset_hol`, so the tag remains
-- withdrawn for this declaration. The exact MlString
-- identifier carrier and executable-path unification are tracked by
-- `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem fresh_name_correct' [BEq String] [LawfulBEq String]
    (name : String) (names names' : List String)
    (hmem : globalFreshName name names ∈ names')
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    False :=
  globalFreshName_not_mem_of_subset name names names' hsubset hmem

/-- `@[hol]`-tagged exact source-shaped port of Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`): a name returned by
    the fresh-name search is not a member of the search list. HOL
    `MEM (fresh_name name names) names ⇒ F` becomes the equivalent
    `freshNameHOL name names ∉ names`. Statement, quantifiers, and body are
    exact apart from the HOL `mlstring`/Lean `String` carrier of `name` and the
    membership-only `names` list: `name` is byte-observable (the generated name
    crosses the compiler boundary and the same-module witness
    `holMlStringWitness_freshNameHOL_not_mem_hol` establishes
    `NameRanged (freshNameHOL name names)` from the input premise
    `NameRanged name`), while `names` is used only for membership equality.
    Delegates to the untagged helper `freshNameHOL_not_mem` in the definitional
    counterpart `Flapjack.Pancake.PanGlobals`, so the executed search runs the
    same recursion. Direct HOL rows are in
    `scripts/hol-probes/pan_globals_fresh_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct"
  (names_as_string := [name, names]) (names_as_string_boundary := [name])]
theorem freshNameHOL_not_mem_hol (name : String) (names : List String) :
    freshNameHOL name names ∉ names :=
  freshNameHOL_not_mem name names

/-- Same-module byte-rangedness witness for the tagged `fresh_name_correct`
    port `freshNameHOL_not_mem_hol`: the generated name is byte-ranged. -/
theorem holMlStringWitness_freshNameHOL_not_mem_hol (name : String)
    (names : List String) (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) :=
  holMlStringWitness_freshNameHOL name names h

/-- `@[hol]`-tagged exact source-shaped port of Cake's `fresh_name_correct'`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1003`): if every member
    of `names'` lies in `names`, then a name fresh for `names` is also fresh for
    `names'`. HOL `set names' ⊆ set names` is stated pointwise, as HOL itself
    uses it (`SUBSET_DEF`), and as HOL does, the proof goes through
    `fresh_name_correct`. Statement, hypotheses, and proof are exact apart from
    the HOL `mlstring`/Lean `String` carrier of `name` (byte-observable, witness
    `holMlStringWitness_freshNameHOL_not_mem_of_subset_hol`) and of the
    membership-only lists `names`/`names'`. Direct HOL rows are in
    `scripts/hol-probes/pan_globals_fresh_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct'"
  (names_as_string := [name, names, names']) (names_as_string_boundary := [name])]
theorem freshNameHOL_not_mem_of_subset_hol (name : String)
    (names names' : List String)
    (hmem : freshNameHOL name names ∈ names')
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    False :=
  freshNameHOL_not_mem_hol name names (hsubset _ hmem)

/-- Same-module byte-rangedness witness for the tagged `fresh_name_correct'`
    port `freshNameHOL_not_mem_of_subset_hol`: the generated name is
    byte-ranged. -/
theorem holMlStringWitness_freshNameHOL_not_mem_of_subset_hol (name : String)
    (names : List String) (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) :=
  holMlStringWitness_freshNameHOL name names h

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `FILTER_decs_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2832`): renaming
    commutes with filtering to the non-function declarations.  HOL
    `FILTER ($¬ ∘ is_function)` is `globalDeclsFilter (fun declaration =>
    !globalDeclIsFunction declaration)` and HOL `fperm_decs` is the reviewed
    production `globalRenameDecls`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem FILTER_decs_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        (globalRenameDecls source target declarations) =
      globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations :=
  globalRenameDecls_filter_not_function source target declarations

/-- Flapjack-only analogue of Cake's `compile_decs_EVERY_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1977`): every entry the
    compilation pass emits into the function table is a function declaration.
    As in HOL, the source is `code`, the four outputs `decls,funs,exns,ctxt'`
    are explicitly quantified, and the premise binds them to the pass result
    (`globalCompileDecs` returns a record in place of HOL's tuple).  This is
    not a HOL port: `globalCompileDecs` compiles every function body under the
    final collected context, whereas HOL `compile_decs` threads the context
    through declarations. A Function before a Decl distinguishes them. -/
theorem compile_decs_EVERY_is_function [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    funs.all globalDeclIsFunction = true := by
  simpa [hcompile] using globalCompileDecs_functions_all_isFunction context code

/-- Flapjack-only analogue of Cake's `compile_decs_decls_thm`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1967`): a program whose
    declarations contain no functions compiles to an empty function table.
    HOL `EVERY (λd. ¬is_function d)` is `code.all (fun declaration =>
    !globalDeclIsFunction declaration) = true`; the four outputs are quantified
    and bound by the equality premise as above. It is untagged because the
    subject `globalCompileDecs` uses the final context, unlike HOL's threaded
    `compile_decs` when a Function precedes a Decl. -/
theorem compile_decs_decls_thm [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' })
    (hnone : code.all (fun declaration => !globalDeclIsFunction declaration) = true) :
    funs = [] := by
  simpa [hcompile] using
    globalCompileDecs_functions_eq_nil_of_no_functions context code hnone

/-- Flapjack-only analogue of Cake's `compile_decs_exns_are_exns`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2448`): the exception
    table is exactly the exception declarations of the source program.  HOL
    `FILTER is_exn_decl` is `globalDeclsFilter globalDeclIsException`; the four
    outputs are quantified and bound by the equality premise as above. It is
    untagged because `globalCompileDecs` is not HOL's context-threading
    `compile_decs` for lists with a Function before a Decl. -/
theorem compile_decs_exns_are_exns [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    exns = globalDeclsFilter globalDeclIsException code := by
  simpa [hcompile] using globalCompileDecs_exceptions_eq_filter context code

/-- Flapjack-only analogue of Cake's `compile_decs_preserve_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2062`): compilation
    preserves the function-name table.  HOL `MAP FST (functions funs)` is
    `(functions funs).map (fun entry => entry.1)`; the four outputs are
    quantified and bound by the equality premise as above. It is untagged
    because its subject compiles functions under the final collected context,
    not HOL's context at each declaration position. -/
theorem compile_decs_preserve_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    (functions funs).map (fun entry => entry.1) =
      (functions code).map (fun entry => entry.1) := by
  simpa [hcompile] using globalCompileDecs_preserve_functions context code

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `EVERY_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2436`): if a predicate
    holds on every non-function declaration and on every renamed function
    declaration, it holds on every declaration produced by the renaming pass.
    HOL `EVERY (λd. ¬is_function d ⇒ P d)` is the boolean
    `declarations.all (fun d => globalDeclIsFunction d || predicate d) = true`;
    the function premise keeps HOL's `Function fi` destructuring. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName` = `String`
-- (via `Decl`/`FunDecl`/`Shape`/`functionEntries`/`exceptionEntries`), while HOL
-- `pan_globalsProofScript.sml` keys names by `funname`/`varname`/`eid`/`stcname` = `mlstring`.
-- HOL also quantifies a Prop-valued predicate `P`, whereas this executable
-- analogue fixes a Bool-valued predicate.  The exact theorem is tracked by
-- `flapjack-pxn.18.3.5.8.14`, depending on the MlString syntax carrier in
-- `flapjack-pxn.18.3.5.8`.
theorem EVERY_fperm_decs [BEq String] (source target : FunName)
    (predicate : Decl α → Bool) (declarations : List (Decl α))
    (hother : declarations.all
      (fun declaration => globalDeclIsFunction declaration || predicate declaration) = true)
    (hfunction : declarations.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              name := globalRenameFunctionName source target function.name
              body := globalRenameProg source target function.body })
        | _ => true) = true) :
    (globalRenameDecls source target declarations).all predicate = true :=
  globalRenameDecls_all_of_predicate source target predicate declarations
    hother hfunction

/-- Exact port of HOL `EVERY_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2436-2442`) over the
    reviewed word-indexed `DeclHOL width` carrier.

    HOL states, for a Prop-valued predicate `P`:
    `EVERY (λd. ¬ is_function d ⇒ P d) decs ∧
     EVERY (λd. ∀fi. d = Function fi ⇒
       P (Function (fi with <|name := fperm_name f g fi.name;
                              body := fperm f g fi.body|>))) decs
     ⇒ EVERY P (fperm_decs f g decs)`.
    The two `EVERY` hypotheses are membership-quantified `Prop` predicates
    over `DeclHOL width` (`∀ d ∈ decs, ...`, HOL's `EVERY` at `Prop`), the
    renamed-function hypothesis destructures exactly as HOL's `Function fi`
    (the renamed declaration uses the exact `fpermName`/`fpermHOL`), and the
    conclusion is `∀ d ∈ fpermDecsHOL f g decs, P d`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "EVERY_fperm_decs"]
theorem EVERY_fperm_decsHOL {width : Nat} [NeZero width] (f g : MlS)
    (P : DeclHOL width → Prop) (decs : List (DeclHOL width))
    (hother : ∀ d ∈ decs, isFunctionHOL d = false → P d)
    (hfunction : ∀ d ∈ decs, ∀ fi : FunDeclHOL width, d = .function fi →
        P (.function { fi with
          name := fpermName f g fi.name
          body := fpermHOL f g fi.body })) :
    ∀ d ∈ fpermDecsHOL f g decs, P d := by
  revert hother hfunction
  induction decs with
  | nil => intro _ _ d hd; simp [fpermDecsHOL] at hd
  | cons d ds ih =>
      intro hother hfunction e he
      cases d with
      | function fi =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq
            exact hfunction (.function fi) (by simp) fi rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | decl shape name value =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.decl shape name value) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | exnDecl exceptionName shape =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.exnDecl exceptionName shape) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | name struct fields =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.name struct fields) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem

/-- Exact port of HOL `FILTER_decs_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2832-2838`) over the
    reviewed word-indexed `DeclHOL width` carrier: removing the function
    declarations commutes with `fpermDecsHOL`.  HOL's `$¬ ∘ is_function` is
    `fun d => !isFunctionHOL d` and HOL's `FILTER` is `List.filter`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FILTER_decs_fperm_decs"]
theorem FILTER_decs_fperm_decsHOL {width : Nat} [NeZero width] (f g : MlS)
    (code : List (DeclHOL width)) :
    (fpermDecsHOL f g code).filter (fun d => !isFunctionHOL d) =
      code.filter (fun d => !isFunctionHOL d) := by
  induction code with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih =>
      cases d with
      | function fi =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_neg (by simp [isFunctionHOL]), if_neg (by simp [isFunctionHOL])]
          exact ih
      | decl shape name value =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]
      | exnDecl exceptionName shape =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]
      | name struct fields =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]

/-- Flapjack-only analogue of Cake's `compile_decs_FILTER_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2822`): filtering the
    source program to its value declarations leaves the initializers and the
    context unchanged and empties the function and exception tables.  HOL
    `FILTER is_decl` is `globalDeclsFilter isDecl`; the four outputs are
    quantified and bound by the equality premise as in the other
    `compile_decs` ports, and the result is stated as a whole record. It is
    untagged because `globalCompileDecs` does not thread the context through
    declarations like HOL's `compile_decs`. -/
theorem compile_decs_FILTER_decs [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    globalCompileDecs context (globalDeclsFilter isDecl code) =
      { initializers := decls, functions := [],
        exceptions := [], context := ctxt' } := by
  obtain ⟨hinit, hfuns, hexns, hctx⟩ := globalCompileDecs_filter_isDecl context code
  simp only [hcompile] at hinit hfuns hexns hctx
  cases h : globalCompileDecs context (globalDeclsFilter isDecl code)
  simp only [h] at hinit hfuns hexns hctx
  simp [hinit, hfuns, hexns, hctx]

/-- FLAPJACK-SPECIFIC (not an exact HOL port). This is Cake's
    `compile_decs_decls_thm` (`pan_globalsProofScript.sml:1967`) for the
    context-threading `globalCompileDecsThreaded`, but the quantifiers are not
    HOL's: the context exposes arbitrary `bytesInWord`/`fromNat`
    (`GlobalPassContext` generalizes HOL's fixed `bytes_in_word` and `n2w`), the
    word type carries arbitrary `[Add α] [Mul α]` rather than HOL's word
    operations, and `[BEq String]` is not required to be lawful.  An exact port
    over a canonical HOL word context is tracked by the dependency bead. -/
theorem compile_decs_decls_thm_threaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecsThreaded context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' })
    (hnone : code.all (fun declaration => !globalDeclIsFunction declaration) = true) :
    funs = [] := by
  have hfuns : funs = (globalCompileDecsThreaded context code).functions := by
    rw [hcompile]
  rw [hfuns]
  exact globalCompileDecsThreaded_functions_eq_nil_of_no_functions code context hnone

/-- FLAPJACK-SPECIFIC (not an exact HOL port). This is Cake's
    `compile_decs_EVERY_is_function` (`pan_globalsProofScript.sml:1977`) for the
    context-threading `globalCompileDecsThreaded`, but the context exposes
    arbitrary `bytesInWord`/`fromNat`, the word type carries arbitrary
    `[Add α] [Mul α]`, and `[BEq String]` need not be lawful; see the exact-port
    dependency bead. -/
theorem compile_decs_EVERY_is_function_threaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecsThreaded context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    funs.all globalDeclIsFunction = true := by
  have hfuns : funs = (globalCompileDecsThreaded context code).functions := by
    rw [hcompile]
  rw [hfuns]
  exact globalCompileDecsThreaded_functions_all_isFunction context code

/-- FLAPJACK-SPECIFIC (not an exact HOL port). This is Cake's
    `compile_decls_append` (`pan_globalsProofScript.sml:1997`) for the
    context-threading `globalCompileDecsThreaded`, with the same quantifier gap as
    the two theorems above: arbitrary `bytesInWord`/`fromNat`, arbitrary
    `[Add α] [Mul α]`, and possibly non-lawful `[BEq String]`; see the
    exact-port dependency bead. -/
theorem compile_decls_append_threaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (decs rest : List (Decl α)) :
    globalCompileDecsThreaded context (decs ++ rest) =
      let first := globalCompileDecsThreaded context decs
      let second := globalCompileDecsThreaded first.context rest
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } :=
  globalCompileDecsThreaded_append context decs rest

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `compile_decs_decls_thm`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1967`) for the canonical
    word context: if every declaration is not a function, `compile_decs` returns
    no compiled functions.  `compileDecsCake` is the exact tagged
    `compile_decs_def` port and `compileProgCake`/`compileExpCake`/`freshNameHOL`
    are the exact tagged `compile_def`/`compile_exp_def`/`fresh_name_def` ports.
    `CakeContext.globals` renders HOL's extensional finite map by a `FiniteMap`
    lookup function; the HOL clauses consult it only through `FLOOKUP`/`FUPDATE`,
    so the extra infinite-support lookups do not alter the port (same local
    argument as `compileExpCake`).  `width` is positive via `[NeZero width]`, as
    HOL `dimindex` is. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `CakeContext`/`Decl`/`FunDecl`/`Shape`/`functionEntries`) plus the
-- executable-only `[LawfulBEq String]`/`[NeZero width]` binders, while HOL
-- `pan_globalsProofScript.sml:1967-1972` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a `Decl`-list equation, so `names_as_string` cannot
-- authorise the embedded `Decl`/`Shape` carriers and no `NameRanged` byte witness
-- applies. The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
theorem compile_decs_decls_thm_cake [LawfulBEq String] {width : Nat} [NeZero width]
    (context : CakeContext width) (code : List (Decl (BitVec width)))
    (decls : List (Prog (BitVec width))) (funs exns : List (Decl (BitVec width)))
    (ctxt' : CakeContext width)
    (hcompile : compileDecsCake context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' })
    (hnone : code.all (fun declaration => !globalDeclIsFunction declaration) = true) :
    funs = [] := by
  have hfuns : funs = (compileDecsCake context code).functions := by
    rw [hcompile]
  rw [hfuns]
  exact compileDecsCake_functions_eq_nil_of_no_functions code context hnone

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `compile_decs_EVERY_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1977`) for the canonical
    word context: every returned declaration is a function.  The result uses
    the untagged, HOL-clause-shaped `compileDecsCake`; its carrier caveat and
    `[NeZero width]` are as in `compile_decs_decls_thm_cake`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `CakeContext`/`Decl`/`FunDecl`/`Shape`/`functionEntries`) plus the
-- executable-only `[LawfulBEq String]`/`[NeZero width]` binders, while HOL
-- `pan_globalsProofScript.sml:1977-1982` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a `Decl`-list predicate (`EVERY is_function`), so
-- `names_as_string` cannot authorise the embedded `Decl` carrier and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem compile_decs_EVERY_is_function_cake [LawfulBEq String] {width : Nat} [NeZero width]
    (context : CakeContext width) (code : List (Decl (BitVec width)))
    (decls : List (Prog (BitVec width))) (funs exns : List (Decl (BitVec width)))
    (ctxt' : CakeContext width)
    (hcompile : compileDecsCake context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    funs.all globalDeclIsFunction = true := by
  have hfuns : funs = (compileDecsCake context code).functions := by
    rw [hcompile]
  rw [hfuns]
  exact compileDecsCake_functions_all_isFunction context code

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's `compile_decls_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1997`) for the canonical
    word context: the second declaration list runs under the context reached by
    the first, and the output lists/context append.  The result uses the
    untagged, HOL-clause-shaped `compileDecsCake`; its carrier caveat and
    `[NeZero width]` are as in `compile_decs_decls_thm_cake`. -/
-- FLAPJACK-SPECIFIC (documented mismatch; tag stays withdrawn): the statement is
-- keyed by the production identifiers `FunName`/`VarName`/`ExceptionId`/`StructName`
-- = `String` (via `CakeContext`/`Decl`/`FunDecl`/`Shape`/`functionEntries`) plus the
-- executable-only `[LawfulBEq String]`/`[NeZero width]` binders, while HOL
-- `pan_globalsProofScript.sml:1997-2009` keys names by
-- `funname`/`varname`/`eid`/`stcname` = `mlstring` and ranges over word-indexed
-- `decl`. The conclusion is a tuple of `Decl`/context-list equations, so
-- `names_as_string` cannot authorise the embedded `Decl`/`Shape` carriers and no
-- `NameRanged` byte witness applies. The exact MlString identifier carrier is
-- tracked by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`).
theorem compile_decls_append_cake [LawfulBEq String] {width : Nat} [NeZero width]
    (context : CakeContext width) (decs rest : List (Decl (BitVec width))) :
    compileDecsCake context (decs ++ rest) =
      let first := compileDecsCake context decs
      let second := compileDecsCake first.context rest
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } :=
  compileDecsCake_append context decs rest

/-- Flapjack-only (untagged) counterpart of Cake's `compile_decs_functions_thm`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1951`) for
    `globalCompileDecsThreaded`, for a program consisting only of functions:
    the function table is the source list with each body compiled under the
    running context.  HOL's statement maps with an `ARB` fallback for
    non-function declarations; here the fallback is the identity declaration,
    which coincides with HOL exactly under the `EVERY is_function` premise, so
    this carries no `@[hol]` tag until the ARB rendering is reviewed. -/
theorem compile_decs_functions_thm_threaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (hall : code.all globalDeclIsFunction = true) :
    (globalCompileDecsThreaded context code).functions =
      code.map (fun declaration => match declaration with
        | .function function =>
            .function { function with body := globalCompileProg context function.body }
        | other => other) := by
  induction code generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [List.all_cons, globalDeclIsFunction, Bool.true_and] at hall
          simp only [globalCompileDecsThreaded, List.map_cons, ih context hall]
      | decl shape name value =>
          simp [List.all_cons, globalDeclIsFunction] at hall
      | exnDecl exception shape =>
          simp [List.all_cons, globalDeclIsFunction] at hall
      | name struct fields =>
          simp [List.all_cons, globalDeclIsFunction] at hall

/-- Exact-shaped port of Cake's `ALOOKUP_MAP3`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2841`). HOL's `ALOOKUP`
    is key-polymorphic; the reviewed `lookupInfo` is likewise key-polymorphic
    (`alist$ALOOKUP` counterpart), and under `[LawfulBEq κ]` its `==` test
    reflects HOL's `=`. The mapped value `(y, f z)` matches `OPTION_MAP (I ## f)`
    exactly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP3"]
theorem ALOOKUP_MAP3 [BEq κ] [LawfulBEq κ] (f : γ → δ)
    (entries : List (κ × (β × γ))) :
    (fun name => lookupInfo name (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2)))) =
      (fun name => (lookupInfo name entries).map (fun value => (value.1, f value.2))) := by
  funext name
  exact lookupInfo_map3 f name entries

/-- Exact-shaped port of Cake's `ALOOKUP_MAP4`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2851`). As for
    `ALOOKUP_MAP3`, the key type is polymorphic and `[LawfulBEq κ]` makes the
    `lookupInfo` equality reflect HOL's `=`. The mapped value `(y, f z, t)`
    matches `OPTION_MAP (I ## (f ## I))` exactly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP4"]
theorem ALOOKUP_MAP4 [BEq κ] [LawfulBEq κ] (f : γ → δ)
    (entries : List (κ × (β × γ × ε))) :
    (fun name => lookupInfo name
        (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2.1, entry.2.2.2)))) =
      (fun name => (lookupInfo name entries).map (fun value => (value.1, f value.2.1, value.2.2))) := by
  funext name
  exact lookupInfo_map4 f name entries

end Flapjack
