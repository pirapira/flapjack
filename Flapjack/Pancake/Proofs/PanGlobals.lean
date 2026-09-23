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

/-! Exact-shaped port of Cake's `not_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2527`). `isName`,
    `isDecl`, and `isExnDecl` are the source-shaped counterparts of HOL
    `is_name`, `is_decl`, and `is_exn_decl`; `globalDeclIsFunction` is the
    pass-facing `is_function`. The production module keeps the three
    per-predicate helper lemmas, assembled here. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "not_is_function"]
theorem not_is_function (declaration : Decl α) :
    (isName declaration = true → globalDeclIsFunction declaration = false) ∧
    (isDecl declaration = true → globalDeclIsFunction declaration = false) ∧
    (isExnDecl declaration = true → globalDeclIsFunction declaration = false) :=
  ⟨isName_not_function declaration, isDecl_not_function declaration,
    isExnDecl_not_function declaration⟩

/-! Exact-shaped port of Cake's `decl_distinct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2535`): a value
    declaration is disjoint from the name, function, and exception
    declaration classes. `a && b = false` is the Bool spelling of HOL
    `a ∧ b ⇔ F`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "decl_distinct"]
theorem decl_distinct (declaration : Decl α) :
    (isDecl declaration && isName declaration) = false ∧
    (isDecl declaration && globalDeclIsFunction declaration) = false ∧
    (isDecl declaration && isExnDecl declaration) = false := by
  cases declaration <;> simp [isDecl, isName, isExnDecl, globalDeclIsFunction]

/-! Exact-shaped port of Cake's `functions_filter_nil`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2967`): filtering out
    function declarations leaves an empty function table. `globalDeclsFilter`
    is the source-shaped `FILTER` and `globalDeclIsFunction` the
    pass-facing `is_function`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_filter_nil"]
theorem functions_filter_nil (declarations : List (Decl α)) :
    functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) = [] :=
  functions_globalDeclsFilter_not_function declarations

/-! Exact-shaped port of Cake's `functions_FILTER_exn_decl`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2042`): keeping only
    exception declarations leaves an empty function table. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_exn_decl"]
theorem functions_FILTER_exn_decl (declarations : List (Decl α)) :
    functions (globalDeclsFilter isExnDecl declarations) = [] :=
  functions_globalDeclsFilter_exnDecl declarations

/-! Exact-shaped port of Cake's `functions_FILTER_is_name`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2049`): keeping only
    name declarations leaves an empty function table. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_is_name"]
theorem functions_FILTER_is_name (declarations : List (Decl α)) :
    functions (globalDeclsFilter isName declarations) = [] :=
  functions_globalDeclsFilter_isName declarations

/-! Exact-shaped port of Cake's `fperm_name_cancel`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1622`). `fperm_name`
    (defined `pan_globalsScript.sml:184`) is the source-shaped rename of a
    function name, spelled `globalRenameFunctionName` in the production pass. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cancel"]
theorem fperm_name_cancel [BEq String] [LawfulBEq String]
    (source target name : FunName) :
    globalRenameFunctionName source target
        (globalRenameFunctionName source target name) = name :=
  globalRenameFunctionName_cancel source target name

/-! Exact-shaped port of Cake's `fperm_name_cong`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1629`):
    `fperm_name` is injective on function names. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cong"]
theorem fperm_name_cong [BEq String] [LawfulBEq String]
    (source target left right : FunName) :
    globalRenameFunctionName source target left =
        globalRenameFunctionName source target right ↔
      left = right :=
  globalRenameFunctionName_cong source target left right

/-! Exact-shaped port of Cake's `fperm_decs_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1663`): the source-shaped
    `fperm_decs` (production `globalRenameDecls`) distributes over declaration
    list concatenation. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_append"]
theorem fperm_decs_append [BEq String] (source target : FunName)
    (declarations rest : List (Decl α)) :
    globalRenameDecls source target (declarations ++ rest) =
      globalRenameDecls source target declarations ++
        globalRenameDecls source target rest :=
  globalRenameDecls_append source target declarations rest

/-! Exact-shaped port of Cake's `functions_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1701`): the function table
    of a renamed declaration list is the renamed function table, matching HOL's
    `MAP (λ(a,b,c,d). (fperm_name x y a, b, fperm x y c, d))` with
    `globalRenameFunctionName`/`globalRenameProg` for `fperm_name`/`fperm`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_fperm_decs"]
theorem functions_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    functions (globalRenameDecls source target declarations) =
      (functions declarations).map (fun entry =>
        (globalRenameFunctionName source target entry.1, entry.2.1,
          globalRenameProg source target entry.2.2.1, entry.2.2.2)) :=
  functions_globalRenameDecls source target declarations

/-! Exact-shaped port of Cake's `ALL_DISTINCT_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1711`): renaming
    declarations preserves distinctness of the function-name table. HOL
    `ALL_DISTINCT` is Lean `List.Nodup` and `MAP FST` is `List.map entry.1`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALL_DISTINCT_fperm_decs"]
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

/-! Exact-shaped port of Cake's `dec_shapes_append`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2328`): the collected
    declaration shapes distribute over list append. `dec_shapes` is the
    production `globalDeclShapes`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_append"]
theorem dec_shapes_append (declarations rest : List (Decl α)) :
    globalDeclShapes (declarations ++ rest) =
      globalDeclShapes declarations ++ globalDeclShapes rest :=
  globalDeclShapes_append declarations rest

/-! Exact-shaped port of Cake's `dec_shapes_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2335`): a declaration
    list all of whose entries are functions collects no shapes. HOL `EVERY
    is_function` is Lean `List.all globalDeclIsFunction = true`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_functions"]
theorem dec_shapes_functions (declarations : List (Decl α))
    (hfunctions : declarations.all globalDeclIsFunction = true) :
    globalDeclShapes declarations = [] :=
  globalDeclShapes_of_functions declarations
    (fun declaration hmem => List.all_eq_true.mp hfunctions declaration hmem)

/-! Exact-shaped port of Cake's `dec_shapes_FILTER`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2343`): filtering out
    function declarations preserves collected shapes, while filtering to names
    or exceptions yields none. HOL `FILTER` is Lean `globalDeclsFilter`,
    `is_decl` is `globalDeclIsGlobal` and `is_exn_decl` is
    `globalDeclIsException`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_FILTER"]
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

/-! Exact-shaped port of Cake's `dec_shapes_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2354`): renaming does not
    change the collected declaration shapes. The source-shaped `fperm_decs` is
    the production `globalRenameDecls`, which only rewrites function entries. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_fperm_decs"]
theorem dec_shapes_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalDeclShapes (globalRenameDecls source target declarations) =
      globalDeclShapes declarations := by
  induction declarations with
  | nil => simp [globalRenameDecls, globalDeclShapes_nil]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalRenameDecls, globalDeclShapes_cons, ih]

/-! Exact-shaped port of Cake's `dec_shapes_resort_decls_def`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2361`): resorting
    declarations preserves the collected shapes. `resort_decls` is the
    production `globalResortDecls`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_resort_decls_def"]
theorem dec_shapes_resort_decls_def (declarations : List (Decl α)) :
    globalDeclShapes (globalResortDecls declarations) =
      globalDeclShapes declarations :=
  globalDeclShapes_globalResortDecls declarations

/-! Exact-shaped port of Cake's `resort_decls_preserve_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2055`): resorting
    declarations leaves the function table unchanged. `resort_decls` is the
    production `globalResortDecls`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_preserve_functions"]
theorem resort_decls_preserve_functions (declarations : List (Decl α)) :
    functions (globalResortDecls declarations) = functions declarations :=
  functions_globalResortDecls declarations

/-! Exact-shaped port of Cake's `fperm_decs_FILTER_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2032`): renaming commutes
    with filtering to the function declarations. HOL `fperm_decs` is the
    production `globalRenameDecls` and HOL `FILTER is_function` is Lean
    `globalDeclsFilter globalDeclIsFunction`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_FILTER_is_function"]
theorem fperm_decs_FILTER_is_function [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalRenameDecls source target
        (globalDeclsFilter globalDeclIsFunction declarations) =
      globalDeclsFilter globalDeclIsFunction
        (globalRenameDecls source target declarations) :=
  globalRenameDecls_filter_function source target declarations

/-- Exact-shaped port of Cake's `fperm_decs_decls`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2023`).  The HOL
    statement carries an unused `ys` binder introduced by `recInduct`, which is
    reproduced here for statement parity.  HOL `EVERY ($¬ ∘ is_function)` is
    Lean `declarations.all (fun declaration => !globalDeclIsFunction declaration)`
    and HOL `fperm_decs` is the reviewed production `globalRenameDecls`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_decls"]
theorem fperm_decs_decls [BEq String] (source target : FunName)
    (declarations _unused : List (Decl α))
    (hnone : declarations.all
      (fun declaration => !globalDeclIsFunction declaration) = true) :
    globalRenameDecls source target declarations = declarations :=
  globalRenameDecls_eq_self_of_no_functions source target declarations hnone

/-- Exact-shaped port of Cake's `new_main_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2073`): the synthesized
    `main` entry-point name is not one of the program's existing function names.
    HOL's `MEM (new_main_name code) (MAP FST (functions code)) ⇒ F` is stated as
    failure of membership in `(functions declarations).map (fun entry => entry.1)`;
    `globalFunctionNames_eq_functions_map` bridges the production
    `globalFunctionNames`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "new_main_name_correct"]
theorem new_main_name_correct [BEq String] [LawfulBEq String]
    (declarations : List (Decl α)) :
    globalNewMainName declarations ∈
        (functions declarations).map (fun entry => entry.1) → False := by
  rw [← globalFunctionNames_eq_functions_map]
  exact globalNewMainName_not_mem declarations

/-- Exact-shaped port of Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`): the name produced
    by the fresh-name search is not a member of the input list.  HOL
    `MEM (fresh_name name names) names ⇒ F` is `globalFreshName name names ∈
    names → False`; the production counterpart is `globalFreshName_not_mem`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct"]
theorem fresh_name_correct [BEq String] [LawfulBEq String]
    (name : String) (names : List String) :
    globalFreshName name names ∈ names → False :=
  globalFreshName_not_mem name names

/-- Exact-shaped port of Cake's `fresh_name_correct'`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1003`): if every member
    of `names'` lies in `names`, then a name fresh for `names` is also fresh
    for `names'`.  HOL `set names' ⊆ set names` is stated pointwise, as in the
    production counterpart `globalFreshName_not_mem_of_subset`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct'"]
theorem fresh_name_correct' [BEq String] [LawfulBEq String]
    (name : String) (names names' : List String)
    (hmem : globalFreshName name names ∈ names')
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    False :=
  globalFreshName_not_mem_of_subset name names names' hsubset hmem

/-- Exact-shaped port of Cake's `FILTER_decs_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2832`): renaming
    commutes with filtering to the non-function declarations.  HOL
    `FILTER ($¬ ∘ is_function)` is `globalDeclsFilter (fun declaration =>
    !globalDeclIsFunction declaration)` and HOL `fperm_decs` is the reviewed
    production `globalRenameDecls`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FILTER_decs_fperm_decs"]
theorem FILTER_decs_fperm_decs [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        (globalRenameDecls source target declarations) =
      globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations :=
  globalRenameDecls_filter_not_function source target declarations

/-- Exact-shaped port of Cake's `compile_decs_EVERY_is_function`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1977`): every entry the
    compilation pass emits into the function table is a function declaration.
    As in HOL, the source is `code`, the four outputs `decls,funs,exns,ctxt'`
    are explicitly quantified, and the premise binds them to the pass result
    (`globalCompileDecs` returns a record in place of HOL's tuple).  HOL
    `EVERY is_function funs` is `functions.all globalDeclIsFunction = true`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_EVERY_is_function"]
theorem compile_decs_EVERY_is_function [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    funs.all globalDeclIsFunction = true := by
  simpa [hcompile] using globalCompileDecs_functions_all_isFunction context code

/-- Exact-shaped port of Cake's `compile_decs_decls_thm`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1967`): a program whose
    declarations contain no functions compiles to an empty function table.
    HOL `EVERY (λd. ¬is_function d)` is `code.all (fun declaration =>
    !globalDeclIsFunction declaration) = true`; the four outputs are quantified
    and bound by the equality premise as above. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_decls_thm"]
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

/-- Exact-shaped port of Cake's `compile_decs_exns_are_exns`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2448`): the exception
    table is exactly the exception declarations of the source program.  HOL
    `FILTER is_exn_decl` is `globalDeclsFilter globalDeclIsException`; the four
    outputs are quantified and bound by the equality premise as above. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_exns_are_exns"]
theorem compile_decs_exns_are_exns [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (decls : List (Prog α)) (funs exns : List (Decl α))
    (ctxt' : GlobalPassContext α)
    (hcompile : globalCompileDecs context code =
      { initializers := decls, functions := funs,
        exceptions := exns, context := ctxt' }) :
    exns = globalDeclsFilter globalDeclIsException code := by
  simpa [hcompile] using globalCompileDecs_exceptions_eq_filter context code

/-- Exact-shaped port of Cake's `compile_decs_preserve_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2062`): compilation
    preserves the function-name table.  HOL `MAP FST (functions funs)` is
    `(functions funs).map (fun entry => entry.1)`; the four outputs are
    quantified and bound by the equality premise as above. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_preserve_functions"]
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

/-- Exact-shaped port of Cake's `EVERY_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2436`): if a predicate
    holds on every non-function declaration and on every renamed function
    declaration, it holds on every declaration produced by the renaming pass.
    HOL `EVERY (λd. ¬is_function d ⇒ P d)` is the boolean
    `declarations.all (fun d => globalDeclIsFunction d || predicate d) = true`;
    the function premise keeps HOL's `Function fi` destructuring. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "EVERY_fperm_decs"]
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

/-- Exact-shaped port of Cake's `compile_decs_FILTER_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2822`): filtering the
    source program to its value declarations leaves the initializers and the
    context unchanged and empties the function and exception tables.  HOL
    `FILTER is_decl` is `globalDeclsFilter isDecl`; the four outputs are
    quantified and bound by the equality premise as in the other
    `compile_decs` ports, and the result is stated as a whole record. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_FILTER_decs"]
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

/-- Exact-shaped port of Cake's `ALOOKUP_MAP3`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2841`): mapping a
    function over the triple value component commutes with the lookup.  HOL
    `ALOOKUP` is `lookupInfo` and `OPTION_MAP (I ## f)` is
    `Option.map (fun value => (value.1, f value.2))`; the HOL statement is an
    equality of functions, stated here with explicit `fun` binders.  The only
    difference is that HOL's `ALOOKUP` is polymorphic in the association-list
    key, while the reviewed production `lookupInfo`/`InfoMap` is specialized
    to `String`; the lookup equations and the mapped value match exactly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP3"]
theorem ALOOKUP_MAP3 [BEq String] (f : γ → δ) (entries : List (String × (β × γ))) :
    (fun name => lookupInfo name (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2)))) =
      (fun name => (lookupInfo name entries).map (fun value => (value.1, f value.2))) := by
  funext name
  exact lookupInfo_map3 f name entries

/-- Exact-shaped port of Cake's `ALOOKUP_MAP4`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2851`): mapping a
    function over the middle component of a quadruple value commutes with the
    lookup.  HOL `OPTION_MAP (I ## (f ## I))` is
    `Option.map (fun value => (value.1, f value.2.1, value.2.2))`; the HOL
    statement is an equality of functions, stated here with explicit `fun`
    binders.  As with `ALOOKUP_MAP3`, the only difference is the `String`
    specialization of the reviewed production `lookupInfo`; the lookup
    equations and the mapped value match exactly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP4"]
theorem ALOOKUP_MAP4 [BEq String] (f : γ → δ)
    (entries : List (String × (β × γ × ε))) :
    (fun name => lookupInfo name
        (entries.map (fun entry => (entry.1, entry.2.1, f entry.2.2.1, entry.2.2.2)))) =
      (fun name => (lookupInfo name entries).map (fun value => (value.1, f value.2.1, value.2.2))) := by
  funext name
  exact lookupInfo_map4 f name entries

end Flapjack
