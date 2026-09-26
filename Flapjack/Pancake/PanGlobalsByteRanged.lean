import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

/-!
Byte-range preservation facts for the executed PanGlobals pass.

The exact DeclHOL compiler boundary can only be used after the production
String declarations have been shown to round-trip through DeclHOL. The parser
provides that invariant, but the final global pass also rewrites programs and
can synthesize names. These lemmas establish the pass-local facts needed to
prove the invariant at the actual compiler boundary.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

private theorem nameRanged_append {left right : String}
    (hleft : NameRanged left) (hright : NameRanged right) :
    NameRanged (left ++ right) := by
  intro character hcharacter
  rw [String.toList_append, List.mem_append] at hcharacter
  rcases hcharacter with h | h
  · exact hleft character h
  · exact hright character h

private theorem globalApostrophes_nameRanged (count : Nat) :
    NameRanged (globalApostrophes count) := by
  induction count with
  | zero => simp [globalApostrophes, NameRanged]
  | succ count ih =>
      apply nameRanged_append
      · decide
      · simpa [globalApostrophes] using ih

private theorem freshNameHOL_literal_byteRanged (seed : String)
    (hseed : NameRanged seed) (names : List String) :
    NameRanged (freshNameHOL seed names) :=
  holMlStringWitness_freshNameHOL seed names hseed

/-- Every shape found in a global compilation context is byte-ranged. -/
def GlobalContextShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ name shape address,
    lookupInfo name context.globals = some (shape, address) → ShapeByteRanged shape

private theorem globalContextShapesByteRanged_update [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (name : String) (shape : Shape) (address : BitVec width)
    (hcontext : GlobalContextShapesByteRanged context)
    (hshape : ShapeByteRanged shape) :
    GlobalContextShapesByteRanged
      { context with globals := (name, (shape, address)) :: context.globals } := by
  intro key foundShape foundAddress hlookup
  by_cases hname : name == key
  · simp [lookupInfo, hname] at hlookup
    cases hlookup.1
    exact hshape
  · simp [lookupInfo, hname] at hlookup
    exact hcontext key foundShape foundAddress hlookup

private theorem globalRenameFunctionName_byteRanged [DecidableEq String]
    (source target name : String)
    (hsource : NameRanged source) (htarget : NameRanged target)
    (hname : NameRanged name) :
    NameRanged (globalRenameFunctionName source target name) := by
  by_cases hsourceName : source = name
  · simpa [globalRenameFunctionName, fpermName, hsourceName] using htarget
  · by_cases htargetName : target = name
    · simpa [globalRenameFunctionName, fpermName, hsourceName, htargetName] using hsource
    · simpa [globalRenameFunctionName, fpermName, hsourceName, htargetName] using hname

/-- Byte-ranged shapes compile to byte-ranged shape-value expressions. -/
theorem globalShapeVal_byteRanged {width : Nat}
    (context : GlobalPassContext (BitVec width)) :
    ∀ shape, ShapeByteRanged shape →
      ExpByteRanged (globalShapeVal context shape) := by
  apply Flapjack.Shape.rec
    (motive_1 := fun shape => ShapeByteRanged shape →
      ExpByteRanged (globalShapeVal context shape))
    (motive_2 := fun shapes =>
      (∀ shape ∈ shapes, ShapeByteRanged shape) →
        ListExpByteRanged (shapes.map (globalShapeVal context)))
  · intro _
    simp [globalShapeVal, ExpByteRanged]
  · intro shapes ih
    intro hshape
    simp only [ShapeByteRanged] at hshape
    simpa [globalShapeVal, ExpByteRanged] using ih hshape
  · intro _ _
    simp [globalShapeVal, ExpByteRanged]
  · intro _
    simp [ListExpByteRanged]
  · intro head tail ihHead ihTail hshapes
    simp only [ListExpByteRanged, List.map_cons]
    exact ⟨ihHead (hshapes head (by simp)), ihTail (by
      intro shape hshape
      exact hshapes shape (by simp [hshape]))⟩

theorem globalCompileExp_byteRanged [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ expression : Exp (BitVec width), ExpByteRanged expression →
      ExpByteRanged (globalCompileExp context expression) := by
  apply globalCompileExp.induct context
    (motive1 := fun expressions =>
      ListExpByteRanged expressions →
        ListExpByteRanged (globalCompileExp.globalCompileExps context expressions))
    (motive2 := fun expression =>
      ExpByteRanged expression → ExpByteRanged (globalCompileExp context expression))
  case case4 =>
    intro name shape address hlookup _hname
    simpa [globalCompileExp, hlookup, ExpByteRanged, ListExpByteRanged] using
      hcontext name shape address hlookup
  all_goals
    try simp_all [globalCompileExp, globalCompileExp.globalCompileExps,
      ExpByteRanged, ListExpByteRanged]

private theorem globalCompileExpList_byteRanged [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
      ∀ expression ∈ globalCompileExpList context expressions,
        ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => intro _ expression hmem; simp [globalCompileExpList] at hmem
  | cons head rest ih =>
      intro hinput expression hmem
      simp only [globalCompileExpList, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        exact globalCompileExp_byteRanged context hcontext head (hinput head (by simp))
      · exact ih (by
          intro item hitem
          exact hinput item (by simp [hitem])) expression hmem

private theorem globalCompileExpList_listByteRanged [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context)
    (expressions : List (Exp (BitVec width)))
    (hinput : ∀ expression ∈ expressions, ExpByteRanged expression) :
    ∀ expression ∈ globalCompileExpList context expressions, ExpByteRanged expression :=
  globalCompileExpList_byteRanged context hcontext expressions hinput

/-- Flapjack-specific representation invariant (no HOL theorem): the executed
    global pass uses production `String` identifiers, while HOL uses `mlstring`.
    This helper shows the pass preserves the byte-range premise required by the
    `ProgHOL` codec; it does not state a HOL evaluator or pass-correctness result. -/
theorem globalCompileProg_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      ProgByteRanged (globalCompileProg context program) := by
  apply globalCompileProg.induct context
    (motive := fun program =>
      ProgByteRanged program → ProgByteRanged (globalCompileProg context program))
  all_goals
    intros
    simp_all [globalCompileProg, ProgByteRanged, ExpByteRanged,
      ListExpByteRanged, globalCompileExp_byteRanged context hcontext]
  case case1 name shape value body ih hinput =>
    exact hinput.1
  case case4 name value hinput =>
    exact hinput.1
  case case5 name operator arguments hinput =>
    exact ⟨hinput.1, globalCompileExpList_listByteRanged context hcontext arguments hinput.2⟩
  case case12 function arguments hinput =>
    exact ⟨hinput.1, globalCompileExpList_listByteRanged context hcontext arguments hinput.2⟩
  case case13 function arguments hinput =>
    exact ⟨hinput.1, globalCompileExpList_listByteRanged context hcontext arguments hinput.2⟩
  case case14 function arguments exception handlerVar handler ih hinput =>
    exact ⟨hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1,
      ⟨hinput.2.2.1, hinput.2.2.2.1⟩⟩
  case case15 function arguments name hinput =>
    exact ⟨hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1,
      hinput.2.2⟩
  case case16 function arguments name exception handlerVar handler ih hinput =>
    exact ⟨hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1,
      ⟨hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩⟩
  case case17 function arguments name shape address hlookup hinput =>
    exact ⟨by decide, hcontext name shape address hlookup, hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1⟩
  case case18 function arguments name hlookup hinput =>
    exact ⟨hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1⟩
  case case19 function arguments name exception handlerVar handler shape address hlookup ih hinput =>
    let names := handlerVar ::
      (freeVarIds (globalCompileProg context handler) ++
        (globalCompileExpList context arguments).flatMap expLocalVars)
    let resultName := freshNameHOL "" names
    let flagName := freshNameHOL "vn'" (resultName :: names)
    have hresult : NameRanged resultName :=
      freshNameHOL_literal_byteRanged "" (by simp [NameRanged]) names
    have hflag : NameRanged flagName :=
      freshNameHOL_literal_byteRanged "vn'" (by decide) (resultName :: names)
    have hargs := globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1
    refine ⟨hresult, hcontext name shape address hlookup,
      globalShapeVal_byteRanged context shape (hcontext name shape address hlookup),
      hflag, by simp [ShapeByteRanged], ?_⟩
    exact ⟨⟨hinput.1, hargs, hresult, hinput.2.2.2.1,
      hinput.2.2.2.2.1, hflag⟩, by trivial⟩
  case case20 function arguments name exception handlerVar handler hlookup ih hinput =>
    exact ⟨hinput.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.1,
      ⟨hinput.2.2.2.1, hinput.2.2.2.2.1⟩⟩
  case case21 name shape function arguments body ih hinput =>
    exact ⟨hinput.1, hinput.2.2.1,
      globalCompileExpList_listByteRanged context hcontext arguments hinput.2.2.2.1⟩
  case case22 function configuration configurationLength array arrayLength hinput =>
    exact hinput.1
  case case23 exception value hinput =>
    exact hinput.1
  case case25 size name address hinput =>
    exact hinput.1
  case case26 size name address globalAddress hlookup hinput =>
    have hlocal : NameRanged (name ++ globalApostrophes 1) :=
      nameRanged_append hinput.1 (globalApostrophes_nameRanged 1)
    exact ⟨hinput.1, by simp [ShapeByteRanged], hlocal,
      by simp [ShapeByteRanged], hlocal, by
        simpa [NameRanged, String.toList_append, List.mem_append] using hlocal⟩

private theorem globalCompileDecsThreaded_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ declarations : List (Decl (BitVec width)),
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      (∀ initializer ∈ (globalCompileDecsThreaded context declarations).initializers,
          ProgByteRanged initializer) ∧
        (∀ declaration ∈ (globalCompileDecsThreaded context declarations).functions,
          DeclByteRanged declaration) ∧
        (∀ declaration ∈ (globalCompileDecsThreaded context declarations).exceptions,
          DeclByteRanged declaration) ∧
        GlobalContextShapesByteRanged
          (globalCompileDecsThreaded context declarations).context := by
  intro declarations
  induction declarations generalizing context with
  | nil =>
      intro _
      simp only [globalCompileDecsThreaded]
      exact ⟨by simp, by simp, by simp, hcontext⟩
  | cons declaration declarations ih =>
      intro hinput
      cases declaration with
      | function function =>
          have hfunction := hinput (.function function) (by simp)
          have hrest := ih context hcontext (by
            intro item hitem
            exact hinput item (by simp [hitem]))
          simp only [globalCompileDecsThreaded]
          refine ⟨hrest.1, ?_, hrest.2.2.1, hrest.2.2.2⟩
          intro output houtput
          simp only [List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            simp only [DeclByteRanged, FunDeclByteRanged] at hfunction
            exact ⟨hfunction.1, hfunction.2.1,
              globalCompileProg_byteRanged context hcontext function.body hfunction.2.2.1,
              hfunction.2.2.2⟩
          · exact hrest.2.1 output houtput
      | exnDecl exception shape =>
          have hrest := ih context hcontext (by
            intro item hitem
            exact hinput item (by simp [hitem]))
          simp only [globalCompileDecsThreaded]
          refine ⟨hrest.1, hrest.2.1, ?_, hrest.2.2.2⟩
          intro output houtput
          simp only [List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.exnDecl exception shape) (by simp)
          · exact hrest.2.2.1 output houtput
      | name struct fields =>
          simpa only [globalCompileDecsThreaded] using
            ih context hcontext (by
              intro item hitem
              exact hinput item (by simp [hitem]))
      | decl shape name value =>
          have hdecl := hinput (.decl shape name value) (by simp)
          have hshape : ShapeByteRanged shape := hdecl.1
          have hvalue := globalCompileExp_byteRanged context hcontext value hdecl.2.2
          let address := globalAddress context shape
          let nextContext := { context with
            globals := (name, (shape, address)) :: context.globals
            globalsSize := address }
          have hnext := globalContextShapesByteRanged_update context name shape address
            hcontext hshape
          have hrest := ih nextContext hnext (by
            intro item hitem
            exact hinput item (by simp [hitem]))
          simp only [globalCompileDecsThreaded]
          refine ⟨?_, hrest.2.1, hrest.2.2.1, hrest.2.2.2⟩
          intro initializer hinitializer
          simp only [List.mem_cons] at hinitializer
          rcases hinitializer with heq | hinitializer
          · cases heq
            simp [ProgByteRanged, ExpByteRanged, ListExpByteRanged, hvalue]
          · exact hrest.1 initializer hinitializer

private theorem globalDeclsFilter_mem_source {α : Type} {predicate : Decl α → Bool}
    {declarations : List (Decl α)} {declaration : Decl α}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter] at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      split at hmem
      · simp only [List.mem_cons] at hmem
        rcases hmem with heq | hmem
        · subst declaration
          simp
        · exact List.mem_cons_of_mem head (ih hmem)
      · exact List.mem_cons_of_mem head (ih hmem)

private theorem globalCompileDecs_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context)
    (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    (∀ initializer ∈ (globalCompileDecs context declarations).initializers,
        ProgByteRanged initializer) ∧
      (∀ declaration ∈ (globalCompileDecs context declarations).functions,
        DeclByteRanged declaration) ∧
      (∀ declaration ∈ (globalCompileDecs context declarations).exceptions,
        DeclByteRanged declaration) := by
  have hthread := globalCompileDecsThreaded_byteRanged context hcontext declarations hinput
  refine ⟨?_, hthread.2.1, ?_⟩
  · intro initializer hmem
    change initializer ∈ globalCompileInitializers context declarations at hmem
    rw [← globalCompileDecsThreaded_initializers] at hmem
    exact hthread.1 initializer hmem
  · rw [globalCompileDecs_exceptions_eq_filter]
    intro declaration hmem
    exact hinput declaration
      (globalDeclsFilter_mem_source hmem)

private theorem globalRenameProg_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (source target : String) (hsource : NameRanged source)
    (htarget : NameRanged target) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      ProgByteRanged (globalRenameProg source target program) := by
  let inductionContext : GlobalPassContext (BitVec width) :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0,
      bytesInWord := 0, fromNat := fun _ => 0 }
  apply globalCompileProg.induct inductionContext
    (motive := fun program =>
      ProgByteRanged program → ProgByteRanged (globalRenameProg source target program))
  all_goals
    intros
    simp_all [globalRenameProg, ProgByteRanged]
  case case1 name shape value body ih hinput => exact hinput.1
  case case2 name value shape address hlookup hinput => exact hinput.1
  case case3 name value hlookup hinput => exact hinput.1
  case case4 name value hinput => exact hinput.1
  case case5 name operator arguments hinput => exact hinput.1
  case case12 function arguments hinput =>
    exact globalRenameFunctionName_byteRanged source target function
      hsource htarget hinput.1
  case case13 function arguments hinput =>
    exact globalRenameFunctionName_byteRanged source target function
      hsource htarget hinput.1
  case case14 function arguments exception handlerVar handler ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1⟩
  case case15 function arguments name hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2⟩
  case case16 function arguments name exception handlerVar handler ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case17 function arguments name shape address hlookup hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case18 function arguments name hlookup hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case19 function arguments name exception handlerVar handler shape address hlookup ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case20 function arguments name exception handlerVar handler hlookup ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case21 name shape function arguments body ih hinput =>
    exact ⟨hinput.1,
      globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.2.2.1⟩
  case case22 function configuration configurationLength array arrayLength hinput => exact hinput.1
  case case23 exception value hinput => exact hinput.1
  case case25 size name address hinput => exact hinput.1
  case case26 size name address globalAddress hlookup hinput => exact hinput.1
  case case27 size name address hlookup hinput => exact hinput.1

private theorem globalRenameDecls_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (source target : String) (hsource : NameRanged source)
    (htarget : NameRanged target) :
    ∀ declarations : List (Decl (BitVec width)),
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      ∀ declaration ∈ globalRenameDecls source target declarations,
        DeclByteRanged declaration := by
  intro declarations
  induction declarations with
  | nil => simp [globalRenameDecls]
  | cons declaration declarations ih =>
      intro hinput output houtput
      cases declaration with
      | function function =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            have hfunction := hinput (.function function) (by simp)
            simp only [DeclByteRanged, FunDeclByteRanged] at hfunction
            exact ⟨globalRenameFunctionName_byteRanged source target function.name
                hsource htarget hfunction.1,
              hfunction.2.1,
              globalRenameProg_byteRanged source target hsource htarget
                function.body hfunction.2.2.1,
              hfunction.2.2.2⟩
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | decl shape name value =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.decl shape name value) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | exnDecl exception shape =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.exnDecl exception shape) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | name struct fields =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.name struct fields) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput

private theorem globalResortDecls_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ globalResortDecls declarations, DeclByteRanged declaration := by
  intro declaration houtput
  unfold globalResortDecls at houtput
  rcases List.mem_append.mp houtput with hleft | hfunction
  · rcases List.mem_append.mp hleft with hleft | hglobal
    · rcases List.mem_append.mp hleft with hname | hexn
      · exact hinput declaration (globalDeclsFilter_mem_source hname)
      · exact hinput declaration (globalDeclsFilter_mem_source hexn)
    · exact hinput declaration (globalDeclsFilter_mem_source hglobal)
  · exact hinput declaration (globalDeclsFilter_mem_source hfunction)

private theorem globalFindFunction_byteRanged {width : Nat} [BEq String]
    (name : String) (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration)
    (function : FunDecl (BitVec width))
    (hfind : globalFindFunction name declarations = some function) :
    FunDeclByteRanged function := by
  induction declarations with
  | nil => simp [globalFindFunction] at hfind
  | cons declaration declarations ih =>
      cases declaration with
      | function fd =>
          by_cases hname : fd.name == name
          · simp [globalFindFunction, hname] at hfind
            have heq : fd = function := hfind
            subst function
            exact hinput (.function fd) (by simp)
          · simp [globalFindFunction, hname] at hfind
            exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | decl shape name' value =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | exnDecl exception shape =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | name struct fields =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind

private theorem nestedSeq_byteRanged {width : Nat}
    (programs : List (Prog (BitVec width)))
    (hprograms : ∀ program ∈ programs, ProgByteRanged program) :
    ProgByteRanged (nestedSeq programs) := by
  induction programs with
  | nil => simp [nestedSeq, ProgByteRanged]
  | cons head tail ih =>
      simp only [nestedSeq, ProgByteRanged]
      exact ⟨hprograms head (by simp), ih (by
        intro program hmem
        exact hprograms program (by simp [hmem]))⟩

private theorem globalCompileTopParameters_byteRanged {width : Nat}
    (parameters : List (String × Shape))
    (hparameters : ListParamByteRanged parameters) :
    ∀ expression : Exp (BitVec width),
      expression ∈ parameters.map
        (fun parameter : String × Shape => Exp.var .local parameter.1) →
      ExpByteRanged expression := by
  intro expression hmem
  rcases List.mem_map.mp hmem with ⟨parameter, hparameter, heq⟩
  cases heq
  exact (hparameters parameter hparameter).1

/-- Flapjack-specific representation invariant (no HOL theorem): the executed
    `globalCompileTopCake` consumes production `Decl`/`String` carriers, while
    HOL `compile_top` uses `DeclHOL`/`mlstring`. This proves that the executed
    output remains encodable through the exact `DeclHOL` boundary; it does not
    claim a HOL pass-correctness statement. -/
theorem globalCompileTopCake_byteRanged [LawfulBEq String]
    {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName)
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ globalCompileTopCake declarations start, DeclByteRanged declaration := by
  rw [globalCompileTopCake_eq]
  unfold globalCompileTopForStart
  cases hfind : globalFindFunction start declarations with
  | none => simp [globalCompileTopForStartSome, hfind]
  | some entry =>
      have hentry := globalFindFunction_byteRanged start declarations hinput entry hfind
      have hstartEq := (globalFindFunction_name_mem start declarations entry hfind).1
      have hstart : NameRanged start := by
        rw [← hstartEq]
        exact hentry.1
      have hrenamedStart : NameRanged (globalNewMainName declarations) :=
        holMlStringWitness_globalNewMainName declarations
      let resorted := globalResortDecls declarations
      have hresorted : ∀ declaration ∈ resorted, DeclByteRanged declaration :=
        globalResortDecls_byteRanged declarations hinput
      let renamedStart := globalNewMainName declarations
      let renamed := globalRenameDecls start renamedStart resorted
      have hrenamed : ∀ declaration ∈ renamed, DeclByteRanged declaration :=
        globalRenameDecls_byteRanged start renamedStart hstart hrenamedStart resorted hresorted
      let maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
        ((globalDeclShapes renamed).map Shape.shapeSize |>.foldl (· + ·) 0)
      let initial : GlobalPassContext (BitVec width) :=
        { globals := []
          globalsSize := BitVec.ofNat width 0
          maxGlobalsSize := maxGlobalsSize
          bytesInWord := cakeBytesInWord width
          fromNat := BitVec.ofNat width }
      have hinitialContext : GlobalContextShapesByteRanged initial := by
        intro name shape address hlookup
        simp [initial, lookupInfo] at hlookup
      have hcompiled := globalCompileDecs_byteRanged initial hinitialContext renamed hrenamed
      let compiled := globalCompileDecs initial renamed
      let parameters : List (Exp (BitVec width)) :=
        entry.params.map (fun (name, _) => Exp.var .local name)
      let newMain : Decl (BitVec width) :=
        .function
          { name := start
            inline := false
            exported := false
            params := entry.params
            body := .seq (nestedSeq compiled.initializers)
              (.call none renamedStart parameters)
            returnShape := entry.returnShape }
      have hnewMain : DeclByteRanged newMain := by
        simp only [newMain, DeclByteRanged, FunDeclByteRanged]
        refine ⟨hstart, hentry.2.1, ?_, hentry.2.2.2⟩
        simp only [ProgByteRanged]
        refine ⟨nestedSeq_byteRanged compiled.initializers hcompiled.1, ?_⟩
        exact ⟨hrenamedStart,
          by simpa [parameters] using
            globalCompileTopParameters_byteRanged (width := width) entry.params hentry.2.1⟩
      simp only [globalCompileTopForStartSome, hfind]
      change ∀ declaration ∈ compiled.exceptions ++ [newMain] ++ compiled.functions,
        DeclByteRanged declaration
      intro declaration hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hleft | hfunction
      · rcases hleft with hexn | hnew
        · exact hcompiled.2.2 declaration hexn
        · cases hnew
          exact hnewMain
      · exact hcompiled.2.1 declaration hfunction

end Flapjack
