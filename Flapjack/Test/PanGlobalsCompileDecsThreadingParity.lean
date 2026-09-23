import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileDecsThreadingParity

open Flapjack

/-- The pass context used by the direct-HOL fixture
    (`scripts/hol-probes/pan_globals_compile_decs_probeScript.sml`). -/
def compileContext : GlobalPassContext Nat :=
  { globals := []
    globalsSize := 0
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-- A function whose body reads the global `g`, which is declared *after* it in
    `functionBeforeDecl`. -/
def globalFunction : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .assign .local "x" (.var .global "g"), returnShape := .one }

def functionBeforeDecl : List (Decl Nat) :=
  [globalFunction, .decl .one "g" (.const 7)]

def functionAfterDecl : List (Decl Nat) :=
  [.decl .one "g" (.const 7), globalFunction]

def nonFunctionDeclarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one]

def threadedBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionBeforeDecl

def threadedAfter : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext functionAfterDecl

def productionBefore : GlobalCompileDecsResult Nat :=
  globalCompileDecs compileContext functionBeforeDecl

def threadedNonFunction : GlobalCompileDecsResult Nat :=
  globalCompileDecsThreaded compileContext nonFunctionDeclarations

/-- Classifies a compiled function body: `0` is an unresolved global read
    (`Const`), `1` a resolved one (`Load`), `2` anything else. -/
def bodyKind : Prog Nat → Nat
  | .assign _ _ (.const _) => 0
  | .assign _ _ (.load _ _) => 1
  | _ => 2

def firstFunctionBodyKind (result : GlobalCompileDecsResult Nat) : Nat :=
  match result.functions with
  | [.function function] => bodyKind function.body
  | _ => 3

/-- The HOL `function_before_decl` row: the later `g` declaration is not yet in
    scope, so the threaded pass leaves the body's global read unresolved. -/
theorem threadedBeforeBodyUnresolved : firstFunctionBodyKind threadedBefore = 0 := by
  simp [firstFunctionBodyKind, threadedBefore, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionBeforeDecl, globalCompileProg, globalCompileExp,
    compileContext, lookupInfo]

/-- The HOL `function_after_decl` row: with `g` declared first, the threaded
    pass resolves the global read. -/
theorem threadedAfterBodyResolved : firstFunctionBodyKind threadedAfter = 1 := by
  simp [firstFunctionBodyKind, threadedAfter, globalCompileDecsThreaded, bodyKind,
    globalFunction, functionAfterDecl, globalCompileProg, globalCompileExp,
    compileContext, globalAddress, lookupInfo]

/-- The old production pass compiles every body under the final collected
    context, so it wrongly resolves the forward reference. -/
theorem productionBeforeBodyResolved : firstFunctionBodyKind productionBefore = 1 := by
  simp [firstFunctionBodyKind, productionBefore, bodyKind, globalFunction,
    functionBeforeDecl, globalCompileProg, globalCompileExp, compileContext,
    globalCompileDecs, globalCollect, globalCompileInitializers,
    globalCompileDecls, globalDeclsFilter, globalDeclIsFunction, globalAddress,
    lookupInfo]

theorem threadedEveryIsFunction :
    threadedBefore.functions.all globalDeclIsFunction = true :=
  compile_decs_EVERY_is_function_threaded compileContext functionBeforeDecl
    threadedBefore.initializers threadedBefore.functions
    threadedBefore.exceptions threadedBefore.context rfl

theorem threadedDeclsThm : threadedNonFunction.functions = [] :=
  compile_decs_decls_thm_threaded compileContext nonFunctionDeclarations
    threadedNonFunction.initializers threadedNonFunction.functions
    threadedNonFunction.exceptions threadedNonFunction.context rfl
    (by simp [nonFunctionDeclarations, globalDeclIsFunction])

theorem threadedAppend :
    globalCompileDecsThreaded compileContext (functionBeforeDecl ++ [.exnDecl "E" .one]) =
      let first := globalCompileDecsThreaded compileContext functionBeforeDecl
      let second := globalCompileDecsThreaded first.context [.exnDecl "E" .one]
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } :=
  compile_decls_append_threaded compileContext functionBeforeDecl [.exnDecl "E" .one]

/-! Canonical HOL-shaped context fixtures.  These use `CakeContext 8` (HOL's
    `globals`/`globals_size`/`max_globals_size` fields over 8-bit words, with an
    extensional finite map for `globals`) and mirror the direct original-HOL rows
    in `scripts/hol-probes/pan_globals_compile_decs_probe.out`. -/

/-- The canonical HOL-shaped context over 8-bit words, with no globals. -/
def cakeContext : CakeContext 8 :=
  { globals := FEMPTY, globalsSize := 0, maxGlobalsSize := 16 }

/-- The canonical context with global `g` bound to address `7`. -/
def cakeContextWithGlobal : CakeContext 8 :=
  { globals := FUPDATE cakeContext.globals ("g", (Shape.one, (7 : BitVec 8)))
    globalsSize := 1
    maxGlobalsSize := 16 }

/-- The same forward-reference function, over 8-bit words. -/
def cakeFunction : Decl (BitVec 8) :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .assign .local "x" (.var .global "g"), returnShape := .one }

def cakeFunctionBeforeDecl : List (Decl (BitVec 8)) :=
  [cakeFunction, .decl .one "g" (.const (7 : BitVec 8))]

def cakeFunctionAfterDecl : List (Decl (BitVec 8)) :=
  [.decl .one "g" (.const (7 : BitVec 8)), cakeFunction]

def cakeNonFunctionDeclarations : List (Decl (BitVec 8)) :=
  [.decl .one "g" (.const (7 : BitVec 8)), .name "S" [], .exnDecl "E" .one]

def cakeResultBefore : CakeCompileDecsResult 8 :=
  compileDecsCake cakeContext cakeFunctionBeforeDecl

def cakeResultAfter : CakeCompileDecsResult 8 :=
  compileDecsCake cakeContext cakeFunctionAfterDecl

/-- Classifies a compiled 8-bit function body, as `bodyKind` does for `Nat`. -/
def cakeBodyKind : Prog (BitVec 8) → Nat
  | .assign _ _ (.const _) => 0
  | .assign _ _ (.load _ _) => 1
  | _ => 2

def firstCakeFunctionBodyKind (result : CakeCompileDecsResult 8) : Nat :=
  match result.functions with
  | [.function function] => cakeBodyKind function.body
  | _ => 3

/-- Canonical `function_before_decl` / `function_after_decl` rows: the compiled
    body reads `Const` before the `g` declaration and `Load` after it, matching
    the HOL probe. -/
def cakeThreadingValues : List Nat :=
  [firstCakeFunctionBodyKind cakeResultBefore, firstCakeFunctionBodyKind cakeResultAfter]

#eval cakeThreadingValues
#guard cakeThreadingValues = [0, 1]

/-! Direct `compile_exp` clause checks matching HOL `compile_exp_def`: a missing
    global is `Const 0w`, a present `(One, addr)` global is
    `Load One (Op Sub [TopAddr; Const addr])`, `NStruct` is `Const 0w`, and
    `TopAddr` is `Op Sub [TopAddr; Const max_globals_size]`. -/
def isConstZero : Exp (BitVec 8) → Bool
  | .const value => value == 0
  | _ => false

def isLoadOneFrom (address : BitVec 8) : Exp (BitVec 8) → Bool
  | .load .one (.op .sub [.topAddr, .const found]) => found == address
  | _ => false

def isTopAddrSub (bound : BitVec 8) : Exp (BitVec 8) → Bool
  | .op .sub [.topAddr, .const found] => found == bound
  | _ => false

def compileExpChecks : List Bool :=
  [ isConstZero (compileExpCake cakeContext (.var .global "missing"))
  , isLoadOneFrom 7 (compileExpCake cakeContextWithGlobal (.var .global "g"))
  , isConstZero (compileExpCake cakeContext (.nStruct "S" []))
  , isTopAddrSub 16 (compileExpCake cakeContext .topAddr) ]

#eval compileExpChecks
#guard compileExpChecks.all id

/-! Direct `compile` program-clause checks matching HOL `compile_def`: assigning
    to a present `(One, addr)` global stores under `Op Sub [TopAddr; Const addr]`,
    while a missing global becomes `Skip`. -/
def isGlobalAssignStore (address value : BitVec 8) : Prog (BitVec 8) → Bool
  | .store (.op .sub [.topAddr, .const found]) (.const stored) =>
      found == address && stored == value
  | _ => false

def isSkip : Prog (BitVec 8) → Bool
  | .skip => true
  | _ => false

def compileProgChecks : List Bool :=
  [ isGlobalAssignStore 7 5
      (compileProgCake cakeContextWithGlobal (.assign .global "g" (.const 5)))
  , isSkip (compileProgCake cakeContext (.assign .global "g" (.const 5))) ]

#eval compileProgChecks
#guard compileProgChecks.all id

/-- Direct rows for the exact `fresh_name` port, mirroring the
    `fresh_name_clear` / `fresh_name_missing_empty` / `fresh_name_hit` /
    `fresh_name_seed` rows of `scripts/hol-probes/pan_globals_compile_decs_probe.out`
    (HOL: `«x»`, `«»`, `«'''»`, `«vn''»`). -/
def freshNameChecks : List Bool :=
  [ freshNameHOL "x" ["y"] == "x"
  , freshNameHOL "" [] == ""
  , freshNameHOL "" ["", "'", "''"] == "'''"
  , freshNameHOL "vn'" ["vn'"] == "vn''" ]

#eval freshNameChecks
#guard freshNameChecks.all id

theorem cakeEveryIsFunction :
    cakeResultBefore.functions.all globalDeclIsFunction = true :=
  compile_decs_EVERY_is_function_cake cakeContext cakeFunctionBeforeDecl
    cakeResultBefore.initializers cakeResultBefore.functions
    cakeResultBefore.exceptions cakeResultBefore.context rfl

theorem cakeDeclsThm :
    (compileDecsCake cakeContext cakeNonFunctionDeclarations).functions = [] :=
  compile_decs_decls_thm_cake cakeContext cakeNonFunctionDeclarations
    (compileDecsCake cakeContext cakeNonFunctionDeclarations).initializers
    (compileDecsCake cakeContext cakeNonFunctionDeclarations).functions
    (compileDecsCake cakeContext cakeNonFunctionDeclarations).exceptions
    (compileDecsCake cakeContext cakeNonFunctionDeclarations).context rfl
    (by simp [cakeNonFunctionDeclarations, globalDeclIsFunction])

theorem cakeAppend :
    compileDecsCake cakeContext (cakeFunctionBeforeDecl ++ [.exnDecl "E" .one]) =
      let first := compileDecsCake cakeContext cakeFunctionBeforeDecl
      let second := compileDecsCake first.context [.exnDecl "E" .one]
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } :=
  compile_decls_append_cake cakeContext cakeFunctionBeforeDecl [.exnDecl "E" .one]

def cakeThreadingGuard : Bool :=
  cakeThreadingValues == [0, 1] &&
  compileExpChecks.all id &&
  compileProgChecks.all id &&
  freshNameChecks.all id &&
  cakeResultBefore.functions.all globalDeclIsFunction

#eval cakeThreadingGuard
#guard cakeThreadingGuard

def threadingGuard : Bool :=
  firstFunctionBodyKind threadedBefore == 0 &&
  firstFunctionBodyKind threadedAfter == 1 &&
  firstFunctionBodyKind productionBefore == 1 &&
  threadedBefore.functions.all globalDeclIsFunction &&
  threadedNonFunction.functions.isEmpty

#eval threadingGuard
#guard threadingGuard

def runChecks : IO Bool := do
  let threadingOk ← if threadingGuard then
      IO.println "PASS pan_globals compile_decs context threading (Function before Decl)"
      pure true
    else
      IO.println "FAIL pan_globals compile_decs context threading (Function before Decl)"
      pure false
  let cakeOk ← if cakeThreadingGuard then
      IO.println "PASS pan_globals canonical CakeContext compile_decs threading"
      pure true
    else
      IO.println "FAIL pan_globals canonical CakeContext compile_decs threading"
      pure false
  pure (threadingOk && cakeOk)

end Flapjack.Test.PanGlobalsCompileDecsThreadingParity
