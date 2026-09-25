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

/-- The production pass now uses the threaded definition, so it also leaves the
    forward reference unresolved. -/
theorem productionBeforeBodyUnresolved : firstFunctionBodyKind productionBefore = 0 := by
  simp [firstFunctionBodyKind, productionBefore, bodyKind, globalFunction,
    functionBeforeDecl, globalCompileDecs, globalCompileDecsThreaded,
    globalCompileProg, globalCompileExp, compileContext, globalAddress,
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

/-! Direct full-program `compile_def` fixture for a handled Global destination.
    The canonical context binds both `g` (argument read) and `r` (destination)
    to `(One, 7)`.  `compileProgCake` must build the whole nested
    `Dec`/`Dec`/`Seq`/`Call`/`If`/`Store` program shown by the original-HOL row
    `compile_def_handled_global` in `scripts/hol-probes/pan_globals_compile_decs_probe.out`,
    including the fresh names `vn' = ""` and `flag = "vn''"`. -/

def cakeContextWithHandled : CakeContext 8 :=
  { globals :=
      FUPDATE (FUPDATE cakeContext.globals ("g", (Shape.one, (7 : BitVec 8))))
        ("r", (Shape.one, (7 : BitVec 8)))
    globalsSize := 1
    maxGlobalsSize := 16 }

/-- Handler body mentioning the local `vn'`, so the fresh-name machinery is
    exercised (`names = ["ev", "x", "vn'"]`). -/
def handledHandlerSource : Prog (BitVec 8) :=
  .seq (.assign .local "x" (.const (1 : BitVec 8)))
    (.assign .local "vn'" (.const (2 : BitVec 8)))

/-- `Call` to global destination `r` with an exception handler, reading global
    `g` in its argument list. -/
def handledCallSource : Prog (BitVec 8) :=
  .call (some (some (.global, "r"), some ("e", "ev", handledHandlerSource)))
    "f" [.var .global "g"]

/-- The complete program the HOL `compile_def_handled_global` row produces. -/
def expectedHandledProgram : Prog (BitVec 8) :=
  .dec "" .one (.const (0 : BitVec 8))
    (.dec "vn''" .one (.const (0 : BitVec 8))
      (.seq
        (.call
          (some (some (.local, ""),
            some ("e", "ev",
              .seq (.seq (.assign .local "x" (.const (1 : BitVec 8)))
                    (.assign .local "vn'" (.const (2 : BitVec 8))))
                (.assign .local "vn''" (.const (1 : BitVec 8))))))
          "f"
          [.load .one (.op .sub [.topAddr, .const (7 : BitVec 8)])])
        (.ite (.var .local "vn''") .skip
          (.store (.op .sub [.topAddr, .const (7 : BitVec 8)])
            (.var .local "")))))

/-- Shape equality via `repr` (the test locals have no `BEq Shape`). -/
def shapeEq (a b : Shape) : Bool := toString (repr a) == toString (repr b)

/- Structural comparison covering every `Exp` and `Prog` constructor used by
   the fixture; any unhandled constructor pair returns `false`, so a `true`
   result certifies complete structural agreement. -/
mutual
  def expEq : Exp (BitVec 8) → Exp (BitVec 8) → Bool
    | .const a, .const b => a == b
    | .var k a, .var k' b => k == k' && a == b
    | .rStruct a, .rStruct b => listExpEq a b
    | .rField i a, .rField i' b => i == i' && expEq a b
    | .nStruct _ _, .nStruct _ _ => false
    | .nField f a, .nField f' b => f == f' && expEq a b
    | .load s a, .load s' b => shapeEq s s' && expEq a b
    | .loadByte a, .loadByte b => expEq a b
    | .load32 a, .load32 b => expEq a b
    | .op o a, .op o' b => o == o' && listExpEq a b
    | .panOp o a, .panOp o' b => o == o' && listExpEq a b
    | .cmp c a a', .cmp c' b b' => c == c' && expEq a b && expEq a' b'
    | .shift s a a', .shift s' b b' => s == s' && expEq a b && expEq a' b'
    | .baseAddr, .baseAddr => true
    | .topAddr, .topAddr => true
    | .bytesInWord, .bytesInWord => true
    | _, _ => false
    termination_by a b => sizeOf a + sizeOf b
  def listExpEq : List (Exp (BitVec 8)) → List (Exp (BitVec 8)) → Bool
    | [], [] => true
    | a :: as, b :: bs => expEq a b && listExpEq as bs
    | _, _ => false
    termination_by a b => sizeOf a + sizeOf b
end

mutual
  def progEq : Prog (BitVec 8) → Prog (BitVec 8) → Bool
    | .skip, .skip => true
    | .dec n s e p, .dec n' s' e' p' =>
        n == n' && shapeEq s s' && expEq e e' && progEq p p'
    | .assign k n e, .assign k' n' e' => k == k' && n == n' && expEq e e'
    | .primitive n o a, .primitive n' o' a' => n == n' && o == o' && listExpEq a a'
    | .store a b, .store a' b' => expEq a a' && expEq b b'
    | .store32 a b, .store32 a' b' => expEq a a' && expEq b b'
    | .storeByte a b, .storeByte a' b' => expEq a a' && expEq b b'
    | .seq a b, .seq a' b' => progEq a a' && progEq b b'
    | .ite c t f, .ite c' t' f' => expEq c c' && progEq t t' && progEq f f'
    | .while c b, .while c' b' => expEq c c' && progEq b b'
    | .break, .break => true
    | .continue, .continue => true
    | .call i n a, .call i' n' a' => callInfoEq i i' && n == n' && listExpEq a a'
    | _, _ => false
    termination_by a b => sizeOf a + sizeOf b
  def callInfoEq :
      Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog (BitVec 8)))
      → Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog (BitVec 8)))
      → Bool
    | none, none => true
    | some (r, h), some (r', h') => retKindEq r r' && handlerEq h h'
    | _, _ => false
    termination_by a b => sizeOf a + sizeOf b
  def retKindEq : Option (VarKind × VarName) → Option (VarKind × VarName) → Bool
    | none, none => true
    | some (k, n), some (k', n') => k == k' && n == n'
    | _, _ => false
  def handlerEq :
      Option (ExceptionId × VarName × Prog (BitVec 8))
      → Option (ExceptionId × VarName × Prog (BitVec 8)) → Bool
    | none, none => true
    | some (e, v, p), some (e', v', p') => e == e' && v == v' && progEq p p'
    | _, _ => false
    termination_by a b => sizeOf a + sizeOf b
end

def handledProgramChecks : Bool :=
  progEq (compileProgCake cakeContextWithHandled handledCallSource)
    expectedHandledProgram

#eval handledProgramChecks
#guard handledProgramChecks

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

def adapterPassContext : GlobalPassContext (BitVec 8) :=
  { globals := [("g", (Shape.one, (7 : BitVec 8)))]
    globalsSize := 8
    maxGlobalsSize := 16
    bytesInWord := cakeBytesInWord 8
    fromNat := BitVec.ofNat 8 }

theorem adapterCanonical : adapterPassContext.IsCakeCanonical :=
  ⟨rfl, fun _ => rfl⟩

theorem adapterAddress :
    cakeAddress (cakeContextOfPass adapterPassContext) Shape.one =
      globalAddress adapterPassContext Shape.one :=
  cakeAddress_ofPass adapterPassContext adapterCanonical Shape.one

theorem adapterUpdate :
    cakeContextOfPass { adapterPassContext with
        globals := ("h", (Shape.one, (8 : BitVec 8))) :: adapterPassContext.globals
        globalsSize := 8 }
      = { cakeContextOfPass adapterPassContext with
          globals := FUPDATE (cakeContextOfPass adapterPassContext).globals
            ("h", (Shape.one, (8 : BitVec 8)))
          globalsSize := 8 } :=
  cakeContextOfPass_update adapterPassContext "h" Shape.one 8

theorem adapterExpAgreement :
    compileExpCake (cakeContextOfPass adapterPassContext) (.var .global "g") =
      globalCompileExp adapterPassContext (.var .global "g") :=
  compileExpCake_cakeContextOfPass adapterPassContext adapterCanonical (.var .global "g")

theorem adapterTopAddrAgreement :
    compileExpCake (cakeContextOfPass adapterPassContext) .topAddr =
      globalCompileExp adapterPassContext .topAddr :=
  compileExpCake_cakeContextOfPass adapterPassContext adapterCanonical .topAddr

theorem adapterProgAgreement :
    compileProgCake (cakeContextOfPass adapterPassContext) handledCallSource =
      globalCompileProg adapterPassContext handledCallSource :=
  globalCompileProg_cakeContextOfPass adapterPassContext adapterCanonical handledCallSource

theorem adapterShapeValAgreement :
    globalShapeVal adapterPassContext Shape.one =
      cakeShapeVal (cakeContextOfPass adapterPassContext) Shape.one :=
  globalShapeVal_cakeShapeVal adapterPassContext adapterCanonical Shape.one

def adapterProgGuard : Bool :=
  progEq (compileProgCake (cakeContextOfPass adapterPassContext) handledCallSource)
    (globalCompileProg adapterPassContext handledCallSource)

#eval adapterProgGuard
#guard adapterProgGuard

def adapterDeclarations : List (Decl (BitVec 8)) := [.decl Shape.one "g" (.const 7)]

theorem adapterRecordAgreement :
    compileDecsCake (cakeContextOfPass adapterPassContext) adapterDeclarations =
      { initializers := (globalCompileDecsThreaded adapterPassContext adapterDeclarations).initializers
        functions := (globalCompileDecsThreaded adapterPassContext adapterDeclarations).functions
        exceptions := (globalCompileDecsThreaded adapterPassContext adapterDeclarations).exceptions
        context :=
          cakeContextOfPass (globalCompileDecsThreaded adapterPassContext adapterDeclarations).context } :=
  compileDecsCake_cakeContextOfPass adapterPassContext adapterCanonical adapterDeclarations

def adapterRecordGuard : Bool :=
  (compileDecsCake (cakeContextOfPass adapterPassContext) adapterDeclarations).initializers.length ==
    (globalCompileDecsThreaded adapterPassContext adapterDeclarations).initializers.length &&
  (compileDecsCake (cakeContextOfPass adapterPassContext) adapterDeclarations).functions.length ==
    (globalCompileDecsThreaded adapterPassContext adapterDeclarations).functions.length

#eval adapterRecordGuard
#guard adapterRecordGuard

def adapterExpGuard : Bool :=
  expEq (compileExpCake (cakeContextOfPass adapterPassContext) (.var .global "g"))
    (globalCompileExp adapterPassContext (.var .global "g")) &&
  expEq (compileExpCake (cakeContextOfPass adapterPassContext) .topAddr)
    (globalCompileExp adapterPassContext .topAddr)

#eval adapterExpGuard
#guard adapterExpGuard

def adapterLookupOk : Bool :=
  match (cakeContextOfPass adapterPassContext).globals "g" with
  | some (Shape.one, address) => address == (7 : BitVec 8)
  | _ => false

def adapterGuard : Bool :=
  (cakeAddress (cakeContextOfPass adapterPassContext) Shape.one ==
      globalAddress adapterPassContext Shape.one) &&
    adapterLookupOk

#eval adapterGuard
#guard adapterGuard

/-- A start function so the total `compile_top` path is exercised end to end. -/
def cakeMainFunction : Decl (BitVec 8) :=
  .function
    { name := "main", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def cakeStartDeclarations : List (Decl (BitVec 8)) :=
  [cakeMainFunction, .decl Shape.one "g" (.const 7)]

/-- The executed fixed-word path is the canonical definition. -/
theorem executedTopCanonicalAgreement :
    globalCompileTopCake cakeStartDeclarations "main" =
      (globalCompileTopForStartSomeCake cakeStartDeclarations "main").getD [] := rfl

/-- The executed fixed-word path computes exactly the polymorphic production
    output; this is the adapter that lets `globalCompileTopCake` route through
    the untagged, HOL-clause-shaped `compileDecsCake` without changing
    observable behavior on this production-carrier example. -/
theorem executedTopAgreement :
    globalCompileTopCake cakeStartDeclarations "main" =
      globalCompileTopForStart (BitVec.ofNat 8 (8 / 8)) (BitVec.ofNat 8)
        cakeStartDeclarations "main" := by
  rw [globalCompileTopCake_eq]
  simp only [cakeBytesInWord]

def executedTopGuard : Bool :=
  !(globalCompileTopCake cakeStartDeclarations "main").isEmpty &&
  (globalCompileTopCake cakeStartDeclarations "main").length ==
    (globalCompileTopForStart (BitVec.ofNat 8 (8 / 8)) (BitVec.ofNat 8)
      cakeStartDeclarations "main").length

#eval executedTopGuard
#guard executedTopGuard

def cakeThreadingGuard : Bool :=
  cakeThreadingValues == [0, 1] &&
  compileExpChecks.all id &&
  compileProgChecks.all id &&
  freshNameChecks.all id &&
  handledProgramChecks &&
  adapterGuard &&
  adapterExpGuard &&
  adapterProgGuard &&
  adapterRecordGuard &&
  executedTopGuard &&
  cakeResultBefore.functions.all globalDeclIsFunction

#eval cakeThreadingGuard
#guard cakeThreadingGuard

def threadingGuard : Bool :=
  firstFunctionBodyKind threadedBefore == 0 &&
  firstFunctionBodyKind threadedAfter == 1 &&
  firstFunctionBodyKind productionBefore == 0 &&
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
  let handledOk ← if handledProgramChecks then
      IO.println "PASS pan_globals compile_def handled-Global full-program oracle"
      pure true
    else
      IO.println "FAIL pan_globals compile_def handled-Global full-program oracle"
      pure false
  pure (threadingOk && cakeOk && handledOk)

end Flapjack.Test.PanGlobalsCompileDecsThreadingParity
