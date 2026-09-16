import Flapjack.Correctness

/-!
# Source-to-Loop call correctness

This module keeps executable call fixtures and their semantic helper
definitions at the Pancake-to-Crepe-to-Loop boundary.  Symbolic correctness
claims are deferred while the implementation is being aligned with Pancake;
the executable tests remain the current regression evidence.
-/

namespace Flapjack

def identityCallDeclarations (value : α) : List (Decl α) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id" [.const value]
        (.return (.var .local "result")), returnShape := .one }]

def identityCallCompileContext [OfNat α 0] : CompileContext α :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 0 }

def identityCallLoopState : LoopState α :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def identityCallSourceFunctions : List (FunName × List VarName × Prog α) :=
  [("id", ["x"], .return (.var .local "x"))]

def identityCallSourceMain (value : α) : Prog α :=
  .decCall "result" .one "id" [.const value]
    (.return (.var .local "result"))

def raiseHandlerDeclarations [OfNat α 0] [OfNat α 1]
    (_exceptionCode value : α) : List (Decl α) :=
  [.exnDecl "E" .one,
   .function
    { name := "raise", inline := false, exported := false, params := [],
      body := .raise "E" (.const value), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true, params := [],
      body := .dec "exception" .one (.const 0)
        (.call
          (some (none, some ("E", "exception",
            .return (.var .local "exception"))))
          "raise" []), returnShape := .one }]

def raiseHandlerCompileContext [OfNat α 0] [OfNat α 1]
    (exceptionCode : α) : CompileContext α :=
  { vars := [], functions := [], exceptions := [("E", exceptionCode)],
    maxVar := 0, bytesInWord := 1 }

def raiseHandlerSourceFunctions (value : α) :
    List (FunName × List VarName × Prog α) :=
  [("raise", [], .raise "E" (.const value))]

def raiseHandlerSourceMain : Prog α :=
  .call
    (some (none, some ("E", "exception",
      .return (.var .local "exception"))))
    "raise" []

def raiseHandlerLoopFunctions [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (exceptionCode value : α) : List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctions .rv64i 1
    (compileToCrepe (raiseHandlerCompileContext exceptionCode)
      (raiseHandlerDeclarations exceptionCode value))

def raiseHandlerLoopResult
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exceptionCode value : α) : Option (List α) := do
  let functions := raiseHandlerLoopFunctions exceptionCode value
  let (_, main) ← lookupLoopFunction 2 functions
  let result ← evalLoopProgWithFunctions functions 100
    identityCallLoopState main
  pure (loopResultValues result)

def raiseHandlerSourceResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) : Option (List α) :=
  (evalPanProgWithHandlers (raiseHandlerSourceFunctions value) 40
    (fun _ => none) raiseHandlerSourceMain).map (fun result =>
      match result with
      | .returned _ values => values
      | _ => [])

/-! The executable handler definitions above are retained for parity probes.
    The old symbolic proof was removed while the compiler is being brought
    back to the exact Pancake implementation; it depended on the former
    reduced call pipeline and no longer states a fact established by the
    current implementation.  A correctness theorem belongs here again after
    source and target semantics have been reviewed. -/

end Flapjack
