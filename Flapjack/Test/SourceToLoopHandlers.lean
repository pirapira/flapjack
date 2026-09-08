import Flapjack.Test.SourceToLoop

/-!
Source-to-Loop exception-handler regression.

The caller declares its handler variable before making the call.  This mirrors
the compiler context used by the real lowering and checks exception-code
materialization, handler-slot setup, and the returned exception value.
-/

namespace Flapjack

open RiscV

def sourceToLoopHandlerDeclarations : List (Decl (Word 64)) :=
  [.exnDecl "E" .one,
   .function
     { name := "raise", inline := false, exported := false, params := [],
       body := .raise "E" (.const (BitVec.ofNat 64 7)), returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .dec "exception" .one (.const 0)
         (.call
           (some (none, some ("E", "exception",
             .return (.var .local "exception"))))
           "raise" []), returnShape := .one }]

def sourceToLoopHandlerPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    sourceToLoopHandlerDeclarations

def sourceToLoopHandlerState : LoopState (Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def sourceToLoopHandlerFunctions :
    List (FunName × List VarName × Prog (Word 64)) :=
  [("raise", [], .raise "E" (.const (BitVec.ofNat 64 7))),
   ("main", [],
     .dec "exception" .one (.const 0)
       (.call
         (some (none, some ("E", "exception",
           .return (.var .local "exception"))))
         "raise" []))]

def sourceToLoopHandlerMain : Prog (Word 64) :=
  .dec "exception" .one (.const 0)
    (.call
      (some (none, some ("E", "exception",
        .return (.var .local "exception"))))
      "raise" [])

theorem sourceToLoop_handler_simulation :
    (do
      let (_, main) ← lookupLoopFunction 2
        sourceToLoopHandlerPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions
        sourceToLoopHandlerPipeline.pipeline.loop 80
        sourceToLoopHandlerState main
      pure (loopResultValues result)) =
      (evalPanProgWithHandlers sourceToLoopHandlerFunctions 30
        (fun _ : VarName => none) sourceToLoopHandlerMain).map (fun result =>
          match result with
          | .returned _ values => values
          | _ => []) := by
  native_decide

#guard
    (do
      let (_, main) ← lookupLoopFunction 2
        sourceToLoopHandlerPipeline.pipeline.loop
      let result ← evalLoopProgWithFunctions
        sourceToLoopHandlerPipeline.pipeline.loop 80
        sourceToLoopHandlerState main
      pure (loopResultValues result)) = some [BitVec.ofNat 64 7]

end Flapjack
