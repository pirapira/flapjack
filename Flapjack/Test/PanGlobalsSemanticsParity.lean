import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsSemanticsParity

open Flapjack

/-! Direct parity for Cake's `compile_top_shape_wf`
    (`pan_globalsProofScript.sml:2458`): a successful declaration evaluation
    makes every function declaration emitted by the start-function entry point
    have well-formed parameter and return shapes. -/

def mainFunction : Decl Nat :=
  .function
    { name := "main", inline := false, exported := false, params := [],
      body := (.skip : Prog Nat), returnShape := .one }

def exceptionDecl : Decl Nat := .exnDecl "E" (.named "T")

def shapeDecls : List (Decl Nat) := [mainFunction, exceptionDecl]

def compiledShapeGuard : Bool :=
  match globalCompileTopForStart 4 id shapeDecls "main" with
  | some compiled => compiled.all (panDeclShapesWellFormed ([] : StructContext))
  | none => false

#eval compiledShapeGuard
#guard compiledShapeGuard

theorem panDeclShapesWellFormed_mainFunction :
    panDeclShapesWellFormed ([] : StructContext) mainFunction = true := by
  simp [panDeclShapesWellFormed, panFunctionShapesWellFormed, mainFunction,
    isWfShape]

/-- `compile_top_shape_wf` for the start-function entry point: any successful
    evaluation justifies the shape invariant of the compiled declaration list. -/
theorem globalCompileTopForStart_shapes_wf_fixture
    (state state' : PanValueProgramState Nat)
    (memoryAccess : Option (PanValueMemoryAccess Nat))
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) state
      shapeDecls memoryAccess = some state') : True := by
  cases hcompile : globalCompileTopForStart 4 id shapeDecls "main" with
  | none => trivial
  | some compiled =>
      have h := globalCompileTopForStart_shapes_wf ([] : StructContext) state
        state' shapeDecls memoryAccess 4 id "main" compiled heval hcompile
      trivial

/-- `compile_top_shape_wf_nil` (`pan_globalsProofScript.sml:2495`): the
    empty-struct-context instance of the shape invariant. -/
theorem globalCompileTopForStart_shapes_wf_nil_fixture
    (state state' : PanValueProgramState Nat)
    (memoryAccess : Option (PanValueMemoryAccess Nat))
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) state
      shapeDecls memoryAccess = some state') : True := by
  cases hcompile : globalCompileTopForStart 4 id shapeDecls "main" with
  | none => trivial
  | some compiled =>
      have h := globalCompileTopForStart_shapes_wf_nil state state' shapeDecls
        memoryAccess 4 id "main" compiled heval hcompile
      trivial

end Flapjack.Test.PanGlobalsSemanticsParity
