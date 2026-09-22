import Flapjack.PanGlobalsSemantics

namespace Flapjack.Test.PanGlobalsSemanticsParity

open Flapjack

/-! Smoke checks for Flapjack's own start-function shape invariant. These
    fixtures are analogous to Cake's `compile_top_shape_wf`
    (`pan_globalsProofScript.sml:2458`), but they do not test that theorem's
    statement shape: they use Flapjack's value evaluator and global compiler. -/

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

/-- Flapjack-specific start-function fixture for the analogous shape invariant. -/
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

/-- Empty-struct Flapjack fixture, analogous to `compile_top_shape_wf_nil`
    (`pan_globalsProofScript.sml:2495`) but with Flapjack's statement shape. -/
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
