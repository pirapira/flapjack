import Flapjack.Pancake.Proofs.PanGlobals

/-!
# `compile_top_shape_wf` statement fixture

This checks the HOL-shaped hypotheses and conclusion at the use site: evaluator
success plus admissible declarations imply well-formed function signatures for
every function in the total `compile_top` result.
-/

namespace Flapjack.Test.PanGlobalsCompileTopShapeWfParity

open Flapjack

example {width : Nat} (declarations : List (Decl (BitVec width)))
    (start : FunName) :
    globalCompileTopCake declarations start =
      globalCompileTopForStart (BitVec.ofNat width (width / 8))
        (BitVec.ofNat width) declarations start := rfl

example {width : Nat} [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)]
    (state : PanSemDeclarationState (BitVec width) Unit)
    (declarations : List (Decl (BitVec width)))
    (start : FunName) (state' : PanSemDeclarationState (BitVec width) Unit)
    (heval : evaluateDecls state declarations = some state')
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    ∀ output, output ∈ globalCompileTopCake declarations start →
      ∀ function, output = .function function →
        function.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) = true ∧
          isWfShape state.runtime.structs function.returnShape = true :=
  globalCompileTopCake_shapes_wf state declarations start state' heval hadmissible

end Flapjack.Test.PanGlobalsCompileTopShapeWfParity
