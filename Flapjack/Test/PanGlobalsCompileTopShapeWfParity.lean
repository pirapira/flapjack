import Flapjack.Pancake.Proofs.PanGlobals

/-!
# `compile_top_shape_wf` statement fixture

This checks the HOL-shaped hypotheses and conclusion at the use site: evaluator
success plus admissible declarations imply well-formed function signatures for
every function in the total `compile_top` result.
-/

namespace Flapjack.Test.PanGlobalsCompileTopShapeWfParity

open Flapjack

example
    (bytesInWord : Nat) (fromNat : Nat → Nat)
    (state : PanSemDeclarationState Nat Unit) (declarations : List (Decl Nat))
    (start : FunName) (state' : PanSemDeclarationState Nat Unit)
    (heval : evaluateDecls state declarations = some state')
    (hadmissible : declarations.all panSemCompileTopAdmissible = true) :
    ∀ output, output ∈ globalCompileTopForStart bytesInWord fromNat declarations start →
      ∀ function, output = .function function →
        function.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) = true ∧
          isWfShape state.runtime.structs function.returnShape = true :=
  globalCompileTopForStart_shapes_wf bytesInWord fromNat state declarations
    start state' heval hadmissible

end Flapjack.Test.PanGlobalsCompileTopShapeWfParity
