import Flapjack.CompileParamVarsBounds

/-!
Equations for the formal-parameter metadata produced by `compileParamVars`.

The compiler keeps both a name/shape/slot table and the flattened parameter
vector.  These projections are definitionally related, but naming the
equations avoids unfolding the allocator in callee-call correctness proofs.
-/

namespace Flapjack

theorem compileParamVars_preserves_parameter_shapes
    (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).1.map
        (fun entry => (entry.1, entry.2.1)) = params := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars, List.map_cons]
          rw [ih]

theorem compileParamVars_flattened_slots
    (params : List (VarName × Shape)) (offset : Nat) :
    (compileParamVars params offset).2.1 =
      (compileParamVars params offset).1.flatMap (fun entry => entry.2.2) := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons param params ih =>
      cases param with
      | mk name shape =>
          simp only [compileParamVars]
          rw [ih]
          rfl

end Flapjack
