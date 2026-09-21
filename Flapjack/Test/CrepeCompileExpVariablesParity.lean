import Flapjack.CrepeCompileExpVariables

namespace Flapjack.Test.CrepeCompileExpVariablesParity

open Flapjack

def emptyContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

/-! A concrete witness for Cake's `genlist_vmax_distinct_lists_compiled_exps`:
    compiled constants contain no source variables, while temporary names start
    strictly above the context's `maxVar`. -/
theorem genlist_vmax_distinct_lists_compiled_exps_fixture :
    ListDisjoint ((List.range 3).map (fun i => i + 1 + emptyContext.maxVar))
      (([Exp.const 4, Exp.const 5].map (compileExp emptyContext)).flatMap
        (fun entry => entry.1.flatMap crepExpVars)) := by
  apply genlist_vmax_distinct_lists_compiled_exps emptyContext 3
    [Exp.const 4, Exp.const 5]
  intro name shape names hlookup varName hvar
  simp [emptyContext, lookupInfo] at hlookup

end Flapjack.Test.CrepeCompileExpVariablesParity
