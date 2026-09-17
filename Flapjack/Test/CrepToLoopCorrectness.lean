import Flapjack.CrepToLoopCorrectness

/-!
Focused Cake-backed guards for the context lookup boundary.  The old file
contained identity-map evaluation witnesses; those are not valid after the
Crep compiler began applying `find_var` to source slots.
-/

namespace Flapjack

def crepLookupContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

#guard crepFindVar crepLookupContext 1 = 5
#guard crepFindVar crepLookupContext 2 = 0

/- The source compiler must apply the same lookup at the expression boundary,
   rather than merely exposing the helper in isolation.  These guards pin the
   Cake hit and missing-variable cases without reinstating the old identity-map
   proof witnesses. -/
example :
    (loopCompileExp crepLookupContext 6 [] (.var 1)).expression = .var 5 := by
  simp [loopCompileExp, crepLookupContext, findLoopVar, lookupNatInfo]

example :
    (loopCompileExp crepLookupContext 6 [] (.var 2)).expression = .var 0 := by
  simp [loopCompileExp, crepLookupContext, findLoopVar, lookupNatInfo]

end Flapjack
